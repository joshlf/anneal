#!/usr/bin/env python3
"""Unit tests for `anneal_lsp_daemon.py` socket inode hygiene and displaced-daemon reaping."""

from __future__ import annotations

import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import sys
import tempfile
import time
import unittest

SERVER_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SERVER_DIR)
import anneal_lsp_daemon as daemon  # noqa: E402


class TestAnnealLspDaemonLifecycle(unittest.TestCase):
    def test_reap_displaced_daemons_targets_matching_socket_and_spares_keep_pid(self) -> None:
        with tempfile.TemporaryDirectory(prefix="test-lsp-reap-") as td:
            sock_a = os.path.join(td, "a.sock")
            sock_b = os.path.join(td, "b.sock")
            dummy_script = os.path.join(td, "anneal_lsp_daemon.py")
            Path(dummy_script).write_text(
                "import signal, sys, time\n"
                "signal.signal(signal.SIGTERM, lambda *_: sys.exit(0))\n"
                "time.sleep(60)\n",
                encoding="utf-8",
            )

            p_victim = subprocess.Popen([sys.executable, dummy_script, "--serve", "--socket", sock_a])
            p_keep = subprocess.Popen([sys.executable, dummy_script, "--serve", "--socket", sock_a])
            p_other = subprocess.Popen([sys.executable, dummy_script, "--serve", "--socket", sock_b])
            try:
                time.sleep(0.15)
                reaped = daemon._reap_displaced_lsp_daemons(sock_a, keep_pid=p_keep.pid)
                self.assertIn(p_victim.pid, reaped)
                self.assertNotIn(p_keep.pid, reaped)
                self.assertNotIn(p_other.pid, reaped)
                self.assertIsNotNone(p_victim.wait(timeout=3.0))
                self.assertIsNone(p_keep.poll())
                self.assertIsNone(p_other.poll())
            finally:
                for p in (p_victim, p_keep, p_other):
                    if p.poll() is None:
                        p.kill()
                        p.wait(timeout=2.0)

    def test_serve_daemon_preserves_replacement_socket_with_distinct_inode(self) -> None:
        with tempfile.TemporaryDirectory(prefix="test-lsp-ino-") as td:
            sock_p = os.path.join(td, "daemon.sock")
            runner_code = (
                f"import sys; sys.path.insert(0, {SERVER_DIR!r}); "
                "import anneal_lsp_daemon as d; "
                "d._maybe_self_slice_reexec = lambda *a, **k: False; "
                f"d.serve_daemon({sock_p!r})"
            )
            p1 = subprocess.Popen(
                [sys.executable, "-c", runner_code],
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            try:
                ping_resp = None
                deadline = time.monotonic() + 8.0
                while time.monotonic() < deadline:
                    if os.path.exists(sock_p):
                        try:
                            resp = daemon._raw_unix_call("ping", {}, timeout_s=1.0, sock_path=sock_p)
                            if resp.get("ok"):
                                ping_resp = resp
                                break
                        except Exception:
                            pass
                    time.sleep(0.05)
                self.assertIsNotNone(ping_resp)
                orig_ino = os.stat(sock_p).st_ino
                pid_file = Path(sock_p + ".pid")
                self.assertTrue(pid_file.is_file())
                pid_doc = json.loads(pid_file.read_text(encoding="utf-8"))
                self.assertEqual(pid_doc.get("pid"), p1.pid)
                self.assertEqual(pid_doc.get("sock_ino"), orig_ino)

                # Simulate a successor daemon replacing sock_p with a brand-new Unix socket inode
                os.unlink(sock_p)
                replacement_srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                try:
                    replacement_srv.bind(sock_p)
                    new_ino = os.stat(sock_p).st_ino
                    self.assertNotEqual(orig_ino, new_ino)

                    p1.send_signal(signal.SIGTERM)
                    p1.wait(timeout=5.0)

                    # Exiting p1 must NOT have unlinked the replacement socket!
                    self.assertTrue(os.path.exists(sock_p))
                    self.assertEqual(os.stat(sock_p).st_ino, new_ino)
                finally:
                    replacement_srv.close()
                    if os.path.exists(sock_p):
                        os.unlink(sock_p)
            finally:
                if p1.poll() is None:
                    p1.kill()
                    p1.wait(timeout=2.0)


if __name__ == "__main__":
    unittest.main()
