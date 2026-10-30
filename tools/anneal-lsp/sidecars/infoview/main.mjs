import { execFile } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { createConnection } from 'node:net';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { Response, SidecarApp } from 'sidecar_sdk';

const execFileAsync = promisify(execFile);
const __dirname = dirname(fileURLToPath(import.meta.url));
const DAEMON_SCRIPT = resolve(__dirname, '..', '..', 'server', 'anneal_lsp_daemon.py');
const SOCK_PATH = process.env.ANNEAL_LSP_SOCKET || '/tmp/anneal-lean-lsp.sock';

function rawSocketRpc(action, args = {}, timeoutMs = 20000) {
  return new Promise((resolvePromise, rejectPromise) => {
    const client = createConnection(SOCK_PATH);
    let buf = '';
    let settled = false;
    const timer = setTimeout(() => {
      if (!settled) {
        settled = true;
        client.destroy();
        rejectPromise(new Error(`Daemon RPC '${action}' timed out after ${timeoutMs}ms`));
      }
    }, timeoutMs);

    client.on('connect', () => {
      client.write(JSON.stringify({ action, args }) + '\n');
    });

    client.on('data', (chunk) => {
      buf += chunk.toString('utf-8');
      const nl = buf.indexOf('\n');
      if (nl !== -1 && !settled) {
        settled = true;
        clearTimeout(timer);
        const line = buf.slice(0, nl);
        client.end();
        try {
          resolvePromise(JSON.parse(line));
        } catch (err) {
          rejectPromise(err);
        }
      }
    });

    client.on('error', (err) => {
      if (!settled) {
        settled = true;
        clearTimeout(timer);
        rejectPromise(err);
      }
    });
  });
}

async function daemonRpc(action, args = {}, timeoutMs = 25000) {
  try {
    return await rawSocketRpc(action, args, timeoutMs);
  } catch (_firstErr) {
    await execFileAsync('/usr/bin/python3', [DAEMON_SCRIPT, '--socket', SOCK_PATH], {
      timeout: 6000,
    });
    return await rawSocketRpc(action, args, timeoutMs);
  }
}

const app = new SidecarApp();

app.page('/', () => readFileSync(join(__dirname, 'index.html'), 'utf-8'));

app.api('/styles.css', () => {
  const css = readFileSync(join(__dirname, 'styles.css'), 'utf-8');
  return new Response(css, { contentType: 'text/css' });
}, 'GET');

app.api('/api/state', async () => {
  return await daemonRpc('ui_state', {}, 6000);
}, 'GET');

app.api('/api/obligations', async (data) => {
  const query = data.query || '';
  const workspace = data.workspace || '';
  return await daemonRpc('anneal_item_bridge', { query, workspace }, 10000);
}, 'GET');

app.api('/api/inspect_goal', async (data) => {
  return await daemonRpc('lean_goal', {
    file: data.file,
    line: Number(data.line || 1),
    column: data.column ? Number(data.column) : undefined,
  }, 45000);
}, 'POST');

app.api('/api/diagnostics', async (data) => {
  return await daemonRpc('lean_diagnostics', { file: data.file }, 45000);
}, 'POST');

app.api('/api/multi_attempt', async (data) => {
  return await daemonRpc('lean_multi_attempt', {
    file: data.file,
    line: Number(data.line || 1),
    tactics: data.tactics || [],
  }, 45000);
}, 'POST');

app.api('/api/audit', async (data) => {
  return await daemonRpc('anneal_audit_preview', { file: data.file }, 45000);
}, 'POST');

app.api('/api/restart_worker', async (data) => {
  return await daemonRpc('lean_restart_workspace', { root: data.root || 'all' }, 10000);
}, 'POST');

await app.run();
