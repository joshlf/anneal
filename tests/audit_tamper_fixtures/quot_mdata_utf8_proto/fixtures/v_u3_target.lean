-- V-U3 Fixture: clean ASCII string literal and binder name whose `LeanString`
-- payloads are binary-patched in-place with RFC 3629 malformed UTF-8 sequences,
-- embedded NULs, and forged `m_length` codepoint counts.
prelude
import Init.Core

def u3StrTarget : String := "UUUUUUUU"
def u3NameTarget (bbbbbbbb : Nat) : Nat := bbbbbbbb
