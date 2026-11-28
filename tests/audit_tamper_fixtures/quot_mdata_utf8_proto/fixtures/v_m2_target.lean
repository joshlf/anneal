-- V-M2 Fixture: clean closed definitions with Nat, String, and polymorphic Level
-- so binary `.olean` mutators can flip `Expr.m_data` (`approxDepth`, `hash`,
-- `hasLevelParam`), `Level.m_data`, and `Name.hash`, plus test `Expr.beq`
-- duplicate-subterm cache poisoning (`fnOk` vs `fnBad`).
prelude
import Init.Core

def m2Id (x : Nat) : Nat := x
def m2Poly.{u} (α : Sort u) (x : α) : α := x
def m2App (x : Nat) : Nat := Nat.succ x
def fnOk (a : Nat) : Nat := a
def fnBad (b : Nat) : Nat := b
