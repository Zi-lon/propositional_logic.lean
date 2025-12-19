import PropositionalLogic.Syntax

open Formula

/-
Sanity checks: using ℕ as the variable type.
-/

#synth Countable (Formula Nat)
#synth Repr (Formula Nat)

def p : Formula Nat := var 0
def q : Formula Nat := var 1
def r : Formula Nat := var 2

#eval (¬(p ∧ q) ↔  r).complexity
-- #eval (subformulas (¬(p ∧ q) ↔ r)).toList
