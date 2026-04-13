import Game.Metadata

World "LeanAndLogic"
Level 1

Title "Type Theory and Lean Syntax"

Introduction "
This level is the scaffold for Lecture L01 of Math 323.
Topic: Type theory, Lean syntax, and term-mode proofs.

TO START PROVE THAT:
"


variable (X : Type)

Statement (f : X → X → Bool) :
  ∃ g : X → Bool, ∀ x : X, f x ≠ g := by
    exists (fun x => not $ f x x)
    intro x h
    have : ∀ b : Bool, ¬(not b = b) := fun b => Bool.not_not_eq.mpr rfl
    apply this $ f x x
    rewrite (occs := .pos [2]) [h]
    rfl

/-
Statement (x y : Nat) (h : x = 2) (g: y = 4) : y = y := by
  rfl
--  Hint "You can either start using `{h}` or `{g}`."
--  Branch
  --   rw [g]
  --   Hint "You should use `{h}` now."
  --   rw [h]
  -- rw [h]
  -- Hint "You should use `{g}` now."
  -- rw [g]

Conclusion "This last message appears if the level is solved."
-/

NewTactic rfl intro rewrite
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
