import Game.Metadata

World "NumberSystems"
Level 1

Title "Number Systems and Coercions"

Introduction "
This level is the scaffold for Lecture L20 of Math 323.
Topic: Nat, Int, Rat, Real, field structure, and coercions.
"

Statement (x y : Nat) (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

NewTactic field_simp positivity push_cast exact_mod_cast gcongr
