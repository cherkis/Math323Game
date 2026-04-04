import Game.Metadata

World "Cardinality"
Level 4

Title "Interleaving Bijection"

Introduction "
This level is the scaffold for Lecture L19 of Math 323.
Topic: The line-equals-plane interleaving bijection.
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

-- Additional lecture tactic form from the plan not representable in `NewTactic`: <;>
NewTactic congr_arg pick_goal nlinarith
