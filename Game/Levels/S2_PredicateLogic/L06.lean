import Game.Metadata

World "PredicateLogic"
Level 2

Title "Quantifiers in Examples"

Introduction "
This level is the scaffold for Lecture L06 of Math 323.
Topic: Quantifiers with concrete examples.
"

Statement {X : Type} (P : X → Prop) (Q : Prop) :
  ((∃ x, P x) → Q) ↔ (∀ x, P x → Q) := by
  constructor
  · intro h x hx
    apply h
    use x
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    apply h x
    exact hx


Conclusion "This last message appears if the level is solved."

NewTactic
