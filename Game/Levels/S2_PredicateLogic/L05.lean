import Game.Metadata

World "PredicateLogic"
Level 1

Title "Universal and Existential Quantifiers"

Introduction "
This level is the scaffold for Lecture L05 of Math 323.
Topic: Universal and existential quantifiers.
"

Statement {X : Type} (P : X → Prop) :
  (¬ (∀ x, P x) ↔ ∃ x, ¬ P x):= by
  constructor
  · intro h
    by_contra h'
    apply h
    intro x
    by_contra h''
    apply h'
    use x
  · intro h h'
    obtain ⟨x, hx⟩ := h
    apply hx
    exact h' x


Conclusion "This last message appears if the level is solved."

NewTactic use linarith
