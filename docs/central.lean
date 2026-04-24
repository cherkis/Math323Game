import Mathlib.Tactic

/-
 # Central Problems for Each Stage
Each stage should have about 2 core theorems about the concept.
This document is meant to help scaffold for the stages, so hint
infrastructure and the like does not yet need to be consider
-/

namespace LeanAndLogic -- Stage 1

theorem prob0 : True := trivial

variable (P Q R: Prop)

theorem prob1: P ∧ Q → Q ∧ P := by
  intro ⟨hp,hq⟩
  exact ⟨hq,hp⟩

theorem prob2: P ∨ Q → Q ∨ P := by
  rintro (hp | hq)
  · right; exact hp
  · left; exact hq

theorem prob3: P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  rintro ⟨hp,(hq | hr)⟩
  · left; exact ⟨hp,hq⟩
  · right; exact ⟨hp,hr⟩

theorem prob4: (P → Q) → (P → R) → P → Q ∧ R := by
  intro hpq hpr hp
  exact ⟨hpq hp, hpr hp⟩

theorem prob5: (P → R) → (Q → R) → P ∨ Q → R := by
 intro hpr hqr
 rintro (hp | hq)
 · exact hpr hp
 · exact hqr hq

theorem prob6: (P ∧ Q → R) ↔ P → (Q → R) := by
  constructor
  intro hpqr hp hq
  exact hpqr ⟨hp,hq⟩
  intro hpqr ⟨hp,hq⟩
  exact hpqr hp hq

theorem prob7: P → P ∨ Q := by
  intro hp
  left; exact hp

theorem prob8: ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q  := by
  constructor
  · intro h
    constructor
    · intro hp; exact h (Or.inl hp)
    · intro hq; exact h (Or.inr hq)
  · rintro ⟨hnp, hnq⟩ (hp | hq)
    · exact hnp hp
    · exact hnq hq

theorem prob10: (P → Q) → (¬ Q → ¬ P) := by
  intro hpq hnq hp
  exact hnq (hpq hp)

theorem prob11_1: ¬¬P → P := by
  exact Classical.not_not.mp

theorem prob11_2: P → ¬¬P := by
  intro hp
  intro hnp
  contradiction


end LeanAndLogic



namespace PredicateLogic -- Stage 2
/--
  We prove the statements comprising the conjunction separately.

  For the forward direction, we are required to use classical logic.
  The contrapositive to the forwards direction
  is "¬ (∃ x, ¬ P x) → ∀ x,  P x". Suppose that there does not exist
  any x such that P x is false, and let x be an arbitrary term of type X.
  Suppose P x is false. Then we have shown that there DOES exist an x
  such that P x is false, so we have contradicted our previous assumption.
  Therefore our supposition that "P x is false" is itself false, i.e.
  P x is true.

  For the backward direction, suppose that there exists an x such that
  P x is false. Then clearly it is false that for all x, P x is true,
  since we have a counterexample. In more detail, if we assume that
  it is true that "∀ x, P x", then we have that P x is true, but we had
  already assumed that P x is false. Since P x cannot be both true and false,
  the claim "∀ x, P x" must be false.

-/
theorem quantifier_negation {X : Type} (P : X → Prop) :
  (¬ (∀ x, P x) ↔ ∃ x, ¬ P x):= sorry


/--
  First, we prove the forward direction, so we suppose that
  (∃ x, P x) → Q. In other words, if we can find a single
  element x such that P x is true, then Q is also true. Now we
  want to show that for all x, if P x is true, then Q is true.
  Let x be an arbitrary element such that P x is true. Then by our
  initial supposition, Q is true, and we are done.

  Now we prove the backwards direction, so we suppose that
  ∀ x, P x → Q, and we want to show that (∃ x, P x) → Q. So
  we further assume that there exists some x such that P x is true.
  By initial assumption, we have that Q is true, and again, we are done.
-/
theorem exists_imp_iff_forall_imp {X : Type} (P : X → Prop) (Q : Prop) :
  ((∃ x, P x) → Q) ↔ (∀ x, P x → Q) := by
  constructor
  · intro h x hx
    apply h
    exists x
  · rintro h ⟨x, hx⟩
    apply h x
    exact hx
end PredicateLogic



namespace Induction -- Stage 3
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end Induction



namespace Sets -- Stage 4
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end Sets



namespace Relations -- Stage 5
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end Relations



namespace Functions -- Stage 6
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end Functions



namespace Cardinality -- Stage 7
/--
  Human Language Proof Goes Here
-/
theorem Cantor (X : Type) (f : X → Set X) :
  ¬ Function.Surjective f := sorry

/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end Cardinality



namespace NumberSystems -- Stage 8
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end NumberSystems



namespace SupInf -- Stage 9
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end SupInf



namespace SequencesLimits -- Stage 10
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end SequencesLimits



namespace Topology -- Stage 11
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

end Topology
