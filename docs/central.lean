--import Mathlib.Tactic
--import MIL.common
--import Game.Metadata

/-
 # Central Problems for Each Stage
Each stage should have about 2 core theorems about the concept
-/

namespace LeanAndLogic -- Stage 1

theorem prob0 : True := sorry

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
  constructor
  exact hpq hp
  exact hpr hp

theorem prob5: (P → R) → (Q → R) → P ∨ Q → R := by
  intro hpr hqr
  rintro (hp | hq)
  exact hpr hp
  exact hqr hq

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
  intro hnpq
  constructor
  intro hp
  have : P ∨ Q := by
    left; exact hp
  contradiction
  intro hq
  have : P ∨ Q := by
    right; exact hq
  contradiction
  intro ⟨hnp,hnq⟩
  rintro (hp | hq)
  contradiction
  contradiction

theorem prob10: (P → Q) → (¬ Q → ¬ P) := by
  intro hpq hnq hp
  exact hnq (hpq hp)

theorem prob11_1: ¬¬P → P := by
  exact Classical.not_not.mp

theorem prob11_2: P → ¬¬P := by
  intro hp
  intro hnp
  contradiction


/--
  Human Language Proof Goes Here
-/

end LeanAndLogic



namespace PredicateLogic -- Stage 2
/--
  Human Language Proof Goes Here
-/
theorem prob1 : True := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 : True := sorry

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
theorem cantor {X : Type} (f : X → X → Bool) :
  ∃ g : X → Bool, ∀ x : X, f x ≠ g := by
  exists (fun x => not $ f x x)
  intro x h
  have : ∀ b : Bool, ¬(not b = b) := fun b => Bool.not_not_eq.mpr rfl
  apply this $ f x x
  rewrite (occs := .pos [2]) [h]
  rfl
  done


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
