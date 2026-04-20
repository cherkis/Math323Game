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

theorem prob1: P ∧ Q → Q ∧ P := by sorry

theorem prob2: P ∨ Q → Q ∨ P := by sorry

theorem prob3: P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)

theorem prob4: (P → Q) → (P → R) → P → Q ∧ R := by sorry

theorem prob5: (P → R) → (Q → R) → P ∨ Q → R := by sorry

theorem prob6: (P ∧ Q → R) ↔ P → (Q → R) := by sorry

theorem prob7: ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q  := by sorry

theorem prob8: ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by sorry

theorem prob9: (P → Q) → (¬ Q → ¬ P) := by sorry

theorem prob10: ¬¬P → P := by sorry

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
