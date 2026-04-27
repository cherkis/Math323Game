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
theorem prob1 : ∀ n : Nat, n ≤ n^2 := by
  intro n
  cases n with
  | zero => apply le_refl
  | succ n =>
    ring_nf
    rw [add_assoc]
    apply Nat.add_le_add_left
    rw [mul_two, add_assoc]
    exact Nat.le_add_right n _


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

def nat_div : Nat → Nat → Prop := fun a => fun b => ∃ k, a * k = b

def reflexive {X : Type} (rel : X → X → Prop) : Prop :=
  ∀ x : X, rel x x

def symmetric {X : Type} (rel : X → X → Prop) : Prop :=
  ∀ x y : X, rel x y → rel y x

def transitive {X : Type} (rel : X → X → Prop) : Prop :=
  ∀ x y z : X, rel x y → rel y z → rel x z

def antisymmetric {X : Type} (rel : X → X → Prop) : Prop :=
  ∀ x y : X, rel x y → rel y x → x = y

structure partial_order {X : Type} (rel : X → X → Prop) where
  refl : reflexive rel
  trans : transitive rel
  antisymm : antisymmetric rel

/--
  Human Language Proof Goes Here
-/
theorem prob1 : partial_order nat_div := by
  constructor
  · intro a
    use 1
    rw [mul_one]
  · rintro a b c ⟨j, hj⟩ ⟨k, hk⟩
    use j*k
    rw [←mul_assoc, hj, hk]
  · have : ∀ {a b}, b > 0 → nat_div a b → a ≤ b := by
      rintro a b bpos ⟨k, hk⟩
      rw [←hk]
      cases a with
      | zero => norm_num
      | succ n =>
        norm_num
        show 0 < k
        suffices k ≠ 0 by {exact Nat.zero_lt_of_ne_zero this}
        intro kzero
        subst kzero
        rw [mul_zero] at hk
        rw [←hk] at bpos
        apply lt_irrefl 0
        exact bpos
    intro a b hab hba
    rcases Nat.eq_zero_or_pos a with (ha | ha)
    · subst ha
      obtain ⟨p, hp⟩ := hab
      rw [←hp, zero_mul]
    rcases Nat.eq_zero_or_pos b with (hb | hb)
    · subst hb
      obtain ⟨p, hp⟩ := hba
      rw [←hp, zero_mul]
    apply le_antisymm
    apply this hb hab
    apply this ha hba





/--
  Human Language Proof Goes Here
-/
theorem prob2 : Equivalence (fun a => fun b => nat_div 2 (a+b)) := by
  constructor
  · intro x
    use x
    exact Nat.two_mul x
    done
  · intro x y ⟨k, hk⟩
    use k
    rw [add_comm]
    exact hk
    done
  · intro x y z ⟨j, hj⟩ ⟨k, hk⟩
    use (j + k) - y
    rw [mul_tsub, mul_add, hj, hk, add_assoc, ←add_assoc y, ←two_mul]
    rw [add_comm, add_assoc, Nat.add_sub_self_left, add_comm]
    done

end Relations



namespace Functions -- Stage 6

def fun_rel {X Y : Type} (f : X → Y) : X → X → Prop :=
  fun a => fun b => f a = f b

/--
  Human Language Proof Goes Here
-/
theorem prob1 {X Y : Type} (f : X → Y) : Equivalence $ fun_rel f  := by
  constructor
  · intro x
    rfl
    done
  · intro x y hxy
    unfold fun_rel at *
    rw [hxy]
    done
  · intro x y z
    unfold fun_rel
    intro h h'
    rw [h, h']
    done


/--
  Human Language Proof Goes Here
-/
theorem prob2 {X Y : Type} (f : X → Y) [Inhabited X] :
  (∃ g : Y → X, ∀ x, g (f x) = x) ↔ Function.Injective f := by
  constructor
  rintro ⟨g, hg⟩
  intro x₁ x₂ h
  rw [←hg x₁, ←hg x₂, h]
  intro h
  use Function.invFun f
  intro x
  sorry



#check Function.invFun

theorem prob3 {X Y : Type} (f : X → Y) :
  (∃ g : Y → X, ∀ y, f (g y) = y) ↔ Function.Surjective f := by
  constructor
  rintro ⟨g, hg⟩
  intro b
  use g b
  exact hg b
  intro h
  choose g hg using h
  use g

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
