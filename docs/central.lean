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
  (¬ (∀ x, P x) ↔ ∃ x, ¬ P x) := sorry

theorem prob2 {X Y : Type} (P : X → Y → Prop) :
  (∃ y, ∀ x, P x y) → (∀ x, ∃ y, P x y) := by
  rintro ⟨y, hy⟩ x
  use y
  apply hy


theorem prob3 {X : Type} (x₁ x₂ : X) (h : x₁ ≠ x₂) :
  ∃ P : X → X → Prop,
  ¬ ((∀ x, ∃ y, P x y) → (∃ y, ∀ x, P x y)) := by
  use fun x => fun y => x=y
  rw [Classical.not_imp]
  constructor
  · intro x
    use x
  · push_neg
    intro y
    rcases eq_or_ne x₁ y with (hy | hy)
    · use x₂
      intro hy'
      apply h
      rw [hy, hy']
    · use x₁

theorem prob4 (A P Q : Prop) :
  ((A → P) ∨ (A → Q)) ↔ A → P ∨ Q := by
    constructor
    · rintro (hp | hq) ha
      · left
        apply hp
        exact ha
      · right
        apply hq
        exact ha
    · intro h
      rcases Classical.em A with (ha | hna)
      · rcases h ha with (hp | hq)
        · left
          intro _
          exact hp
        · right
          intro _
          exact hq
      · left
        intro ha
        exfalso
        apply hna
        exact ha


theorem prob4_1 {X : Type} (P Q : X → Prop) :
  ((∀ x, P x) ∨ (∀ x, Q x)) → ∀ x, P x ∨ Q x := by
    rintro (hP | hQ) x
    · left
      apply hP
    · right
      apply hQ

theorem prob4_2 {X : Type} (x₁ x₂ : X) (h : x₁ ≠ x₂) : ∃ P Q : X → Prop,
  ¬(∀ x, P x ∨ Q x → ((∀ x, P x) ∨ (∀ x, Q x))) := by
  use fun x => x = x₁, fun x => x = x₂
  push_neg
  use x₁
  constructor
  · left
    rfl
  constructor
  · use x₂
    intro h'
    apply h
    rw [h']
  · use x₁


theorem prob5 {X : Type} (P Q : X → Prop) :
  (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
    constructor
    · intro h
      constructor
      · intro x
        specialize h x
        obtain ⟨hp, _⟩ := h
        exact hp
      · intro x
        specialize h x
        obtain ⟨_, hq⟩ := h
        exact hq
    · rintro ⟨hp, hq⟩ x
      specialize hp x
      specialize hq x
      exact ⟨hp, hq⟩



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

def int_div : Int → Int → Prop := fun a => fun b => ∃ k : Nat, a * k = b

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
theorem prob1 : partial_order int_div := by
  constructor
  · intro x
    use 1
    rw [Nat.cast_one, mul_one]
  · rintro x y z ⟨k, hk⟩ ⟨l, hl⟩
    use k*l
    rw [Nat.cast_mul, ←mul_assoc, hk, hl]
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    rcases eq_or_ne x 0 with (subst | xne0)
    · subst subst
      rw [←ha, zero_mul]
    rw [←ha, mul_assoc, ←sub_eq_zero, ←mul_one x, mul_assoc, ←mul_sub] at hb
    rw [Int.mul_eq_zero, one_mul, sub_eq_zero] at hb
    rcases hb with ⟨xz | h⟩
    · linarith
    rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at h
    rcases h with (⟨h, _⟩|⟨h, _⟩)
    · rw [h, mul_one] at ha
      exact ha
    exfalso
    linarith


/--
  Human Language Proof Goes Here
-/
theorem prob2 (n : Int) : Equivalence (fun a => fun b => ∃ k, n * k = a - b) := by
  constructor
  · intro x
    use 0
    norm_num
  · rintro x y ⟨k, hk⟩
    use -k
    rw [mul_neg, hk, neg_sub]
  · rintro x y z ⟨k, hk⟩ ⟨l, hl⟩
    use k + l
    rw [mul_add, hk, hl]
    norm_num

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

def rel {X : Type}: Set X → Set X → Prop := fun S ↦ fun T ↦
  ∃ f : S → T, ∃ g : T → S, f ∘ g = id ∧ g ∘ f = id


/--
  Human Language Proof Goes Here
-/
theorem prob2 {X : Type} : Equivalence $ @rel X := by
  constructor
  · intro S
    use id, id
    rw [CompTriple.comp_eq, and_self]
    done
  · intro S T ⟨f, g, hfg, hgf⟩
    use g, f
    done
  · intro S T U ⟨f, g, hfg, hgf⟩ ⟨j, k, hjk, hkj⟩
    unfold rel
    use j ∘ f
    use g ∘ k
    rw [←Function.comp_assoc, Function.comp_assoc j, hfg]
    rw [Function.comp_id, hjk]
    use rfl
    rw [←Function.comp_assoc, Function.comp_assoc g, hkj]
    rw [Function.comp_id, hgf]

instance Std_inst {X : Type} : Setoid (Set X) := ⟨rel, prob2⟩

def ordinal : Type := Quotient $ @Std_inst Nat

def ord_mk (S : Set Nat) : ordinal := Quotient.mk' S

theorem prob3 : Infinite ordinal := sorry







end Cardinality



namespace NumberSystems -- Stage 8
/--
  Human Language Proof Goes Here
-/
theorem prob1 : ∃ S : Set Int, S.Nonempty ∧ ∀ n ∈ S, ∃ m ∈ S, m < n := sorry


/--
  Human Language Proof Goes Here
-/
theorem prob2 {F : Type} [Field F] : ∀ x : F, x * 0 = x := sorry

theorem prob3 {p : Nat} (hp : Nat.Prime p) : ∀ q : Rat, q*q ≠ p := sorry

/-
def irrational (x : Real) : Prop := ∀ q : Rat, x ≠ ↑q
noncomputable def root2 : Real := Real.sqrt 2
axiom obv : irrational root2

theorem prob3_5 : ∃ α β : Real, irrational α ∧ irrational β ∧ α^β ∈ (Set.range Rat.cast) := by
  rcases Classical.em (irrational (root2^root2)) with (h | h)
  · use root2 ^ root2, root2, h, obv
    use 2
    push_cast
    sorry
  · use root2, root2, obv, obv
    contrapose! h
    intro q hq
    apply h
    rw [Set.mem_range]
    use q
    rw [hq]
-/

theorem prob4 : ∀ x : Real, ∃ n : Nat, x < n := sorry



end NumberSystems



namespace SupInf -- Stage 9

def isSup {X : Type} [PartialOrder X] (S : Set X) (m : X) : Prop :=
  (∀ x ∈ S, x ≤ m) ∧ (∀ m' : X, (∀ x ∈ S, x ≤ m') → m ≤ m')
def isInf {X : Type} [PartialOrder X] (S : Set X) (m : X) : Prop :=
  (∀ x ∈ S, m ≤ x) ∧ (∀ m' : X, (∀ x ∈ S, m' ≤ x) → m' ≤ m)

/--
  Human Language Proof Goes Here
-/
theorem prob1 {X : Type} [PartialOrder X] (S : Set X) (m m' : X) :
  isSup S m → isSup S m' → m = m' := sorry

def S_recip : Set Real := {x | ∃ n : Nat, x = (n+1 : Real)⁻¹}

/--
  Human Language Proof Goes Here
-/
theorem prob2 : isInf S_recip 0 := sorry

variable {X : Type} {Y : Type} [PartialOrder Y]

def bdd_above (f : X → Y) : Prop :=
  ∃ M : Y, ∀ x, f x ≤ M

def isFunSup (f : X → Y) (M : Y) : Prop := isSup (f '' (Set.univ)) M

theorem prob3 {f g : X → ℝ} (hf : bdd_above f) (hg : bdd_above g) :
  bdd_above (f + g) := sorry

theorem prob4 {f g : X → ℝ} (hf : bdd_above f) (hg : bdd_above g)
  {fM gM y : ℝ} (hf' : isFunSup f fM) (hg' : isFunSup g gM)
  (h : isFunSup (f+g) y) : y ≤ fM + gM := sorry

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
