import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L10

World "LeanAndLogic"
Level 11

Title "De Morgan: Not (P or Q)"

Introduction "
## Augustus De Morgan

**Augustus De Morgan** (1806–1871) was a British mathematician and logician,
one of the founders of modern formal logic alongside George Boole.
His **De Morgan's laws** describe how negation interacts with conjunction and
disjunction:

$$¬(P \\lor Q) \\iff ¬P \\land ¬Q$$
$$¬(P \\land Q) \\iff ¬P \\lor ¬Q$$

The first law (our theorem) says: *\"not (P or Q)\"* is the same as
*\"not P and not Q\"*. Intuitively: to rule out both possibilities in a
disjunction, you must rule out each individually.

**Importantly, both directions of this law hold constructively** — no
classical axioms needed. The second De Morgan law, `¬(P ∧ Q) ↔ ¬P ∨ ¬Q`,
is more subtle: the left-to-right direction `¬(P ∧ Q) → ¬P ∨ ¬Q` requires
classical logic.

In this level, let:
- **P** = \"De Morgan was a professor at University College London\"
- **Q** = \"De Morgan founded the London Mathematical Society\"

(Both are true! He was the first professor of mathematics at UCL and the
first president of the London Mathematical Society.)

---

This level combines `constructor` (for `↔`), `rintro` for nested patterns,
and negation reasoning. It's the most complex level so far — take it step by step.
"

/-- **De Morgan's first law**: `¬(P ∨ Q) ↔ ¬P ∧ ¬Q`. -/
Statement not_or_iff_and_not (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  Hint "Use `constructor` to split the biconditional into two goals."
  constructor
  · Hint "Forward: the goal is `¬(P ∨ Q) → ¬P ∧ ¬Q`. Use `intro h` to name the hypothesis."
    intro h
    Hint "Now `{h} : ¬(P ∨ Q)` (i.e., `P ∨ Q → False`). Use `constructor` to split
    the goal `¬P ∧ ¬Q`, then in each branch introduce the assumption and apply `{h}`
    to `Or.inl` or `Or.inr` as appropriate."
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · Hint "Backward: the goal is `¬P ∧ ¬Q → ¬(P ∨ Q)`. Use `rintro ⟨hnp, hnq⟩ (hp | hq)`
    to introduce and destruct both hypotheses at once, splitting into two subgoals."
    rintro ⟨hnp, hnq⟩ (hp | hq)
    · exact hnp hp
    · exact hnq hq

Conclusion "
The backward direction used a powerful combination:
`rintro ⟨hnp, hnq⟩ (hp | hq)` introduces *and* destructs two hypotheses at once —
the conjunction `¬P ∧ ¬Q` and the disjunction `P ∨ Q` — leaving two subgoals.

**Why doesn't `¬(P ∧ Q) → ¬P ∨ ¬Q` work constructively?**
Given `h : ¬(P ∧ Q)`, to prove `¬P ∨ ¬Q` constructively you'd need to decide
whether `¬P` or `¬Q` holds — but you can't do that without knowing which of P,
Q is false. Classically, `¬(P ∧ Q)` means \"at least one is false\", so LEM
lets you identify which. Constructively, `h` only tells you they can't both be
true simultaneously.

This is one of many places where classical and intuitionistic logic diverge.
"

