import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L06

World "LeanAndLogic"
Level 7

Title "Distributivity of And over Or"

Introduction "
## Martin-Löf Type Theory

**Martin-Löf Type Theory** (MLTT) is the foundational system Lean is built on.
It extends the Curry-Howard correspondence to *dependent* types — types that
can depend on values. For example, the type of vectors of length `n` depends on
the natural number `n`.

MLTT comes in several variants. The most important distinction is:
- **Inductive types** — types defined by constructors (like `Nat`, `List`, `Or`)
- **Dependent function types** — `(x : A) → B x`, generalizing `A → B`

The **Calculus of Inductive Constructions** (CIC), developed by Thierry Coquand
and Christine Paulin-Mohring in the late 1980s, forms the basis for Coq and
inspired Lean's type theory.

In this level, let:
- **P** = \"MLTT is constructive\"
- **Q** = \"MLTT uses dependent types\"
- **R** = \"MLTT uses inductive types\"

---

**New pattern: nested `rintro`.**
The hypothesis has the form `P ∧ (Q ∨ R)` — a conjunction whose right
component is itself a disjunction. The pattern `⟨hp, hq | hr⟩` destructs
both layers at once, producing two goals.
"

/-- Conjunction distributes over disjunction:
**P and (Q or R)** implies **(P and Q) or (P and R)**. -/
Statement and_distrib_or (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  Hint "Use `rintro ⟨hp, hq | hr⟩` to destruct the conjunction *and* case-split
  on the inner disjunction in one step. This creates two goals."
  rintro ⟨hp, hq | hr⟩
  · Hint "In this branch: `{hp} : P` and `{hq} : Q`. The goal is `(P ∧ Q) ∨ (P ∧ R)`.
    Use `left` and then build the conjunction."
    left
    exact ⟨hp, hq⟩
  · Hint "In this branch: `{hp} : P` and `{hr} : R`. The goal is `(P ∧ Q) ∨ (P ∧ R)`.
    Use `right` and then build the conjunction."
    right
    exact ⟨hp, hr⟩

Conclusion "
The nested `rintro` pattern `⟨hp, hq | hr⟩` is doing a lot at once:
- The outer `⟨·, ·⟩` destructs the conjunction `P ∧ (Q ∨ R)` into `P` and `Q ∨ R`
- The inner `· | ·` case-splits on the disjunction `Q ∨ R`

This mirrors exactly how you would write the proof in natural language:
*\"Assume P and (Q or R). Case 1: P and Q. Then (P ∧ Q), so left. Case 2: P and R.
Then (P ∧ R), so right.\"*

The discipline of **proof terms** in type theory makes this correspondence
between informal and formal proof unusually tight.
"

