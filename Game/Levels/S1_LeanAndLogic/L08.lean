import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L07

World "LeanAndLogic"
Level 8

Title "Currying"

Introduction "
## Haskell Curry, Moses Schönfinkel, and Lambda Calculus

**Currying** — converting a function of two arguments into a function that takes
arguments one at a time — is named after **Haskell Curry** (1900–1982), though
it was first described by **Moses Schönfinkel** (1889–1942) in 1924. Curry later
developed it extensively in **combinatory logic**.

**Alonzo Church** (1903–1995) independently developed the **lambda calculus** in
the 1930s, which provides a formal model of computation based on function
abstraction and application. Church's lambda calculus and Schönfinkel-Curry's
combinatory logic are equivalent in expressive power.

The logical content of currying is exactly this theorem: `(P ∧ Q → R) ↔ (P → Q → R)`.
In type theory, this is the **internal hom adjunction**: the function spaces
`(A × B → C)` and `(A → B → C)` are isomorphic.

In this level, let:
- **P** = \"Schönfinkel introduced combinators\"
- **Q** = \"Curry generalized the theory\"
- **R** = \"Currying is now a standard technique\"

---

**New tactic: `constructor` for `↔`.**
To prove `A ↔ B`, use `constructor` to split into two goals:
- goal 1: `A → B` (the forward direction)
- goal 2: `B → A` (the backward direction)
"

/-- **(P ∧ Q → R) if and only if (P → Q → R)**.
This is the logical statement of currying. -/
Statement curry_prop (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) := by
  Hint "Use `constructor` to split the `↔` into two implications."
  constructor
  · Hint "Forward direction: the goal is `(P ∧ Q → R) → P → Q → R`.
    Use `intro hpqr hp hq` to name all three hypotheses."
    intro hpqr hp hq
    Hint "Apply `{hpqr}` to the pair `⟨{hp}, {hq}⟩`."
    exact hpqr ⟨hp, hq⟩
  · Hint "Backward direction: the goal is `(P → Q → R) → P ∧ Q → R`.
    Use `rintro hpqr ⟨hp, hq⟩` to introduce and destruct simultaneously."
    rintro hpqr ⟨hp, hq⟩
    Hint "Apply `{hpqr}` step by step: first to `{hp}`, then to `{hq}`."
    exact hpqr hp hq

Conclusion "
You just proved currying in both directions.

The forward direction says: a function `f : P ∧ Q → R` that takes a pair can be
converted to `g : P → Q → R` that takes arguments one at a time. In Haskell
(named after Curry), this is the built-in `curry` and `uncurry` functions.

The backward direction is *uncurrying*.

**Biconditionals in Lean:** `A ↔ B` is the type `Iff A B`, a structure with two
fields: `mp : A → B` (modus ponens) and `mpr : B → A` (modus ponens reversed).
The `constructor` tactic fills these fields as two separate goals.

To *use* a biconditional `h : A ↔ B` later, you can write `h.mp` (forward)
or `h.mpr` (backward).
"

