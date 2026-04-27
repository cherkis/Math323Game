import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L04

World "LeanAndLogic"
Level 5

Title "Conjunction from Two Implications"

Introduction "
## Gerhard Gentzen and Natural Deduction

**Gerhard Gentzen** (1909–1945) was a German logician who in 1935 introduced
two revolutionary proof systems: **natural deduction** (NK/NJ) and the
**sequent calculus** (LK/LJ). These are still the dominant frameworks for
proof theory today.

Natural deduction was designed to mimic the way mathematicians actually reason:
you introduce hypotheses, derive conclusions, and discharge assumptions.
Every logical connective has **introduction rules** (how to prove it) and
**elimination rules** (how to use it). The system is remarkably clean.

Gentzen's life was tragically short — he died in 1945 in a Prague internment
camp at age 35. Despite this, his 1935 dissertation is one of the most
influential documents in the history of logic.

In this level, let:
- **P** = \"Gentzen invented natural deduction\"
- **Q** = \"Gentzen's work influenced modern proof theory\"
- **R** = \"Gentzen created the sequent calculus\"

---

**Proof pattern this level:** Multiple `intro` steps followed by constructing
a conjunction from two function applications. If `hpq : P → Q` and `hp : P`,
then `hpq hp : Q` is the application of the function to its argument.
"

/-- From `P → Q` and `P → R` and `P`, derive `Q ∧ R`. -/
Statement hyp_conj (P Q R : Prop) : (P → Q) → (P → R) → P → Q ∧ R := by
  Hint "Introduce all three hypotheses with `intro hpq hpr hp`."
  intro hpq hpr hp
  Hint "Now you have `{hpq} : P → Q`, `{hpr} : P → R`, and `{hp} : P`.
  Build the conjunction: `exact ⟨{hpq} {hp}, {hpr} {hp}⟩`.
  Notice how `{hpq} {hp}` *applies* the function `{hpq}` to the argument `{hp}`."
  exact ⟨hpq hp, hpr hp⟩

Conclusion "
The expression `hpq hp` is **function application**: `hpq : P → Q` is a function,
and `hp : P` is its argument, so `hpq hp : Q`.

This is Curry-Howard again: under the correspondence, implication `P → Q` *is* a
function type, and a proof of `P → Q` *is* a function. Applying a proof to an
argument is the same as applying a function.

Gentzen's **conjunction introduction rule** says: to prove `Q ∧ R`, prove Q and
prove R separately. That is exactly what `exact ⟨hpq hp, hpr hp⟩` does.

**Alternative proof using `constructor`:**
```
intro hpq hpr hp
constructor
· exact hpq hp
· exact hpr hp
```
The `constructor` tactic splits a conjunction goal into two subgoals.
"

NewTactic constructor
