import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L05

World "LeanAndLogic"
Level 6

Title "Disjunction Elimination"

Introduction "
## Sequent Calculus and Disjunction Elimination

Gentzen's **sequent calculus** pairs every introduction rule with an elimination
rule. The elimination rule for disjunction says:

> To prove R from `P ∨ Q`, it suffices to prove R from P *and* R from Q.

This is sometimes called **proof by cases** or *disjunction elimination*, and
it is one of the most-used proof techniques in mathematics.

In Lean, this pattern arises when you have a disjunction in your hypotheses —
as the *last* argument here — and need to dispatch each case.

In this level, let:
- **P** = \"The sequent calculus is complete\"
- **Q** = \"Natural deduction is complete\"
- **R** = \"The logical system is complete\"

The theorem says: if P implies R, and Q implies R, and we know P or Q, then R.

---

**Key pattern this level:** Using `rintro` *after* introducing other hypotheses.
The `intro` tactic can introduce multiple things at once with `intro h1 h2 ...`,
and then `rintro` handles the remaining disjunction.
"

/-- If **P implies R** and **Q implies R**, then **P or Q implies R**. -/
Statement or_elim_prop (P Q R : Prop) : (P → R) → (Q → R) → P ∨ Q → R := by
  Hint "Introduce the two function hypotheses first: `intro hpr hqr`."
  intro hpr hqr
  Hint "Now the goal is `P ∨ Q → R`. Use `rintro (hp | hq)` to split on the
  disjunction."
  rintro (hp | hq)
  · Hint "In this case you have `{hp} : P`. Apply `{hpr}` to get `R`."
    exact hpr hp
  · Hint "In this case you have `{hq} : Q`. Apply `{hqr}` to get `R`."
    exact hqr hq

Conclusion "
This theorem is **modus ponendo tollens** or disjunction elimination — one of
Gentzen's original elimination rules. In the sequent calculus it is written:

```
  Γ, P ⊢ R    Γ, Q ⊢ R    Γ ⊢ P ∨ Q
  ─────────────────────────────────── (∨E)
               Γ ⊢ R
```

The 'Γ' represents the ambient hypotheses. The rule says: to eliminate a
disjunction from the hypotheses, handle both branches.

Note that this proof is **entirely constructive** — no classical axioms needed.
Disjunction elimination works the same way in intuitionistic logic as in
classical logic.
"

