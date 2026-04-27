import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L11

World "LeanAndLogic"
Level 12

Title "Double Negation Elimination"

Introduction "
## Classical Logic and the Law of Excluded Middle

We have reached the boundary between **constructive** and **classical** logic.

In constructive (intuitionistic) logic, `¬¬P → P` — **double negation
elimination** — is *not* provable. Brouwer rejected it because `¬¬P` only
says \"a proof of `¬P` is impossible\", which does not hand you a construction
of `P`.

In **classical** logic, we add one of the following as an axiom (they are
all equivalent):
- **Law of Excluded Middle (LEM):** `P ∨ ¬P` for every P
- **Double Negation Elimination:** `¬¬P → P` for every P
- **Pierce's Law:** `((P → Q) → P) → P` for every P, Q

Lean is built on constructive type theory, but the `Classical` namespace
provides these axioms explicitly. Using them is allowed and often necessary
for \"real\" mathematics — Lean's Mathlib uses classical logic throughout.

**Gödel's double-negation translation** (1933) showed that every classical
theorem can be translated into an intuitionistic theorem by systematically
inserting double negations. This means classical and constructive mathematics
are more closely related than they appear.

---

**New tactic: `by_contra`.**
`by_contra h` introduces the hypothesis `h : ¬P` (where `P` is the goal)
and changes the goal to `False`. This is proof by contradiction.
"

/-- **Double negation elimination**: `¬¬P → P`. This requires classical logic. -/
Statement dne (P : Prop) : ¬¬P → P := by
  Hint "The goal is `¬¬P → P`. Use `intro hnnp` to introduce the hypothesis."
  intro hnnp
  Hint "Now you have `{hnnp} : ¬¬P` and need to prove `P`.
  Try `by_contra hnp` — this introduces `hnp : ¬P` and changes the goal to `False`."
  by_contra hnp
  Hint "You have `{hnnp} : ¬¬P` (i.e., `¬P → False`) and `{hnp} : ¬P`.
  Apply `{hnnp}` to `{hnp}`: `exact {hnnp} {hnp}`."
  exact hnnp hnp

Conclusion "
You used `by_contra` — proof by contradiction — which is a classical principle.

**The alternative: use `Classical.not_not.mp` directly.**
```
intro hnnp
exact Classical.not_not.mp hnnp
```
The theorem `Classical.not_not : ¬¬P ↔ P` lives in Lean's classical library.

**Summary of the world so far.**
You've now proven the core laws of propositional logic:
- Weakening, symmetry of ∧ and ∨, distributivity
- Currying (the logical statement of Curry-Howard)
- De Morgan's law, contrapositive, double negation

The theorems you proved are available in your inventory — in the next world,
**Predicate Logic**, they'll be tools rather than goals.

**Historical coda:** The axiom `Classical.em : P ∨ ¬P` in Lean traces back to
Ernst Zermelo's 1904 proof of the Well-Ordering Theorem, which made explicit use
of the Axiom of Choice (equivalent to LEM for propositions). The ensuing
controversy between Brouwer and Hilbert shaped 20th-century foundations of
mathematics.
"

NewTactic by_contra
