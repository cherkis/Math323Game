import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L02

World "LeanAndLogic"
Level 3

Title "Conjunction is Symmetric"

Introduction "
## The Curry-Howard Correspondence

The **Curry-Howard correspondence** is one of the deepest ideas in logic and
computer science. It says that propositions and types are the *same thing*,
and proofs and programs are the *same thing*:

| Logic        | Type Theory           |
|--------------|-----------------------|
| proposition  | type                  |
| proof        | program (term)        |
| `P ∧ Q`      | `P × Q` (product type)|
| `P → Q`      | `P → Q` (function type)|

This was observed independently by **Haskell Curry** (1934) and **William Howard**
(1969), though the ideas were implicit in Brouwer's intuitionism much earlier.

In this level, let:
- **P** = \"Lean is a proof assistant\"
- **Q** = \"Lean is a functional programming language\"

(Both are true — Lean 4 is genuinely used as a general-purpose language.)

The theorem `P ∧ Q → Q ∧ P` says conjunction is symmetric.

---

**New syntax this level:**
- `intro ⟨hp, hq⟩` — introduces a conjunction and immediately destructs it:
  a hypothesis `h : P ∧ Q` becomes two hypotheses `hp : P` and `hq : Q`
- `exact ⟨hq, hp⟩` — constructs a conjunction from two existing proofs
- `obtain ⟨hp, hq⟩ := h` — alternative way to destruct an existing hypothesis
"

/-- Conjunction is symmetric: if **P and Q**, then **Q and P**. -/
Statement and_symm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  Hint "The goal is `P ∧ Q → Q ∧ P`. Use `intro ⟨hp, hq⟩` to introduce the
  conjunction and destruct it into its two parts at once."
  intro ⟨hp, hq⟩
  Hint "You now have `{hp} : P` and `{hq} : Q`, and the goal is `Q ∧ P`.
  Build the answer pair in the right order: `exact ⟨{hq}, {hp}⟩`."
  exact ⟨hq, hp⟩

Conclusion "
Under Curry-Howard, this proof **is** a program:
```
fun ⟨hp, hq⟩ => ⟨hq, hp⟩
```
It takes a pair `(hp, hq)` and swaps the components. The proof *is* the program.

In Lean 4, `P ∧ Q` is literally the structure `And P Q` with fields `left : P`
and `right : Q`. Constructing a proof of `P ∧ Q` *is* constructing a value of
that structure type. There is no gap between 'doing logic' and 'writing code'.
"

NewTactic obtain
