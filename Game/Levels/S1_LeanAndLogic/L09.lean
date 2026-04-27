import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L08

World "LeanAndLogic"
Level 9

Title "Double Negation Introduction"

Introduction "
## Negation in Constructive Logic

In Lean (and in intuitionistic logic generally), **negation is defined by**:
```
¬P  :=  P → False
```
That is, `¬P` is not a primitive — it is *notation* for the type of functions
that take a proof of `P` and produce a proof of `False`. A proof of `¬P` is
a refutation of P.

`False` is an inductive type with **no constructors** — there is no way to
construct a value of type `False` directly. The only way to prove `False` is
to derive a contradiction from your hypotheses.

This is the **BHK interpretation** of negation: a proof of `¬P` is a method
for deriving a contradiction from any proof of `P`.

In this level, let:
- **P** = \"This proof is constructively valid\"

The theorem `P → ¬¬P` is **double negation introduction**: if you have a
proof of P, you can produce a proof of `¬¬P` (i.e., a function that takes
a proof of `¬P` and derives `False`).

---

**New tactic: `contradiction`.**
If you have both `h : P` and `hn : ¬P` (i.e., `hn : P → False`) in context,
then `contradiction` closes the goal by applying `hn` to `h`.
"

/-- Double negation introduction: **P implies not-not-P**. -/
Statement dni (P : Prop) : P → ¬¬P := by
  Hint "Introduce `hp : P` first. Then remember that `¬¬P` means `¬P → False`,
  so introduce `hnp : ¬P` next: `intro hp hnp`."
  intro hp hnp
  Hint "You have `{hp} : P` and `{hnp} : ¬P`, which is `{hnp} : P → False`.
  Use `contradiction` to close the goal — it finds the contradiction automatically.
  Alternatively, `exact {hnp} {hp}` applies the function `{hnp}` to `{hp}`."
  contradiction

Conclusion "
The proof is: *\"Given P, assume ¬P; but ¬P means P → False; apply it to P
to get False.\"* This is a valid *constructive* proof — no classical axioms needed.

**The crucial asymmetry:** We can constructively prove `P → ¬¬P`, but NOT `¬¬P → P`.
The reverse direction requires the **law of excluded middle** (LEM), which
intuitionistic logic rejects. Brouwer's objection: `¬¬P` says \"it is impossible
that P is false\", but that doesn't mean you can *construct* a proof of P.

We'll prove `¬¬P → P` in Level 12 — using classical reasoning.

**Branch: term-mode proof**
```
fun hp hnp => hnp hp
```
Since `¬¬P = (P → False) → False`, this is just applying `hnp : P → False`
to `hp : P`. No tactics needed — it's a pure λ-abstraction.
"

NewTactic contradiction
