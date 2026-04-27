import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L03

World "LeanAndLogic"
Level 4

Title "Disjunction is Symmetric"

Introduction "
## Brouwer and Intuitionism

**L.E.J. Brouwer** (1881–1966) was a Dutch mathematician famous for two things:
foundational contributions to topology (fixed-point theorems, dimension theory),
and founding **intuitionism** — the philosophy of mathematics that insists a
mathematical object exists only if you can *construct* it.

Brouwer rejected the **law of excluded middle** (`P ∨ ¬P`) as an axiom, because
for infinite domains you cannot always decide which branch holds. His student
**Arend Heyting** later formalized intuitionistic logic.

In this level, let:
- **P** = \"Brouwer was primarily a topologist\"
- **Q** = \"Brouwer was primarily a logician\"

The theorem `P ∨ Q → Q ∨ P` says disjunction is symmetric.

---

**New tactic this level:**
- `rintro (hp | hq)` — a powerful combination of `intro` and case-splitting on
  a disjunction. If the goal is `P ∨ Q → ...`, this introduces the disjunction
  and immediately creates *two goals*: one where `hp : P`, one where `hq : Q`.

This mirrors the BHK interpretation: to use a proof of `P ∨ Q`, you must handle
*both* cases.
"

/-- Disjunction is symmetric: if **P or Q**, then **Q or P**. -/
Statement or_symm (P Q : Prop) : P ∨ Q → Q ∨ P := by
  Hint "Use `rintro (hp | hq)` to introduce the disjunction and split into two cases."
  rintro (hp | hq)
  · Hint "In this branch you have `{hp} : P` and must prove `Q ∨ P`.
    Since you have P, use `right` then `exact {hp}`."
    right
    exact hp
  · Hint "In this branch you have `{hq} : Q` and must prove `Q ∨ P`.
    Since you have Q, use `left` then `exact {hq}`."
    left
    exact hq

Conclusion "
You handled *both* cases. This is case analysis — the fundamental proof technique
for disjunctions.

An equivalent proof using `rcases` instead of `rintro`:
```
intro h
rcases h with hp | hq
· right; exact hp
· left; exact hq
```
`rintro` just fuses `intro` and `rcases` into a single step.

**Historical note:** Brouwer was actually *both* a topologist and a logician —
the historical question was which he considered primary. He reportedly regarded
his logical work as the more important contribution, though his topological
theorems are what most mathematicians know him for today.
"

NewTactic rintro rcases
