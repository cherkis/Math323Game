import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L01

World "LeanAndLogic"
Level 2

Title "Weakening: P implies P or Q"

Introduction "
## Per Martin-Löf and Propositions-as-Types

**Per Martin-Löf** (born 1942) is a Swedish logician and philosopher who developed
**Martin-Löf Type Theory** (MLTT) in the 1970s — the foundational theory on which
Lean is built. He holds appointments in both mathematics *and* philosophy at
Stockholm University, which is fitting: MLTT blurs the line between the two.

In this level, let:
- **P** = \"Martin-Löf is a logician\"
- **Q** = \"Martin-Löf is a philosopher\"

(Both happen to be true, but in formal logic we work from *assumptions*, not
from facts about the world.)

The theorem `P → P ∨ Q` is called **weakening**: knowing P is enough to assert
'P or Q', since the left branch of the disjunction is already satisfied.

---

**New tactics this level:**
- `intro h` — introduces a hypothesis `h : P` into the context, changing the
  goal from `P → ...` to `...`
- `left` — when the goal is `P ∨ Q`, commits to proving the *left* branch `P`
- `right` — commits to the *right* branch `Q`
- `exact h` — closes the goal when it matches hypothesis `h` exactly
"

/-- If **P** holds, then **P or Q** holds (for any Q whatsoever). -/
Statement weaken_or (P Q : Prop) : P → P ∨ Q := by
  Hint "The goal is `P → P ∨ Q`. Use `intro hp` to bring the assumption `P`
  into your context as a hypothesis named `hp`."
  intro hp
  Hint "Now the goal is `P ∨ Q` and you have `{hp} : P`. Since you can prove
  the left branch, use `left` to commit to it."
  left
  Hint "The goal is now `P`, and you have `{hp} : P` in context.
  Use `exact {hp}` to close the goal."
  exact hp

Conclusion "
You just proved **weakening for disjunction**: knowing P lets you assert 'P or Q'.

Notice: you *chose* `left`. Under the **BHK interpretation**
(Brouwer–Heyting–Kolmogorov), a proof of `P ∨ Q` must be either:
- a proof of P tagged with 'left', or
- a proof of Q tagged with 'right'.

This is *constructive* disjunction. In classical logic, `P ∨ ¬P` holds for any
P without knowing which side — we'll meet that contrast in Level 12.
"

NewTactic intro exact left right
