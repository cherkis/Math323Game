import Game.Metadata
import Game.Levels.S1_LeanAndLogic.L09

World "LeanAndLogic"
Level 10

Title "Contrapositive"

Introduction "
## Modus Tollens and the Contrapositive

In classical logic, `P → Q` and `¬Q → ¬P` are logically equivalent.
The equivalence is called the **contrapositive**. In natural language:
*\"If it is raining, the ground is wet\"* is equivalent to
*\"If the ground is not wet, it is not raining.\"*

The **constructive half** — `(P → Q) → (¬Q → ¬P)` — holds in intuitionistic
logic too, with no classical axioms. This is what we prove here.

The other direction, `(¬Q → ¬P) → (P → Q)`, requires classical logic. That
asymmetry is subtle: you can always *derive* the contrapositive from an
implication, but you cannot always *recover* the implication from its
contrapositive without LEM.

This pattern appears constantly in mathematics:
- In number theory: \"if n is prime and n > 2, then n is odd\" ↔ \"if n is even
  and n > 2, then n is not prime\"
- In analysis: convergent sequences are bounded ↔ unbounded sequences diverge

In this level, let:
- **P** = \"the proof is correct\"
- **Q** = \"the type checks\"

---

**Proof pattern:** Prove `¬P` (which is `P → False`) by assuming `P` and
deriving `False` — using the hypothesis `¬Q` and the derived fact `Q`.
"

/-- The constructive **contrapositive**: `(P → Q) → (¬Q → ¬P)`. -/
Statement contrapose_prop (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  Hint "Introduce all hypotheses: `intro hpq hnq hp`.
  You'll have the implication, the negation of Q, and an assumption of P."
  intro hpq hnq hp
  Hint "Now you have `{hpq} : P → Q`, `{hnq} : ¬Q`, and `{hp} : P`.
  Apply `{hpq}` to `{hp}` to get `Q`, then apply `{hnq}` to that.
  Write: `exact {hnq} ({hpq} {hp})`."
  exact hnq (hpq hp)

Conclusion "
The proof is a pure function composition: `hnq ∘ hpq` — first apply `hpq : P → Q`,
then apply `hnq : Q → False`. This gives `P → False`, which is `¬P`.

In Lean: `exact hnq (hpq hp)` or equivalently `exact Function.comp hnq hpq`.

**Why doesn't the other direction work constructively?**
To prove `(¬Q → ¬P) → (P → Q)` constructively, given `P`, you'd need to
produce `Q`. From `¬Q → ¬P` and `P`, you could derive `¬¬Q`. But getting
from `¬¬Q` to `Q` requires double negation elimination — that's LEM. We'll
see exactly this in Level 12.
"

