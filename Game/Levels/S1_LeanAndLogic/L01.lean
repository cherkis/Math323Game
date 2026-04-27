import Game.Metadata

World "LeanAndLogic"
Level 1

Title "Your First Proof"

Introduction "
## Welcome to the Logic World

You are about to write your first formal proof in **Lean 4**, a proof assistant and
programming language created by **Leonardo de Moura** (Microsoft Research, now AWS).
Lean 4 was released in 2023 and is rapidly becoming a tool of choice for formalizing
mathematics — including recent formalizations of research-level results.

The tradition of machine-checked proof goes back to **Nicolaas Govert de Bruijn**
(1918–2012), a Dutch mathematician who built **AUTOMATH** in the late 1960s — the
first system to mechanically verify mathematical proofs. Lean is his intellectual
great-grandchild, via a lineage through Coq, Isabelle, and Agda.

---

Your first goal is the simplest possible: prove **True**.

In logic, `True` is a proposition that requires no assumptions — it is
unconditionally provable. In Lean, the tactic `trivial` closes any goal of
the form `True` immediately.

*Tip: click a tactic name in the right-hand inventory to read its documentation.*
"

/-- Prove that `True` is true. -/
Statement : True := by
  Hint "The tactic `trivial` closes goals of the form `True`. Try it!"
  trivial

Conclusion "
Well done on your first formal proof!

Under the hood, `True` is defined in Lean as an inductive type with a single
constructor: `True.intro : True`. The tactic `trivial` finds and applies it.

In the next level we introduce **propositions as variables** — the starting
point of propositional logic in Lean.
"

NewTactic trivial
