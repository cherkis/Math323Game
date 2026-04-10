# Collection of Exercises for Math 323

This document exists to aggregate the problems assigned in
Jason Aubrey and Daniel Madden's
*An Introduction to Proof through Real Analysis*, specifically
the exercises which are most thematic of the sections in which they
were assigned. These exercises are meant to be included in
the Lean4 Math323Game, so they are augmented and/or reordered
to fit into the structure of the Math323Game.

There are also some exercises in this document which are lifted
from the Spring 2026 Math496T course, as well as a few exercises which are wholly original.

## Stage 1 - Lean and Logic

- $P\wedge Q\implies R$ is equivalent to $P\implies(Q\implies R)$

- $(P \implies Q)\implies (\neg Q \implies \neg P)$

---

## Stage 2 - Predicate Logic

- Given a predicate $P:X\to Y\to\mathrm{Prop}$, compare
    - $\forall x,\exists y,\; P x y$
    - $\exists x,\forall y,\; P x y$
    - $\forall y,\exists x,\; P x y$
    - $\exists y,\forall x,\; P x y$
---

## Stage 3 - Induction

- $\displaystyle \forall n\ge0,\quad2\sum_{k=0}^n \;k = n^2+n$

- $\forall n \in\mathbb N,\quad n^2 \ge n$

---

## Stage 4 - Sets

- For $A$ a set and $\{B_i \;\big|\; i\in I\}$ and indexed family
of sets, prove that
$A\cup(\bigcap_{i\in I}B_i) = \bigcap_{i\in I}(A\cup B_i)$

---

## Stage 5 - Relations

- Show that for each positive integer $m$, the relation defined by
$a\simeq b\iff m\mid a-b$ is an equivalence relation.





---

## Stage 6 - Functions

- Given a function $f : A \to B$, consider the
following relations on $A$ and $B$, and determine whether or not each relation is an equivalence relation.
  - For $a, a'\in A$, say that $a\sim a'$ if $f(a) = f(a')$.
  - For $b, b'\in B$, say that $b\sim b'$ if
    $f^{-1}(\{b\})\subseteq f^{-1}(\{b'\})$

- Show that a function has a left-inverse under composition iff
the function is injective

- Show that a function has a right-inverse under composition iff
the function is surjective

---

## Stage 7 - Cardinality

- Show that every finite subset of $\N$ is bounded above
-- Sergey: Note, this has a constructive proof without using induction.
--      define injective $$f : S \to S, n \mapsto \min\ \{m \in S \ :\ m > n\}$$

- Let $\mathcal P(\N)$ be the collection of all subsets of $\N$. For
$S, T \in P(\N)$, say that $S\sim T$ if there are functions $f: S\to T$ and $g:T\to S$ such that $f\circ g = \mathrm{id}_T$ and
$g\circ f = \mathrm{id}_S$.
  - Show that $\sim$ is an equivalence relation on $\mathcal P(\N)$
  - Let $X = \frac{\mathcal P(\N)}\sim$. Show that X is infinite.
  (Hint: Construct an injection $\N\hookrightarrow X$)

---

## Stage 8 - Number Systems

- Prove that there is some $S\subsetneq\mathbb Z$ such that $S$
is nonempty but has no minimal element

- Prove that in every field $F$, for every $x\in F$, $x\cdot 0 = 0$

- Prove that for every prime number $p$, there is no rational
number $x$ such that $x^2 = p$

- Prove that $\forall x\in\R, \exist n \in\N$ such that $x < n$

- Suppose we try defining a new kind of addition on $\mathbb Q$:
$\frac a b \oplus \frac c d = \frac{a+c}{b+d}$. Prove that this is NOT well-defined.

---

## Stage 9 - Supremum and Infimum

- Prove that the supremum of a set is unique, if it exists

- Prove that $\mathrm{inf}\{\frac 1 n\; \big|\; n \in\N\} = 0$

- For a function $f : X \to \R$, we say that $f$ is bounded above if $\exists M \in \R,\forall x\in X, f(x)\le M$. For such a function $f$, define $\sup f = \sup \{f(x)\;\big|\;x \in X\}$. Let $f, g : X \to \R$ be bounded above.
  - Prove that $f+g : X \to \R$ by $x\mapsto f(x) + g(x)$ is also bounded above.
  - Prove that $\sup(f+g)\le\sup f + \sup g$.

---

## Stage 10 - Sequences and Limits

- Show that $\lim_{n\to\infty}\frac{n}{n+1} = 1$

- Consider the sequence defined by $a_n = (-1)^n$.
  - Find $\limsup a_n$
  - Find $\liminf a_n$
  - Prove either that $\lim a_n$ does or does not exist.

---

## Stage 11 - Topology

- Show that the infimum of a subset $A$ of $\R$, if it exists, is the
minimum of $\overline A$, the closure of $A$ in $\R$.
