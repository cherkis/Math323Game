# Tactic Introduction Plan — Introduction to Proofs with Lean 4

This document is the tactic-focused companion to `CoursePlan.md`. Where `CoursePlan.md` records the mathematical content and dependency structure of each stage, this document records which new Lean proof tools each lecture introduces. Stages 1–9 reflect existing lecture files; Stages 10–11 are prospective.

---

## Coverage Status

| Stage | Lectures | Status | Topic |
|-------|----------|--------|-------|
| 1 | L01–L04 | Covered | Lean foundations and propositional logic |
| 2 | L05–L06 | Covered | Quantifiers and predicates |
| 3 | L07–L09 | Covered | Induction and arithmetic on `ℕ` |
| 4 | L10–L11 | Covered | Sets and the logic-set dictionary |
| 5 | L12–L13 | Covered | Relations, equivalence, and quotients |
| 6 | L14–L15 | Covered | Functions, image/preimage, inverses |
| 7 | L16–L19 | Covered | Cardinality |
| 8 | L20–L21 | Covered | Number systems and real-analysis tools |
| 9 | L22–L23 | Covered | Supremum and infimum |
| 10 | L24–L25 | Planned | Sequences and limits |
| 11 | L26–L27 | Planned | Topology of the real line |

---

## Stage 1 — Lean and Logic (L01–L04)

### L01 — Type theory, Lean syntax, term-mode proofs

| Tool | Role |
|------|------|
| `#check`, `#eval`, `#print` | Lean inspection commands |
| `def`, `theorem`, `lemma`, `example` | Declaration forms |
| `fun` / `λ` | Lambda abstraction; proofs as terms |
| `rfl` | Reflexivity and definitional equality |

### L02 — Implication, `False`, `True`; term mode vs. tactic mode

| Tool | Role |
|------|------|
| `intro` | Introduce hypotheses and universal variables |
| `exact` | Close a goal with a proof term |
| `apply` | Backward chaining from a lemma or hypothesis |
| `contradiction` | Close a goal from conflicting hypotheses |
| `exfalso` | Reduce the goal to `False` |

### L03 — Conjunction, equivalence, negation

| Tool | Role |
|------|------|
| `dsimp` | Definitional simplification |
| `constructor` | Split a conjunction or equivalence |
| `rintro` | Combined intro with immediate pattern matching |

### L04 — Disjunction, case splits, first rewrites

| Tool | Role |
|------|------|
| `left`, `right` | Choose a branch of a disjunction goal |
| `obtain` | Destructure a conjunction, disjunction, or existential |
| `rcases` | Pattern-match a hypothesis (preferred form for propositions) |
| `by_cases` | Classical case split on a proposition |
| `have` | Introduce an intermediate named claim |
| `rw` | Rewrite using an equality |

*Note: `rcases` is the preferred form over `cases` for propositional case analysis per the course style. `cases` is reserved for structural splits on inductive data (introduced in L07). `rintro` first appears in L03 but becomes heavily used here.*

---

## Stage 2 — Predicate Logic (L05–L06)

### L05 — Universal and existential quantifiers

| Tool | Role |
|------|------|
| `use` | Provide a witness for an existential goal |
| `linarith` | Close linear arithmetic goals over ordered types |

### L06 — Quantifiers with concrete examples (consolidation)

No new tactics. L06 consolidates quantifier tools in the context of even/odd predicates and arithmetic examples.

---

## Stage 3 — Induction (L07–L09)

### L07 — Peano axioms, custom inductive types, structural induction

| Tool | Role |
|------|------|
| `cases` | Case split on an inductive data type |
| `induction'` | Structured induction on `ℕ` and custom inductive types |

*Note: `rw` (introduced in L04) becomes central here for rewriting along definitional equalities on custom inductive types.*

### L08 — Sigma/Pi types, dependent types, library exploration

| Tool | Role |
|------|------|
| `ring` | Normalize ring/semiring expressions |
| `norm_num` | Prove concrete numerical statements |

*Note: L08 is a library-exploration lecture. `ring` and `norm_num` are encountered through MIL exercises and become standard toolkit from this point on.*

### L09 — Summation formulas, multi-step arithmetic proofs

| Tool | Role |
|------|------|
| `congrArg` | Apply a function to both sides of an equality |
| `calc` | Multi-step structured equality/inequality chains |

---

## Stage 4 — Sets (L10–L11)

### L10 — Sets as predicates, membership, operations, extensionality

| Tool | Role |
|------|------|
| `ext` | Prove set equality by pointwise membership |
| `show` | State the current goal explicitly |
| `change` | Replace the goal with a definitionally equal statement |
| `suffices` | Reduce the goal to a sufficient subgoal |
| `simp only` | Controlled simplification with a named lemma list |
| `tauto` | Close pure propositional goals |

*Note: `have` (introduced in L04) becomes central here for multi-step set proofs. `norm_num` (introduced in L08) handles concrete membership goals like `3 ∈ {n | n > 2}`.*

### L11 — Indexed families, power set, De Morgan's laws

| Tool | Role |
|------|------|
| `push_neg` | Push negation through quantifiers and logical connectives |

---

## Stage 5 — Relations and Quotients (L12–L13)

### L12 — Binary relations, equivalence relations, modular arithmetic

| Tool | Role |
|------|------|
| `unfold` | Expand a named definition in the goal or hypothesis |
| `omega` | Linear arithmetic over `ℕ` and `ℤ` |
| `trans` | Apply transitivity directly |

### L13 — Quotient types, well-definedness, residue classes

| Tool | Role |
|------|------|
| `Quotient.mk` / `⟦_⟧` | Construct an equivalence class |
| `Quotient.sound` | Prove equal classes from the underlying relation |
| `Quotient.exact` | Recover the relation from equal classes |
| `Quotient.lift` | Define a function on a quotient (well-definedness check) |
| `Quotient.lift₂` | Lift a binary function to a quotient |
| `Quotient.ind` | Prove properties by working with representatives |
| `rename_i` | Rename anonymous inaccessible hypotheses |
| `congr` | Congruence — transport equalities through constructors |

---

## Stage 6 — Functions (L14–L15)

### L14 — Injections, surjections, bijections, composition

| Tool | Role |
|------|------|
| `funext` | Prove function equality by pointwise equality |

### L15 — Image, preimage, inverses, axiom of choice

| Tool | Role |
|------|------|
| `choose` | Extract a choice function from a family of existentials |
| `aesop` | Lightweight goal automation for routine goals |
| `exact?` | Search for a closing lemma interactively |

---

## Stage 7 — Cardinality (L16–L19)

### L16 — Countability, bijections `ℕ ↔ ℤ`, Cantor's diagonal argument

No new tactics (consolidation lecture). `native_decide` was listed for this lecture in the original plan but does not appear in the current L16.lean.

*Suggested future addition: introduce `native_decide` here for verifying small decidable cardinality examples by computation.*

### L17 — Schröder–Bernstein theorem

| Tool | Role |
|------|------|
| `refine` | Build a structured proof with named placeholder holes |

*Note: `by_contra` appears in L17's recall list and is used here, but it is not a new introduction at this stage.*

### L18 — Classical witness extraction, unique existence

| Tool | Role |
|------|------|
| `Classical.choose` | Extract a witness from a classical existence proof |
| `Classical.choose_spec` | Recover the property of the chosen witness |
| `noncomputable` | Mark definitions that use classical choice |
| `∃!` | State and prove unique existence |
| `abbrev` | Transparent definition (vs. opaque `def`) |
| `local notation` | Section-scoped notational shortcuts |

### L19 — Line-equals-plane: interleaving bijection

| Tool | Role |
|------|------|
| `<;>` | Broadcast a tactic to all open goals simultaneously |
| `congr_arg` | Apply a function to both sides of an equality (term-level) |
| `pick_goal` | Select a specific numbered goal (useful in 4-case splits) |
| `nlinarith` | Nonlinear arithmetic (products, powers) |

*Note: `nlinarith` first appears in the pairing-function argument here and becomes more central in Stage 8.*

---

## Stage 8 — Number Systems (L20–L21)

### L20 — `ℕ → ℤ → ℚ → ℝ`, field structure, coercions

| Tool | Role |
|------|------|
| `field_simp` | Clear denominators in field expressions |
| `positivity` | Prove nonnegativity or strict positivity goals |
| `push_cast` | Normalize coercions between number systems |
| `exact_mod_cast` | Transfer equalities/inequalities across type coercions |
| `gcongr` | Monotone inequality transport (`≤` congr) |

### L21 — Archimedean property, floor function, density of `ℚ` and irrationals

| Tool | Role |
|------|------|
| `Int.floor_le`, `Int.lt_floor_add_one` | Floor function properties |

---

## Stage 9 — Supremum and Infimum (L22–L23)

### L22 — Supremum, completeness of `ℝ`, approximation property

| Tool | Role |
|------|------|
| `Set.Icc`, `Set.Ioo` | Closed and open interval notation |
| `BddAbove`, `upperBounds` | Boundedness predicates |
| `IsLUB` | Least upper bound predicate |
| `le_csSup`, `csSup_le` | Two-directional supremum API |
| `le_antisymm` (as dominant pattern) | Equality from `≤` in both directions |

### L23 — Infimum, separation theorem, nested intervals

| Tool | Role |
|------|------|
| `BddBelow`, `lowerBounds` | Boundedness predicates (mirror of L22) |
| `IsGLB` | Greatest lower bound predicate |
| `csInf_le`, `le_csInf` | Two-directional infimum API |

---

## Stage 10 — Sequences and Limits (Planned, tentatively L24–L25)

### L24 — Epsilon-N definition of limits (proposed)

| Tool | Role |
|------|------|
| `specialize` | Instantiate a universally quantified hypothesis at a specific value |
| `use max N₁ N₂` pattern | Combine two Archimedean indices for a joint bound |
| `abs_sub_comm`, `abs_le` | Absolute value API for ε-N estimates |

### L25 — Monotone sequences, Cauchy sequences (proposed)

| Tool | Role |
|------|------|
| `Filter.Tendsto` | Mathlib's convergence predicate (metric-space formulation) |

*Pedagogical note: The ε-N pattern `∀ ε > 0, ∃ N, ∀ n ≥ N, ...` is structurally new even though individual tactics (`linarith`, `use`, `obtain`) are already known. `specialize` and the `use max N₁ N₂` witness combination are the key new proof moves.*

---

## Stage 11 — Topology of the Real Line (Planned, tentatively L26–L27)

### L26 — Open and closed sets, interiors and closures (proposed)

| Tool | Role |
|------|------|
| `IsOpen`, `IsClosed`, `closure` | Core topological predicates |
| `Metric.ball` | Ball neighborhoods in metric spaces |

### L27 — Compactness, continuity, Heine-Borel (proposed)

| Tool | Role |
|------|------|
| `Continuous` | Continuity predicate |
| `IsCompact` | Compactness predicate (Heine-Borel context) |
| `Filter.Eventually` | Filter-based quantification (generalizes ε-N) |

*Pedagogical note: At this stage, library navigation (`exact?`, `apply?`, `simp` with topological lemmas) becomes more important than new tactic primitives.*

---

## Master Tactic Index

### Group 0 — Inspection and declaration tools

| Tool | Stage | Lecture |
|------|-------|---------|
| `#check`, `#eval`, `#print` | 1 | L01 |
| `abbrev` | 7 | L18 |
| `def`, `theorem`, `lemma`, `example` | 1 | L01 |
| `exact?` | 6 | L15 |
| `fun` / `λ` | 1 | L01 |
| `local notation` | 7 | L18 |
| `noncomputable` | 7 | L18 |

### Group 1 — Structural and propositional tactics

| Tool | Stage | Lecture |
|------|-------|---------|
| `apply` | 1 | L02 |
| `by_cases` | 1 | L04 |
| `by_contra` | 1 | L04 (first use); becomes central in L17 |
| `calc` | 3 | L09 |
| `cases` | 3 | L07 |
| `change` | 4 | L10 |
| `choose` | 6 | L15 |
| `Classical.choose` | 7 | L18 |
| `Classical.choose_spec` | 7 | L18 |
| `congr` | 5 | L13 |
| `congr_arg` / `congrArg` | 3 / 7 | L09 / L19 |
| `constructor` | 1 | L03 |
| `contradiction` | 1 | L02 |
| `dsimp` | 1 | L03 |
| `exact` | 1 | L02 |
| `exfalso` | 1 | L02 |
| `ext` | 4 | L10 |
| `funext` | 6 | L14 |
| `have` | 1 | L04 |
| `induction'` | 3 | L07 |
| `intro` | 1 | L02 |
| `left`, `right` | 1 | L04 |
| `obtain` | 1 | L04 |
| `pick_goal` | 7 | L19 |
| `push_neg` | 4 | L11 |
| `rcases` | 1 | L04 |
| `refine` | 7 | L17 |
| `rename_i` | 5 | L13 |
| `rintro` | 1 | L03 |
| `rfl` | 1 | L01 |
| `rw` | 1 | L04 |
| `show` | 4 | L10 |
| `suffices` | 4 | L10 |
| `tauto` | 4 | L10 |
| `trans` | 5 | L12 |
| `unfold` | 5 | L12 |
| `use` | 2 | L05 |
| `<;>` combinator | 7 | L19 |
| `∃!` | 7 | L18 |

### Group 2 — Automation and arithmetic solvers

| Tool | Stage | Lecture |
|------|-------|---------|
| `aesop` | 6 | L15 |
| `exact_mod_cast` | 8 | L20 |
| `field_simp` | 8 | L20 |
| `gcongr` | 8 | L20 |
| `Int.floor_le`, `Int.lt_floor_add_one` | 8 | L21 |
| `linarith` | 2 | L05 |
| `nlinarith` | 7 | L19 |
| `norm_num` | 3 | L08 |
| `omega` | 5 | L12 |
| `positivity` | 8 | L20 |
| `push_cast` | 8 | L20 |
| `ring` | 3 | L08 |
| `simp only` | 4 | L10 |

### Group 3 — Quotient API

| Tool | Stage | Lecture |
|------|-------|---------|
| `Quotient.exact` | 5 | L13 |
| `Quotient.ind` | 5 | L13 |
| `Quotient.lift` | 5 | L13 |
| `Quotient.lift₂` | 5 | L13 |
| `Quotient.mk` | 5 | L13 |
| `Quotient.sound` | 5 | L13 |

### Group 4 — Sup/Inf and order API

| Tool | Stage | Lecture |
|------|-------|---------|
| `BddAbove`, `upperBounds` | 9 | L22 |
| `BddBelow`, `lowerBounds` | 9 | L23 |
| `csInf_le`, `le_csInf` | 9 | L23 |
| `csSup_le`, `le_csSup` | 9 | L22 |
| `IsGLB` | 9 | L23 |
| `IsLUB` | 9 | L22 |
| `le_antisymm` (dominant pattern) | 9 | L22 |
| `Set.Icc`, `Set.Ioo` | 9 | L22 |
