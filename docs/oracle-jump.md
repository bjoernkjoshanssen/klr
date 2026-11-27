# Oracle computation and finite jumps

The public entry point is [`Klr.Computability`](../Klr/Computability.lean).
It supplies the computability foundations for the completed effective
refinement of the separation construction. The fourth-jump bound for the
selected separating measure and the fifth-jump bound for a separating sequence
are now unconditional theorems in
[`EffectiveSeparation.lean`](../Klr/EffectiveSeparation.lean). The
[degree-bounds note](effective-degree-bounds.md) explains their construction.

## Oracle model

The definitions in [`Oracle.lean`](../Klr/Computability/Oracle.lean) use
Mathlib's `RecursiveIn`, `ComputableIn`, and Turing reducibility:

```lean
abbrev Oracle := ℕ → Bool
def oracleFunction (A : Oracle) : ℕ →. ℕ :=
  fun n => Part.some (bit (A n))
def Reduces (A B : Oracle) : Prop :=
  TuringReducible (oracleFunction A) (oracleFunction B)
```

Here `bit false = 0` and `bit true = 1`. The total characteristic function
is exposed to programs as a partial function with domain all natural numbers.
`zeroOracle` is the constantly false oracle. Computation relative to this
oracle is equivalent to ordinary partial recursive computation.

The total-function helpers `total_comp`, `total_pair`, `total_primrec`, and
`total_computable` work with any set of partial numerical oracles. They do not
introduce a separate notion of computability.

## Programs, finite oracle use, and the jump

[`OracleCode.lean`](../Klr/Computability/OracleCode.lean) gives syntax for
zero, successor, projections, oracle query, pairing, composition, primitive
recursion, and minimization. Its evaluator accepts an arbitrary partial oracle.

* `OracleCode.eval_recursiveIn` proves that evaluating a code is recursive in
  its oracle.
* `OracleCode.exists_code` proves the converse for every function in Mathlib's
  `Nat.RecursiveIn` relation with a singleton oracle set.
* `OracleCode.turingReducible_iff_exists_code` connects this interpreter to
  Mathlib's Turing reducibility.

[`OracleSimulation.lean`](../Klr/Computability/OracleSimulation.lean) proves
that finite oracle prefixes approximate each successful oracle computation.
Its `Approximates` relation records both soundness of all finite outputs and
eventual agreement with each actual output. Closure under minimization includes
the finitely many failed tests before the successful one.

An ordinary program can be run on a finite oracle prefix with a finite
evaluation bound. The function `OracleSimulation.run` implements this trial, and
`run_uniform_recursive` proves relative computability jointly in the program
index, input, and trial. This uniformity is needed for the halting jump.

[`OracleJump.lean`](../Klr/Computability/OracleJump.lean) defines `Halts A e n`
by the existence of a successful finite trial and defines `jump A` as the
characteristic function of this halting relation on coded pairs `(e,n)`.
`partial_table` proves that every `A`-partial-recursive function has a program
index with exactly its domain. In particular, `domain_recursive_jump` decides
the domain of any such function using `jump A`.

[`JumpProperties.lean`](../Klr/Computability/JumpProperties.lean) proves:

| Theorem | Content |
| --- | --- |
| `reduces_jump` | `Reduces A (jump A)` |
| `jump_not_reduces` | `¬ Reduces (jump A) A`, by a diagonal argument |
| `jump_mono` | A reduction from `A` to `B` induces a reduction of their jumps |
| `iterate_mono` | The same oracle monotonicity for every finite number of jumps |
| `iterate_le_iterate` | Increasing the number of jumps increases computational power |
| `zeroJump_succ_not_reduces` | Every successive jump above the empty oracle is strictly stronger |

`OracleJump.zeroJump n` denotes the `n`-fold jump of `zeroOracle`.
The fourth and fifth jumps are therefore actual halting-jump iterates, with
the expected strictness theorem, rather than abstract oracle parameters.

## The hierarchy-to-jump theorem

[`ArithmeticHierarchy.lean`](../Klr/Computability/ArithmeticHierarchy.lean)
defines a semantic relative arithmetical hierarchy. Level zero consists of
predicates whose characteristic functions are computable in the oracle.
Successor levels alternate existential and universal number quantifiers over
a coded pair. `Sigma A n P` and `Pi A n P` are the two polarities of `Form`.

The closure API includes negation, conjunction, disjunction, primitive
recursive substitution, raising the level, and same-polarity number
quantification at positive levels. `predicateOracle P` is the characteristic
set of a predicate, and `recursivePred_iff_reduces` connects relative
decidability with actual Turing reducibility.

The central upper-bound theorem is:

```lean
OracleJump.form_recursive
  (h : ArithmeticHierarchy.Form A n polarity P) :
  ArithmeticHierarchy.RecursivePred (OracleJump.iterate A n) P
```

Its set-reducibility form is `OracleJump.form_reduces`.
The proof handles one number quantifier with one halting jump and then
inducts on the hierarchy level. This is the upper-bound direction of Post's
theorem needed by the effective construction. A full characterization of
every hierarchy level by relative enumerability is not claimed here.

## Search does not require a new jump

[`RelativeSearch.lean`](../Klr/Computability/RelativeSearch.lean) works with a
bounded enumerator `E : ℕ → ℕ → Option ℕ`. The arguments are the problem input
and the finite search stage. Several different stages may return different
valid answers.

* `search_recursive` proves that partial search uses the enumerator's oracle.
* `search_dom` characterizes termination by the existence of some successful
  stage.
* `search_spec` and `search_sound` establish the returned answer's correctness.
* `exists_selector` gives a total selector when every input has an answer.

The first successful *stage* is selected. The selected answer need not be the
least semantic witness: deciding that a smaller witness never succeeds could
require an additional jump.

[`ArithmeticSelection.lean`](../Klr/Computability/ArithmeticSelection.lean)
also proves `exists_selector_of_sigma_one`: a uniformly relative Sigma-one
relation with a witness for every input has a selector computable in the same
oracle. The search ranges over a proposed witness together with the certificate
for its existential definition. `exists_computableIn_selector_of_sigma_one`
exports the result using Mathlib's `ComputableIn` notation.

The higher-level theorem `exists_selector_of_sigma_succ` proves that a total
relative Sigma-`(n+1)` relation has a selector computable in the `n`-fold jump.
It decides the inner Pi-`n` matrix using `form_recursive` and searches over the
outer existential certificate. This saves the jump that would be needed to
decide the whole relation before selecting its least semantic witness.
`least_recursive_of_form` provides that latter operation when a least witness
is specifically needed.

## Iterating a search on valid histories

[`OracleRecursion.lean`](../Klr/Computability/OracleRecursion.lean) proves
same-oracle primitive recursion and iteration. Its partial-transition theorem
`exists_computable_run` only requires termination along states satisfying a
preserved invariant.

[`StageSearch.lean`](../Klr/Computability/StageSearch.lean) combines this with
bounded witness search. `exists_computable_stage_run` assumes:

1. A bounded checker is uniformly computable in the oracle.
2. The initial history satisfies `Valid`.
3. From every valid history, some bounded stage produces an output.
4. Every output from a valid history is valid and satisfies the intended
   one-step relation.

It concludes that there is a total history sequence computable in the same
oracle, starting at the given history, satisfying `Valid` at every stage and
the one-step relation between consecutive stages. Neither `Valid` nor the
semantic one-step relation is assumed decidable. There is no termination
requirement on invalid histories.

The effective affine construction now instantiates this interface: finite
approximations certify strict probability inequalities, while the analytic
existence theorem, applied at half the requested error, proves that some
certified candidate is eventually found.

## Application to the degree bounds

All five application interfaces are now proved:

* [`UniformStrategyFamily`](../Klr/UniformStrategyFamily.lean) gives one actual
  uniformly effective family of total rational simulators covering every
  original strategy's success set. [`UniformNormalization`](../Klr/UniformNormalization.lean)
  computes the actual normalized wagers uniformly in the second jump.
* [`EffectiveFixedPartitions`](../Klr/EffectiveFixedPartitions.lean) supplies
  fourth-jump clopen approximations in measure to the same fixed Borel high
  sets that satisfy the ordinary computable-pool contract.
* [`EffectiveStageChecker`](../Klr/EffectiveStageChecker.lean) implements a
  bounded fourth-jump checker for all stage conditions and proves its
  soundness and completeness on valid finite histories.
* [`EffectiveConstruction`](../Klr/EffectiveConstruction.lean) instantiates
  same-oracle stage recursion. [`EffectiveBlockProduct`](../Klr/EffectiveBlockProduct.lean)
  uses an explicit support escape bound to compute exact rational cylinder
  masses from a finite prefix of the selected block codes.
* [`EffectiveKLSelection`](../Klr/EffectiveKLSelection.lean) proves the relative
  positive-closed-class selection argument for the actual KL definition. It
  extracts a KL-random support point in one jump above the cylinder oracle.
  Full-measure closed affine events force that point to fail the original
  short-description Martin-Löf test.

The earlier arbitrary existential choices alone did not establish these
bounds. The new construction makes effective selections using the existing
mathematical existence proofs. See the [degree-bounds note](effective-degree-bounds.md)
for the complete jump accounting and exact public theorem statements.

## Source and dependencies

The program, approximation, hierarchy, jump, and some search proofs are
adapted from [`bjoernkjoshanssen/tt-auto`](https://github.com/bjoernkjoshanssen/tt-auto),
commit `3190d8d1a78e709297423d1343f68395127be5de`, under its Apache-2.0 license.
Individual source files record the original module paths. The extraction
removes the degree-rigidity and set-model dependencies. Mathlib remains the
only external dependency, pinned to the version already used by `klr`.
