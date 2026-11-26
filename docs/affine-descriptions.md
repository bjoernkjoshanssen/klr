# Concrete affine descriptions and the Martin-Löf test

The description-budget argument has a concrete interpreter, finite
verifiers, and an actual Martin-Löf test. The completed stage construction
now supplies short descriptions of its selected block events: the program
reconstructs the pool and candidate, searches for the horizon, computes the
syndrome, and produces a verified exact affine code.

[`Separation.lean`](../Klr/Separation.lean) proves the unconditional separation
theorem for the repository's **total computable-real betting-strategy
convention**. No construction or description premise remains in that
theorem. A general partial computable-real strategy convention requires a
separate bridge. The [stage-construction note](stage-construction.md) explains
the complete assembly; this note documents its effective descriptions.

## Finite affine codes and exact event coverage

[AffineCode.lean](../Klr/AffineCode.lean) represents an affine system by ordinary
finite data: an ambient width, a row count, Boolean matrix rows, a Boolean
syndrome, and Boolean rows of a proposed right inverse. Missing entries are
zero. The interpreted equations are

$$
A(X\mathbin{\upharpoonright}M)=y
$$

over the field with two elements. The finite Boolean checker `AffineCode.valid`
checks $AR=I_r$. Its total computability is proved, and acceptance implies
actual surjectivity of the interpreted matrix. Consequently

$$
\operatorname{fairCoin}(\operatorname{AffineCode.event}(c))=2^{-r}
$$

for every verified code of row count $r$.

The representation covers all full-row-rank affine systems, not just systems
already presented with a special matrix form.
[AffineCodeCoverage.lean](../Klr/AffineCodeCoverage.lean) proves existence of a
right inverse by choosing preimages of the standard basis vectors. It also
proves `exists_valid_code_of_affineBlock`: every existing `AffineBlock` has a
verified code with the same rank and exactly the same Cantor-space event.
Unused positions below the largest support coordinate become zero columns.

[AffineCodePrefix.lean](../Klr/AffineCodePrefix.lean) supplies the total
computable prefix checker. A prefix must cover the ambient width and satisfy
all equations. `cylinderUnion_accepts` proves that the union of its accepted
cylinders is exactly the affine event.

## Rank checks and computed certificates

The affine-code verifier checks a supplied certificate. The candidate-list
construction also needs to recognize full rank before such a certificate has
been supplied. [SparseSearchRank.lean](../Klr/SparseSearchRank.lean) provides
that separate operation: `SparseSearch.fullRank` exhaustively checks the
finite matrix's surjectivity, and `fullRank_eq_true` proves its mathematical
meaning. [SparseSearchMask.lean](../Klr/SparseSearchMask.lean) provides
`maskedFullRank`, with correctness for the actual linear map restricted to
the columns selected by a Boolean mask.

[SparseSearchCertificate.lean](../Klr/SparseSearchCertificate.lean) then gives
an actual partial-recursive certificate search. Its `completeCode` operation
halts exactly when the input matrix has full row rank. Every output passes
`AffineCode.valid` and preserves the matrix, syndrome, rank, and event.

Thus a description program can compute and output the certificate. The
certificate's literal size need not be included in the program's binary
length. The completed stage uses `StageCodeSearch` and `StageCandidateCode`
to recover a verified code by exact finite truth-table comparison with the
selected candidate event. This also computes a valid certificate and proves
exact event and rank equality, without encoding a noncomputably chosen
matrix representation as advice.

## The plain binary interpreter and the test

[AffineDescription.lean](../Klr/AffineDescription.lean) interprets a finite
binary string as a natural number, unpairs that number into a program index
and a numerical input, and runs the corresponding actual
`Nat.Partrec.Code.eval`. A halting output decodes to the finite affine data
above. No separate assumed universal interpreter is used.

The constructor

```lean
AffineDescription.programFor e n =
  (Nat.pair (Encodable.encode e) n).bits
```

packages a fixed algorithm `e` with numerical input `n`. The exact evaluation
theorem is

```lean
run (programFor e n) = (e.eval n).map decodeOutput
```

For test level $n$, binary program $p$, and prefix $s$, the predicate
`AffineDescription.W (n,p,s)` says that the program halts with a code $c$,
the code passes the certificate verifier, its rank satisfies

$$
r\ge 2|p|+n+1,
$$

and its prefix checker accepts $s$. `rePred_W` proves uniform computable
enumerability of this predicate.

A program has at most one output. Its accepted cylinders therefore form
either the empty set or the single verified affine event, whose measure is
at most $2^{-(2|p|+n+1)}$. The existing exact plain-description budget is

$$
\sum_{p\in\{0,1\}^{<\omega}}2^{-(2|p|+n+1)}=2^{-n}.
$$

This counts all binary strings and needs no prefix-free condition. Countable
subadditivity gives the test-level bound. The definition
`AffineDescription.test : MartinLofTest` fixes an actual test code, and
`test_level` identifies its levels with this concrete description family.

`exists_program_of_affineBlock` proves that every block has some successfully
evaluated exact description. It deliberately asserts no length bound.

## What the program-length lemmas establish

[AffineProgramLength.lean](../Klr/AffineProgramLength.lean) proves exact binary
encoding bounds for this interpreter. Writing $\operatorname{size}(n)$ for
the binary length of a natural number,

$$
|\operatorname{programFor}(e,n)|
\le 2\max\bigl(\operatorname{size}(\operatorname{encode}(e)),
                 \operatorname{size}(n)\bigr).
$$

There is also an additive bound separating the fixed header and input sizes.
For every fixed algorithm $e$, exponent $k$, and test level $\ell$, the
theorem `eventually_programFor_bounded_pow_length_budget` proves that, for all
sufficiently large $r$, uniformly over $n\le r^k$,

$$
2|\operatorname{programFor}(e,n)|+\ell+1\le r.
$$

`eventually_programFor_pair_advice_length_budget` proves the corresponding
statement for input $\operatorname{pair}(r,q)$, uniformly over advice indices
$q\le r^k$. The proof uses elementary bounds on binary size and an explicit
eventual threshold. It does not require an optimality theorem for Mathlib's
syntactic program encoding.

The algorithm and polynomial exponent are fixed before taking the eventual
rank bound. The stage construction respects this order: one fixed program
works for all trial ranks and admissible advice values at the current stage.

[`StageProgramLength.lean`](../Klr/StageProgramLength.lean) specializes the
encoding estimates to the actual nested input

$$
\operatorname{pair}\bigl(r,\operatorname{pair}(q,b)\bigr),
\qquad q<r^{24},\quad b\le B,
$$

where $B$ is fixed before varying $r$. Its
`eventually_programFor_stage_budget` proves the required length/rank budget
uniformly over these $q,b$. `StagePrepared` intersects this eventual bound
with the eventual existence of good pools and candidates, after the program
header is already fixed.

## The effective sparse-list construction

[SparseListSearch.lean](../Klr/SparseListSearch.lean) specifies finite lists of
support masks and matrix codes. Its checker verifies list length, support
sizes, dimensions, full rank, zero padding outside the support, the point
incidence inequalities, and the restriction-rank inequality for every dense
Boolean mask. All counts are `List.countP` counts, so repeated entries have
their intended multiplicities. The thresholds are exact rationals.

`GoodEntry.maskedFullRank`, `GoodEntry.selectedColumns_card`, and
`GoodEntry.restricted_fullRank` prove that deleting the zero padding leaves
a genuine full-rank system on exactly the prescribed $m$ support columns.

[SparseListSearchComputable.lean](../Klr/SparseListSearchComputable.lean) proves
the entire checker computable. [SparseListSearchEffective.lean](../Klr/SparseListSearchEffective.lean)
implements exhaustive search over natural encodings of finite lists and
proves that it halts exactly when a good code exists. The finite existence
bridge and its specialization to
$M=r^8$, $m=r^2$, and $J=M^3$ are in
[SparseListCodeBridge.lean](../Klr/SparseListCodeBridge.lean) and
[SparseListConstruction.lean](../Klr/SparseListConstruction.lean). For fixed
positive rational density and error tolerance, the actual list-producing
partial-recursive computation eventually halts and returns a good list.

## The modular description obligation and its discharge

[AffineDescriptionSeparation.lean](../Klr/AffineDescriptionSeparation.lean)
proves `exists_separating_of_stage_estimates_and_affine_programs`. It assumes
an actual disjoint block sequence satisfying the stage estimates and, for
each test level, a successfully evaluated verified affine description with
the required length/rank inequality whose event contains a selected block
event. It concludes

$$
\exists X\;[\operatorname{KLR}(X)\land\neg\operatorname{MLR}(X)].
$$

The exact-event variant replaces containment by equality. This conditional
theorem remains a useful modular reduction. `StageConstruction.exists_sequence`
now supplies its estimates and exact description witnesses together.

The actual program is assembled in
[`StageReconstruction.lean`](../Klr/StageReconstruction.lean). The fixed header
contains the earlier affine codes, the finite protected strategy list, the
pool program, and rational parameters. Only $(r,q,b)$ varies. Evaluation
performs the following operations:

1. Run the fixed pool program at $M=r^8$.
2. Run the sparse-list constructor and retrieve candidate $q$.
3. Compute exact rational finite-horizon rank probabilities and search using
   the bounded integer advice $b$.
4. Minimize the finite rational objective over all $2^r$ syndromes.
5. Reconstruct a certified affine code for the selected event.

The horizon advice bounds the eventual total drop probability to within one
error interval. Its bound depends on the stage tolerance and protected scan
count, not on $r$. It supplies neither a convergence modulus nor a literal
syndrome. `StageFiniteScan` and `StageConditionalScan` compute the objective
under the actual affine conditions on raw input bits, using an all-branch
finite query bound. The adaptive answers are simulated inside this finite
calculation.

`StageSyndromeObjective.chosen_minimizes_integral` proves that the computed
word minimizes the actual conditional integral. The old-law average over
all syndromes gives the desired early-wager and partial-rank bound for the
minimizer. The first-drop tail estimate holds for every syndrome, so it is
preserved by this choice. This supplies the description argument that
existence of an arbitrary $r$-bit syndrome alone would not provide.

`StageOneStep` proves successful evaluation of this same program and its
shortness for the actual chosen block. `StageRecursion` obtains an exact
short program at every test level, and `Separation` concludes

```lean
Klr.exists_kolmogorovLovelandRandom_not_martinLofRandom
Klr.martinLofRandom_ssubset_kolmogorovLovelandRandom
```

with no stage or description hypothesis, for the total computable-real
strategy predicate specified above.
