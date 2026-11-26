# Concrete affine descriptions and the Martin-Löf test

The description-budget argument now has a concrete interpreter, finite
verifiers, and an actual Martin-Löf test. The final separation theorem still
requires the paper's stage construction and short descriptions of the
particular block events that construction selects. Those requirements are
explicit hypotheses, rather than assumptions about an unspecified decoder.

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
length. This is an effectiveness statement; it does not itself construct the
program for the paper's chosen stage.

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
rank bound. These results therefore become useful once a single reconstruction
algorithm, with the required bound on its numerical input or advice, has
been supplied.

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

## The remaining separation obligation

[AffineDescriptionSeparation.lean](../Klr/AffineDescriptionSeparation.lean)
proves `exists_separating_of_stage_estimates_and_affine_programs`. It assumes
an actual disjoint block sequence satisfying the stage estimates and, for
each test level, a successfully evaluated verified affine description with
the required length/rank inequality whose event contains a selected block
event. It concludes

$$
\exists X\;[\operatorname{KLR}(X)\land\neg\operatorname{MLR}(X)].
$$

The exact-event variant replaces containment by equality. Uniform
enumerability, interpreter correctness, and description measure budgets are
already discharged by the concrete development.

What remains is the simultaneous stage construction: selecting blocks with
the stated estimates and reconstructing the selected affine system,
including its coordinates and syndrome, from a fixed algorithm and
sufficiently short input. The polynomial-advice theorem does not show that
the paper's actual choices have polynomially bounded advice. In particular,
the existence of an arbitrary $r$-bit syndrome does not supply its short
description; the construction must compute the chosen syndrome or otherwise
justify its description cost. The repository does not yet prove the
unconditional separation theorem.
