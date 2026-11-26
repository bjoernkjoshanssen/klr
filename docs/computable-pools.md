# Fixed Borel partitions and computable pools

The pool lemma is implemented by
[`PoolConstruction.exists_fixed_partitions_computable_pools`](../Klr/PoolConstruction.lean).
It constructs the fixed Borel partitions, proves the existence of ordinary
finite advice, and proves eventual termination and correctness of an actual
partial-recursive pool-producing program. Mathlib is the only external
library dependency.

This establishes Lemma 3. The simultaneous affine-block construction and its
short reconstruction programs remain to be proved before the repository can
conclude that KL randomness differs from Martin-Löf randomness.

## The checked statement and its quantifiers

Let $(\pi_i)_{i\in\mathbb N}$ be any countable family of total computable scan
rules. No effective enumeration of the family is required. There are Borel
sets $H_i$, with $L_i=H_i^c$, such that the following holds.

For every finite protected prefix $i<\ell$, positive real error $\eta$, and
position cutoff $z$, there are a rational $0<\tau<1/4$ and one program $e$.
For every sufficiently large integer $M$, the program on input $M$ halts
with a list $G$ of exactly $M$ distinct positions, all at least $z$, and
for every $i<\ell$,

$$
\kappa\{Z\in H_i:\pi_i\text{ misses a position of }G\}<\eta,
$$

$$
\kappa\{Z\in L_i:
  \#\{a\in G:\pi_i\text{ never queries }a\}<\tau M\}<\eta.
$$

Here the probability space is **prescribed answer space**. On an answer
sequence $Z$, the query at time $t$ is $\pi_i(Z\upharpoonright t)$. It is
not the adaptive input-space transcript obtained by running the scan on $Z$
as an input. [`PoolQuery`](../Klr/PoolQuery.lean) makes this distinction
explicit in the definition of `queryAt`.

The order of the choices is

$$
\forall (\pi_i)\ \exists (H_i)\quad
\forall\ell,\eta>0,z\ \exists\tau,e\quad
\forall^{\infty}M\ \exists G.
$$

The notation $\forall^{\infty}M$ means all sufficiently large $M$; Lean uses
`∀ᶠ M in Filter.atTop`. Both the rational margin and the program precede
this varying input. The program returns an ordinary natural-number encoding
of a finite list, using `PoolAdvice.encodePool`. Its successful evaluation
is stated with actual membership in `Nat.Partrec.Code.eval`.

`GoodPool` is the complete output specification: length, absence of repeated
positions, position cutoff, and the two actual measure inequalities. The
intermediate `goodPool_of_mem` theorem proves correctness of **every** output
of the fixed search. The specially selected analytic pools serve to prove
halting; the algorithm need not return those particular pools.

## Choosing the partitions once

For a scan and a position, define

$$
g_{i,a}(Z)=\mathbf 1\{\pi_i\text{ ever queries }a\text{ on answers }Z\}.
$$

These are measurable functions taking values in $\{0,1\}$. The zero-based
weight convention is $w_i=2^{-(i+1)}$, corresponding to the paper's
positive-index weights. Thus $\sum_iw_i=1$. Define

$$
p(a)=\sum_iw_i\int g_{i,a}\,d\kappa,
\qquad p^*=\limsup_{a\to\infty}p(a).
$$

[`PoolWeighted`](../Klr/PoolWeighted.lean) proves convergence of this series,
the bounds $0\le p(a)\le1$, the uniform geometric truncation bound, and the
existence of positions tending to infinity along which $p(a)$ tends to
$p^*$. It also proves that, for any $s>0$, eventually every position satisfies
$p(a)<p^*+s$.

[`PoolWeakLimit`](../Klr/PoolWeakLimit.lean) obtains one common weakly
convergent subsequence for all the sequences $g_{i,a}$. Its proof uses the
compact metrizable weak-dual unit ball, a countable product, and Hilbert-space
Riesz representation. These are Mathlib theorems; weak compactness is not
assumed as a project axiom. The common extraction preserves the previously
arranged scalar convergence to $p^*$.

Testing weak convergence against indicators of measurable sets proves
convergence of set integrals. It also proves that the limiting $L^2$ classes
have values in $[0,1]$ almost everywhere. An $L^2$ class is not itself a
specified pointwise function, so
[`PoolPartitionRepresentative`](../Klr/PoolPartitionRepresentative.lean)
chooses a measurable representative and clips it to $[0,1]$. The clipping
changes it only on a null set. Write the resulting Borel function as $g_i$,
and put

$$
H_i=\{Z:g_i(Z)=1\},\qquad L_i=\{Z:g_i(Z)<1\}.
$$

[`PoolPartitionQuery`](../Klr/PoolPartitionQuery.lean) applies these results
to the actual query events and proves both properties needed later:

- The mass of $H_i$ missing the current position tends to zero along the
  common subsequence.
- On $L_i$, the mass where $g_i$ is arbitrarily close to one tends to zero.
  One positive rational margin can be chosen for any finite protected prefix.

This is an alternative to formalizing the paper's cylinder-martingale
construction of the weak limits. It yields the same partition properties.

## The fixed finite advice

The analytic choices need not be computable. The program receives only
finite constants chosen from them, once for the specified $\ell,\eta,z$.

[`PoolApproximation`](../Klr/PoolApproximation.lean) proves that every Borel
set can be approximated in symmetric-difference measure by a Boolean table
on a finite prefix. [`PoolApproximationFunction`](../Klr/PoolApproximationFunction.lean)
proves density in $L^1$ of rational finite-prefix tables; a $[0,1]$-valued
target has approximating tables with entries in $[0,1]$. It also chooses one
common depth for a finite family of both kinds of approximation.

[`PoolAdviceTables`](../Klr/PoolAdviceTables.lean) encodes these arbitrary
finite tables as ordinary finite lists. The resulting `Advice` contains a
position cutoff, a protected scan count, a common prefix depth, rational
error and acceptance thresholds, and the finite Boolean/rational tables.
The finite list of actual scan rules is fixed alongside that record.

[`PoolParameters`](../Klr/PoolParameters.lean) proves that the choices can be
made with all the required bounds. With $\delta>0$ the rational approximation
error and $s=2^{-\ell}\delta$, it chooses

$$
4\delta<\eta,\qquad
\frac\eta3+\frac{8\delta}{\tau}<\eta,
\qquad p^*-3s<\gamma<p^*-2s,
$$

and a finite scan count $D\ge\ell$ satisfying $2^{-D}<s/4$. It chooses a
cutoff $z'\ge z$ beyond which $p(a)<p^*+s$, and tables $H'_i,\psi_i$ with

$$
\kappa(H_i\mathbin\triangle H'_i)<\delta,
\qquad \|\psi_i-g_i\|_1<\delta.
$$

All these choices precede $M$. There is no assertion that they can be chosen
uniformly effectively from the original scan family and the real tolerance.

## What the program computes

For each requested size $M$, the program searches through codes for pairs
$(G,V)$, with a finite list of positions and a finite horizon. It first checks
that the list has length $M$, no repetitions, and no position below $z'$.
Let $v_{i,V}$ be the fraction of $G$ queried before $V$. It then checks

$$
\kappa\{Z\in H'_i:v_{i,V}(Z)<1\}<3\delta\quad(i<\ell),
$$

$$
\|v_{i,V}-\psi_i\|_1<3\delta\quad(i<\ell),
$$

$$
\sum_{i<D}w_i\int v_{i,V}\,d\kappa>\gamma.
$$

Every quantity is computed exactly as a rational average over all words of
length $\max(V,d)$, where $d$ is the common advice depth.
[`PoolAdviceMeasure`](../Klr/PoolAdviceMeasure.lean) proves that these
rational averages equal the actual measures and integrals.

[`PoolAdviceComputable`](../Klr/PoolAdviceComputable.lean) proves total
computability of the finite verifier. In particular, it proves that a fixed
finite list of actual total computable scans has a computable query
dispatcher. It does not require deciding which arbitrary program codes are
total. [`PoolSearch`](../Klr/PoolSearch.lean) implements the exhaustive search
with `Nat.rfindOpt`, proves its partial recursiveness, and extracts an
ordinary `Nat.Partrec.Code`. Halting is proved equivalent to the existence
of a pair passing that exact verifier.

## Why the search eventually halts

[`PoolSelection`](../Klr/PoolSelection.lean) proves a finite Hilbert-space
selection theorem. For any requested size, it chooses samples with small
pairwise centered inner products, while preserving any finitely many
eventual side conditions and making their actual positions distinct.

Using only that both the samples and the limit have norm at most one gives

$$
\left\|\frac1M\sum_{a\in G}(g_{i,a}-g_i)\right\|_2^2
\le\frac4M+\varepsilon.
$$

The paper has the sharper diagonal constant $1/M$. The weaker $4/M$ bound
is sufficient and follows from a general Hilbert-space estimate. Choosing
$\varepsilon$ small and then $M$ large gives $L^1$ error below $\delta$.
The selection simultaneously gives small individual high-set misses and
the finite weighted-coverage lower bound.

[`PoolWitness`](../Klr/PoolWitness.lean) translates these samples into actual
finite position pools. A union bound gives high-set failure below $\delta$;
the Hilbert-space estimate gives distance to $g_i$ below $\delta$; and the
weighted probability bound gives strict final coverage above $\gamma$.

For a fixed finite pool and a fixed answer sequence, there is a finite horizon
after which its queried fraction is exactly its eventual value: take the
maximum of the finitely many first-query times that exist on that path.
[`PoolQueryLimit`](../Klr/PoolQueryLimit.lean) uses this fact and dominated
convergence to prove the required finite-horizon limits.
[`PoolAcceptance`](../Klr/PoolAcceptance.lean) then chooses a horizon at which
all three strict tests pass. This proves eventual halting of the actual
search, without providing a convergence modulus to the program.

## Why every accepted pool is correct

The third finite test is essential to soundness. The position cutoff bounds
the final weighted coverage by $p^*+s$. An accepted finite horizon has weighted
coverage above $\gamma$, so the total later increase is below

$$
p^*+s-\gamma<4s.
$$

Every protected scan has weight at least $2^{-\ell}$. Nonnegativity of the
individual increases therefore gives

$$
\|v_i-v_{i,V}\|_1<4\delta.
$$

Combining this with the accepted $3\delta$ approximation test and the fixed
$\delta$ approximation to $g_i$ gives

$$
\|v_i-g_i\|_1<8\delta.
$$

[`PoolSoundness`](../Klr/PoolSoundness.lean) proves these inequalities for
arbitrary accepted pairs. Set approximation gives high-set failure below
$4\delta$. On the low set, a near-full read fraction forces either membership
in the small near-one strip or an error of magnitude greater than $\tau$.
Markov's inequality and the chosen budgets give the bound below $\eta$.

Finally, [`PoolCoverage`](../Klr/PoolCoverage.lean) proves the exact identity

$$
v_i(Z)=1-\frac{\#\{a\in G:\pi_i\text{ misses }a\}}{|G|}
$$

for nonempty pools and transports the strict inequalities to the paper's
missed-count formulation. The one-way implications needed for soundness
also handle the empty pool, whose strict missed-count event is empty.

## Remaining construction work

The pool theorem and the effective sparse-list theorem now supply the two
main finite combinatorial components. They must still be combined with the
actual finite-stage measures and normalized wager weights to choose the
affine blocks and horizons satisfying estimates (6)–(9). Their selected
syndromes and horizons must also be reconstructed by the fixed programs
needed for the short-description argument. Those obligations remain in
[`StageEstimates`](../Klr/StageEstimates.lean) and the
[affine-description note](affine-descriptions.md).
