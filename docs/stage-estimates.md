# The remaining construction and the checked final reduction

The probability argument after the stage construction is now connected in Lean.
The remaining work is to **construct one sequence of blocks and descriptions**
meeting its hypotheses. This note states that boundary precisely.

The main conditional theorem is

```lean
Klr.exists_separating_of_stage_estimates_and_affine_programs
```

Its conclusion is the intended

```lean
∃ X : Klr.Cantor,
  Klr.KolmogorovLovelandRandom X ∧ ¬ Klr.MartinLofRandom X
```

but it has substantive construction hypotheses. There is no unconditional
separation theorem yet. The effective sparse-list construction and concrete
description test are proved; suitable pools and stage reconstruction programs
still have to be constructed. None of these results is assumed as an axiom.

## Indexing and the stage contract

Let `B : ℕ → AffineBlock` have pairwise disjoint supports. Write `P_n` for
`PrefixStage.law B n`; this conditions fair coin on exactly the blocks `k<n`.
Thus `P_{j+1}` is the stage already imposing block `j`, and `P_j` is the stage
immediately before it. Put

\[
e_j=2^{-j}/100.
\]

For each original strategy `s`, use its proved normalization. Write `π` for
its scan and `h` for its signed wager function. The construction must supply
one Borel transcript set `H`, its complement `L`, and a finite exceptional
cutoff `J`, such that the following properties hold for every `j≥J`.
The block horizons `V_j` are common to the construction.

| Field of `StageEstimates` | Required property |
| --- | --- |
| `measurableH` | `H` is a measurable set in transcript space |
| `horizon_avoidance` | On every transcript of length `V_j`, all blocks `k>j` still have full unread rank |
| `early_and_partial` | `E_{P_{j+1}} W_j(V_j) + P_{j+1}(0<R_j(V_j)<r_j) ≤ 4e_j` |
| `first_drop_tail` | `P_{j+1}(V_j<T_j<∞) ≤ 2e_j` |
| `high_no_drop` | `P_j(H ∩ {T_j=∞}) ≤ e_j` |
| `later_low_drop` | For every `k>j`, `P_{j+1}(L ∩ {T_k<∞}) ≤ e_k` |

Here `W_j(V_j)` is the actual sum of absolute wagers at rank drops in block
`j` through the first `V_j` queries. `R_j` is numerical remaining rank, and
`T_j` is the first strict rank decrease. A transcript-space set in a measure
formula means its preimage under the scan's measurable observation map.

These are the consequences of estimates (6)–(9) needed in Section 6. Weak
inequalities are sufficient; the paper's strict estimates imply them.
The horizon field is also weaker than the paper's support avoidance:
`HorizonAvoidance` explicitly enumerates every coordinate queried on every
branch before the horizon and proves that avoiding this finite set implies
the stated full-rank property.

The full hypothesis is

```lean
∀ s : BettingStrategy, ∃ (H : Set Cantor) (J : ℕ),
  StageEstimates B s.normalize.scan s.normalize.capital.wager V H J
```

There is no effective enumeration of total strategies in this statement.
`StrategyCountability` independently proves countability of the actual
computable-real strategy type, which is what the final null-set union needs.

## What follows from those stage estimates

`BlockProduct` constructs the actual infinite measure `ρ` from coherent
finite-coordinate marginals and proves that all block equations hold almost
surely. It also proves agreement with a finite stage on any transcript at
which all later blocks retain full unread rank.

`HorizonLaw` transports the entire finite-horizon transcript distribution,
including the early-wager expectation. `LateDropBound` uses the first
subsequent drop in the current or a later block, the Borel no-drop identity,
and the `H/L` partition to obtain

\[
\rho(\text{a drop in block }j\text{ after }V_j)
\le 4e_j+2e_j+e_j+\sum_{k>j}e_k=8e_j.
\]

The exact geometric tail identity and the finiteness of the `8e_j` and `4e_j`
budget series are proved in `StageErrorBudget`.

`EarlyLateWagers` then proves equation (11):

\[
\sum_{t:\,\text{query }t+1\text{ causes a rank drop}}|h(v_t)|<\infty
\quad\rho\text{-almost surely}.
\]

For early drops this follows from finite total expected wager. For late
drops, the first Borel–Cantelli lemma leaves only finitely many exceptional
blocks. A fresh scan makes only finitely many queries in any finite block,
so their total contribution is a finite sum on each input. The same argument
handles all blocks before `J`; no moment estimates for that finite prefix
are needed.

At every other query, `BlockProductAnswer` proves the actual fair child-mass
identity under `ρ`. `FairForced` factors capital into the fair-step and
forced-step products. A maximal inequality bounds the former almost surely;
the latter is bounded by the exponential of the finite absolute-wager sum.
Thus normalized capital is bounded almost surely. The proved normalization
preserves unbounded success, and countability gives KL randomness almost
surely under `ρ`.

This last product argument replaces the paper's separate `L²` martingale
convergence argument. It proves the same required boundedness conclusion.
The square-sum estimate remains necessary for the earlier candidate-support
wager bound.

## The concrete description test and the remaining programs

The original modular reduction took a predicate

```lean
W : ℕ × List Bool × List Bool → Prop
```

on `(test level, plain program, input cylinder)`, together with:

1. `REPred W`: one genuine c.e. predicate, uniformly in all three arguments.
2. For every level `n` and program `p`,

   \[
   \lambda\!\left(\bigcup_{v:\,W(n,p,v)}[v]\right)
   \le 2^{-(2|p|+n+1)}.
   \]

3. At every level `n`, some imposed block event `E_j` is contained in the
   cylinder union decoded from one program `p` at that level.

`DescriptionBudget` proves the exact sum over all plain programs and builds
a genuine ML test from these data. `AffineDescription` now supplies a concrete
`W`, with its uniform c.e. property and per-program bounds proved. A binary
description designates an actual partial-recursive program and a natural
input. The output is finite affine data, checked by a computable right-inverse
verifier and a rank threshold. Accepted prefixes enumerate exactly the
decoded affine event, whose measure is exactly `2^-r`.

Consequently the new final theorem takes only the following concrete
description obligation in addition to the stage estimates:

```lean
∀ n : ℕ, ∃ (j : ℕ) (p : List Bool) (c : AffineCode.Data),
  c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
  2 * p.length + n + 1 ≤ AffineCode.rank c ∧
  (B j).event ⊆ AffineCode.event c
```

An exact-event wrapper replaces the last inclusion with equality. Every
existing `AffineBlock` is proved to have a valid finite code and some binary
program producing it. That coverage theorem does not assert shortness.

`AffineProgramLength` separately proves explicit bounds for the actual
compiler. A fixed program with polynomially bounded numerical input, or
paired rank/advice input, eventually meets `2|p|+n+1 ≤ r` at each fixed test
level. `SparseSearch` supplies an actual partial-recursive completion of a
right-inverse certificate, halting precisely on full-row-rank systems and
preserving their affine events.

The remaining task is to write the stage reconstruction algorithm, prove it
computes the chosen matrix and syndrome, and show its input/advice obey the
proved length bounds. Writing the syndrome literally still costs `r` bits
and does not meet the desired budget. The
[affine-description note](affine-descriptions.md) records the concrete APIs.

Every input satisfying all block equations then fails the constructed test.
Since the block intersection has `ρ`-measure one, it meets the set of KL-random
inputs supplied by the probabilistic argument.

## Remaining substantive work

The proof still needs the computable pool lemma and the stage selection that
supplies the estimates above together with the reconstruction programs.
The [sparse-candidate note](sparse-candidates.md) records the now proved
Lemma 4, including its actual finite verifier and eventual termination of
exhaustive search. Its output, the pool program, the horizon and syndrome
choices, and the compiler bounds must be made compatible in one construction.
The checked reduction isolates their exact output requirements; it does not
reduce their mathematical difficulty to a routine final invocation.
