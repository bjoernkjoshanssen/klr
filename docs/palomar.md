# Palomar entry preparation

This package advertises the completed separation theorem for the repository's
total computable-real strategy convention. It is a preparation for a Palomar
entry; no registration or editorial approval is claimed.

## Compared mathematical claims

There exists an infinite binary sequence on which every total computable
adaptive betting strategy with uniformly computable-real, nonnegative, fair
capital has bounded capital, while the sequence fails a Martin-Löf test for
the fair-coin measure. Each strategy queries distinct positions along every
possible answer history. Success means unbounded capital; there is no
requirement that a scan eventually visit every input coordinate.

Martin-Löf randomness implies randomness against these strategies. The two
compared declarations therefore state separation and proper inclusion:

```lean
PalomarKlr.separation
PalomarKlr.strict_inclusion
```

The substantive development is this repository, following Chenghua Liu and
Boning Meng's [version 1 paper](https://arxiv.org/abs/2611.31004v1). The entry
does not claim an independent discovery of the mathematical result. Proof
adaptations, automation, review, and scope are recorded in
[formalization.yaml](../formalization.yaml).

The proved partial rational-wager corollary remains supplementary. An
equivalence with a general partial computable-real capital presentation is
not formalized and is not asserted by the entry.

## Statement and proof are separate

[Challenge.lean](../Challenge.lean) imports only Mathlib. It independently
states Cantor space, fair coin, uniformly computable-real capital, total fresh
scans, unbounded success, KL randomness, uniformly coded ML tests, and ML
randomness. Every mathematical definition is fixed; there are no definition
holes. Comparator checks the statements and their transitive definitions
against the proof environment.

The two theorem `sorry` holes in Challenge are the advertised statements that
Comparator asks the solution to prove. They are required statement templates,
not admissions in the proved development. Neither `Klr` nor `Solution` imports
Challenge. The files deliberately compile in separate environments because
Challenge repeats the foundational definition names independently.

[Solution.lean](../Solution.lean) imports `Klr.Separation` and proves both
wrappers from the completed theorems. Its proofs have only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

The submitted [comparator.json](../comparator.json) names both theorems and
permits only those three axioms. Its `definition_names` list is empty: that
field would designate definitions the solver is allowed to supply, not a list
of the fixed definitions to audit.

## Verification

With the pinned Lean toolchain available:

```sh
lake exe cache get
lake build Klr Solution Challenge
bash scripts/verify-comparator.sh
```

The last command requires bubblewrap and working Linux user/network namespace
support. It uses the toolchain's Comparator and replays the exported proof
with Lean's kernel, NanoDa, and con-ron. The sandbox is retained; a local host
that cannot provide it can use the repository's Comparator verification
workflow. Successful compilation or an axiom audit alone is not a Comparator
result.

Palomar also requires its **full reusable preflight**, which is distinct from
the standalone Comparator check. The workflow in
[palomar-preflight.yml](../.github/workflows/palomar-preflight.yml) pins both
the reusable workflow and its `pipeline_commit` to
`046554302064b2c83c2b924bea6db87fc5900c68`, with `mode: full` and
`execution_profile: palomar-standard-v1`. It runs on the exact source commit
selected by the workflow event. A passing report from that complete workflow
is required before requesting intake.

## Licence

The maintainer selected Apache-2.0 for this repository. The complete text is
in the root [LICENSE](../LICENSE), and `project.license` records the matching
SPDX identifier `Apache-2.0`. Cited papers and external dependencies retain
their own licences.

The complete reusable preflight checks the licence together with the pinned
source, metadata, statement, proof, and independent kernel verification.
Successful metadata-shape or standalone Comparator checks alone do not mean
that the full Palomar preflight passed.

## Submission handoff

Once the licensed snapshot passes full preflight, submit the immutable
40-character commit at <https://submit.palomar-registry.org/> with:

| Field | Value |
| --- | --- |
| Repository | `bjoernkjoshanssen/klr` |
| Commit | The exact public commit covered by the passing full preflight |
| Comparator configuration | `comparator.json` |
| Project directory | Repository root; leave the optional field blank |
| Metadata | `formalization.yaml`; leave the optional field blank |
| Existing Palomar ID | Blank for this first entry |
| Relationship | Responsible author or maintainer |

Palomar's agent route requires both a temporary Git tag and a fresh secret
gist. If that route is unavailable, the human submitter performs the browser
GitHub sign-in. The official instructions prohibit an agent from completing
that sign-in on the human's behalf. Keep the private status link returned by
the service; it is needed to follow the review.

Successful verification and review do not register the result automatically.
The submitter sees the actual review and makes a separate decision to publish
the permanent registry record. No such decision or review is implied by this
preparation package.

## Official requirements

- [Submission guide](https://palomar-registry.org/how-to-submit)
- [Binding submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Agent and preflight instructions](https://submit.palomar-registry.org/llms.txt)
- [Formalization metadata standard](https://github.com/mathlib-initiative/formalization.yaml)
