# Extraction and statement correspondence

The authoritative mathematical source is [MeyerGeneralProblem PR #653](https://github.com/ls558/MeyerGeneralProblem/pull/653), at immutable head `65fe4ece1e3d2e83a9ac757b615141d3c0a2718b` (open when inspected on 2026-10-06). Original files were read using `git show` at that commit, not from uncommitted working files. The private upstream repository is not a build dependency. All project sources in the recursive import closure of `MeyerGeneralProblem.Cardinal.Strong.OriginalClassicalStrongCountable` are included here with original paths and names.

[`extraction.json`](extraction.json) records upstream source SHA-256 hashes. The packaging/port reference is pinned at `0de61962a757b5e930dfe59dd94d191ae1f87922`. Module/API ports shared with the earlier publication were reused only when their original upstream bytes match. Its trimmed strong definitions in MeyerSpace and CarrierUnion were restored from PR #653. Module headers, public imports, exposed definitions and necessary API/visibility repairs adapt the proof to the newer pinned libraries. See [PORT.md](PORT.md) for the additional strong-proof API changes. Such ports preserve statements and use only standard Lean axioms.

The main source declaration is `MeyerGeneralProblem.StrongParity.exists_stronglyTemperedMeyerSpace_rank_aleph0`. Its witness is `originalClassicalStrongCountableCarrier`. The upper bound uses `originalClassicalStrongCarrier_finiteLayer`, the exact two-record exponent filtration and countably many finite-dimensional layers. The lower bound uses the independent original scheduled modes, with strong admission on the same carrier. The radius bound is classically selected, rather than supplied as a hypothesis.

| Publication object | Source correspondence |
| --- | --- |
| `LocallyFinite Λ` | `LocallyFiniteCarrier.finite_inter_Icc` |
| Local finite atomic formula | `IsLocallyAtomicCoefficientFamily` |
| Summable weighted coefficient norm | `stronglyTemperedCoefficientTerm`, after unique isolation-coefficient recovery |
| `StronglyAtomic S.carrier T` | Membership in `StronglyTemperedAtomicOnCarrier S`, proved by `strong_iff` |
| `strongMeyerSpace S.carrier` | `StronglyTemperedMeyerSpace S`, proved by `space_eq` |
| Hamel rank ℵ₀ | `exists_stronglyTemperedMeyerSpace_rank_aleph0` |

The independent Challenge uses bare subsets and existential coefficients, avoiding bundled project definitions and construction certificates. Solution proves that the span interface equals the entire strong class, so rank refers to the whole space. Both records impose absolute variation, not just distributional continuity or conditional action convergence. The complex C*-algebra instance introduced by proof imports is locally disabled in Solution to preserve identical topology elaboration with Challenge.

Jamie Martin is the sole submission author and responsible maintainer, as explicitly requested. OpenAI Codex assisted extraction, porting, interfaces, documentation and verification. Historical source automated attack/review reports are evidence for the upstream candidate only. No independent review of this new port, human peer review, novelty or Palomar acceptance is asserted. Supporting source names and mathematical provenance remain intact.
