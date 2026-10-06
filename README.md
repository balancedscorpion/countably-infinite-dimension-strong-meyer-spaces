# A strongly tempered Meyer space of countably infinite dimension

**Author and responsible maintainer: Jamie Martin.**

We prove that there exists a locally finite carrier Λ ⊆ ℝ whose **whole strongly tempered Meyer space** has complex Hamel dimension ℵ₀. Both a distribution and its distributional Fourier transform are locally atomic on Λ, and both actual coefficient records have polynomially weighted finite absolute variation:

\[
\exists N\in\mathbb N,\qquad
\sum_{x\in\Lambda}\frac{|a_x|}{(1+|x|)^N}<\infty.
\]

The physical and spectral records may use different exponents. Local atomicity means a single coefficient family gives the finite atomic formula on every compactly supported Schwartz test. Supports are contained in Λ; equality is not required. Fourier normalization is exp(−2πixξ). Dimension means algebraic Hamel dimension.

This is the strongly tempered example formalized in [MeyerGeneralProblem PR #653](https://github.com/ls558/MeyerGeneralProblem/pull/653), extracted from commit `65fe4ece1e3d2e83a9ac757b615141d3c0a2718b`. The entire recursive Lean proof closure is included, so building does not require access to the private source repository.

The [earlier countably infinite Meyer-space repository](https://github.com/balancedscorpion/countably-infinite-dimension-meyer-spaces) concerns the broader distributionally tempered class, without the weighted absolute-variation condition. Here that condition is imposed on **both** Fourier sides. A countable independent family alone would give only a lower bound; the proof also bounds the complete strong space from above.

The source constructs a parity carrier using a classically selected radius schedule. Every fixed weighted exponent layer of the whole strong space is finite dimensional, and these layers exhaust the space. Independent original modes on that same carrier supply the lower bound, proving exact rank ℵ₀. This is an existence result for one carrier. No effective schedule, classification of all carriers, equality with the broader distributional space, or novelty claim is asserted.

## Formal interfaces

[`Challenge.lean`](Challenge.lean) is the independent Mathlib-only statement of record. It defines local finiteness and weighted local atomic action directly. Its main theorem states exact rank and proves that membership is precisely the two-record strong condition on the same carrier. The span used to define the interface space is explicitly proved to equal that whole class.

[`Solution.lean`](Solution.lean) proves the same statement by identifying the existential local coefficients with the canonical isolation-test coefficients used by the original development. It imports the substantive proof, never Challenge. The only `sorry` is the intentional Challenge placeholder. [`comparator.json`](comparator.json) selects `CountablyInfiniteStrongCrystallineMeasures.strongCardinalClaim`, allowing only `propext`, `Quot.sound`, and `Classical.choice`.

## Reproduce

Install the toolchain in `lean-toolchain`, then run:

```sh
lake exe cache get Challenge.lean Solution.lean
lake build Challenge Solution
python3 scripts/check.py
git diff --check
```

Dependencies are pinned in `lake-manifest.json`; do not run `lake update` during verification. The extraction is ported to Lean 4.35.0-rc3 and matching Mathlib/Tau Ceti revisions. See [provenance](docs/PROVENANCE.md), [submission procedure](docs/PUBLICATION.md), and [validation](docs/VALIDATION.md).

The full Palomar reusable verification workflow is prepared in [`.github/workflows/palomar.yml`](.github/workflows/palomar.yml). Local checks, Palomar mechanical verification, editorial review, and permanent registration are separate stages. This preparation does not claim acceptance or registration.

## Attribution

Jamie Martin is the sole author of this submission. The implementation derives from the pinned PR #653 proof development. The earlier publication provides packaging and shared module-port references; its theorem is not used in place of this strong result. Source provenance, automated assistance and review boundaries are disclosed in [`formalization.yaml`](formalization.yaml). The submission is MIT licensed. Historical source agent reviews apply to their original commits, not to this extraction and toolchain port; no new independent human review is claimed.
