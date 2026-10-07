# A strongly tempered Meyer space of countably infinite dimension

**Author and responsible maintainer: Jamie Martin.**

We prove that there exists a locally finite carrier Λ ⊆ ℝ whose **whole strongly tempered Meyer space** has complex Hamel dimension ℵ₀. Both a distribution and its distributional Fourier transform are locally atomic on Λ, and both actual coefficient records have polynomially weighted finite absolute variation:

\[
\exists N\in\mathbb N,\qquad
\sum_{x\in\Lambda}\frac{|a_x|}{(1+|x|)^N}<\infty.
\]

The physical and spectral records may use different exponents. Local atomicity means a single coefficient family gives the finite atomic formula on every compactly supported Schwartz test. Supports are contained in Λ; equality is not required. Fourier normalization is exp(−2πixξ). Dimension means algebraic Hamel dimension.

## Main achievement

The theorem establishes **exactly countably infinite dimension for the entire strongly tempered Meyer space** on one locally finite carrier. The weighted absolute-variation condition holds for both the physical and spectral coefficient families. This strengthens ordinary distributional temperedness by controlling the absolute size of the atomic coefficients on each Fourier side.

The proof combines two bounds on the same carrier:

- **Upper bound:** each fixed weighted exponent layer is finite dimensional, and countably many such layers exhaust the whole strongly tempered space.
- **Lower bound:** a countably infinite family of linearly independent strongly tempered distributions belongs to that space.

Together these establish complex Hamel rank ℵ₀. The carrier is constructed using a classically selected radius schedule, so the result is an existence theorem rather than an algorithm for computing the carrier.

The complete Lean proof and its supporting modules are included in this repository.

## Formal interfaces

[`Challenge.lean`](Challenge.lean) is the independent Mathlib-only statement of record. It defines local finiteness and weighted local atomic action directly. Its main theorem states exact rank and proves that membership is precisely the two-record strong condition on the same carrier. The span used to define the interface space is explicitly proved to equal that whole class.

[`Solution.lean`](Solution.lean) proves the same statement by identifying the existential local coefficients with canonical coefficients recovered by isolation tests. It imports the complete proof independently of Challenge. The only `sorry` is the intentional Challenge placeholder. [`comparator.json`](comparator.json) selects `CountablyInfiniteStrongCrystallineMeasures.strongCardinalClaim`, allowing only `propext`, `Quot.sound`, and `Classical.choice`.

## Reproduce

Install the toolchain in `lean-toolchain`, then run:

```sh
lake exe cache get Challenge.lean Solution.lean
lake build Challenge Solution
python3 scripts/check.py
git diff --check
```

The project uses Lean 4.35.0-rc3 with matching Mathlib and Tau Ceti revisions. Dependencies are pinned in `lake-manifest.json`; do not run `lake update` during verification. See the [validation record](docs/VALIDATION.md) and [submission procedure](docs/PUBLICATION.md).

The full Palomar reusable verification workflow is prepared in [`.github/workflows/palomar.yml`](.github/workflows/palomar.yml). Local checks, Palomar mechanical verification, editorial review, and permanent registration are separate stages. This preparation does not claim acceptance or registration.

## Author and license

Jamie Martin is the sole author and responsible maintainer of this submission. The project is released under the [MIT license](LICENSE). Formalization metadata and assistance disclosures are recorded in [`formalization.yaml`](formalization.yaml).
