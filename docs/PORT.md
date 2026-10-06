# Toolchain port

The source uses Lean 4.34.0-rc1. This submission uses Lean 4.35.0-rc3, meeting the inspected Palomar minimum of 4.35.0-rc2. Mathlib and Tau Ceti use the immutable revisions in the root manifest, shared with the pinned packaging reference.

All project files have module headers, public imports and exposed public definitions. Shared prior ports are identified in `extraction.json`; raw source hashes are retained separately from the submission hashes. The full strong definitions and transport lemmas in MeyerSpace and CarrierUnion were restored from the pinned upstream source, because the distributional publication had removed them.

Additional API changes in the strong proof:

- Real product inequalities use `Finset.prod_le_prod₀`, the renamed nonnegative-factor lemma, in PolydiskBound, ProductZCoefficients, CompactOriginalPolynomial and CompactOriginalZCoefficients.
- Injective coefficient transport uses `Finsupp.mapDomain_apply_of_injective`, the renamed injective evaluation lemma, in OriginalPositiveIntegerCoefficients, OriginalArrayEmbedding, PositiveOriginalNativeDilation and ScheduledOriginalChartCorners.

These are proof implementation changes, not theorem weakening. The independent interfaces prove equivalence with the original coefficient condition and complete space. Exact separately elaborated theorem-type equality and an axiom audit form part of the local verification script; Palomar Comparator remains a separate mechanical check.
