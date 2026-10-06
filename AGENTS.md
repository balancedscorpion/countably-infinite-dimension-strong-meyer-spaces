Don't use env vars unless it really is the best solution.

This repository submits the whole strongly tempered Meyer-space countable
Hamel-rank existence theorem from PR #653. Preserve weighted absolute variation
on both actual Fourier records, local atomicity, same-carrier quantifiers and
exhaustiveness. Jamie Martin is the sole submission author.

Keep Challenge Mathlib-only and Solution independent of Challenge. No proof
holes outside the statement placeholder, custom axioms, native_decide or
weakened statements. Keep interfaces, metadata and README aligned. Include
only the recursive proof import closure, not research archives or unrelated
entry points. Run lake build Challenge Solution, python3 scripts/check.py and
git diff --check. Distinguish local checks from Palomar verification and registration.
