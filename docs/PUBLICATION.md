# Palomar submission preparation

Requirements were inspected on 2026-10-06 in the [Palomar specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md). The prepared full reusable workflow pins PalomarSubmission at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. Its toolchain minimum is Lean 4.35.0-rc2; this project uses 4.35.0-rc3.

1. Run the commands in README and inspect `docs/VALIDATION.md`.
2. Commit the complete sources, independent interfaces, metadata, license and dependency lock. Publish the exact snapshot to the public submission repository and record its full 40-character SHA.
3. Dispatch **Palomar mechanical preflight** with that exact SHA. The workflow calls the full verifier with `comparator.json` and `palomar-standard-v1`. Retain the run URL and report. A local build or axiom check is not a full mechanical pass.
4. Once the full report passes, submit that same public repository and SHA through the [Palomar intake](https://submit.palomar-registry.org/). Jamie Martin is the author and responsible maintainer. Review the editorial report before deciding on permanent registration.

The repository contains one root Lakefile, one MIT license and immutable public Git dependency pins. Every project Lean file uses the module system. Challenge imports only Mathlib and contains one intentional placeholder. Solution and its complete proof closure contain no placeholders and never import Challenge. The local script checks source boundaries, pins, metadata, elaborated statement equality and theorem axioms.

Preparation is authorized by Jamie Martin's request. Intake, editorial acceptance and permanent registry publication are not claimed as completed. Permanent registration is a separate decision on the reviewed exact-commit result.
