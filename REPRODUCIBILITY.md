# Reproduction and execution boundaries

The signed Dyck formalization was executed from mathematical commit `634f8fa6637688044f12ad108b14051e6d29e8bb`, tree `693e4670ea95c81f64996ac7f007680b46c0ddc1`. The exact workflow is [.github/workflows/w05-dyck-identification.yml](.github/workflows/w05-dyck-identification.yml), SHA256 `0b7857279c297e7b5d05d03ba20e57d99dc336bc52f4c7fb06787ad4ec388614`. Both checked workflows and all 28 project sources are distributed without changes.

The workflow retains its historical title “W05 finite Dyck contraction (not DyckWord identification)”. Its actual fixed source, complete declaration probe, and final assertions cover the later signed Dyck identification in [FORMALIZATION.md](FORMALIZATION.md). The older core workflow also keeps its historical banded-spine title. Neither title determines theorem scope, and neither workflow was renamed or rerun for this update.

## Fixed environment and procedure

The workflow uses the official Lean 4.19.0 binary release (compiler commit `6caaee842e94`), mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and nine revisions in [lake-manifest.json](lean-candidate/lake-manifest.json). ProofWidgets is checked against `v0.0.57`. The toolchain was not bootstrapped from source.

The seven cache roots are:

- `Mathlib.Combinatorics.Enumerative.DyckWord`
- `Mathlib.LinearAlgebra.Matrix.Block`
- `Mathlib.Algebra.MvPolynomial.Rename`
- `Mathlib.RingTheory.Localization.FractionRing`
- `Mathlib.Data.Matrix.Mul`
- `Mathlib.Combinatorics.SimpleGraph.Hasse`
- `Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting`

External precompiled libraries are trusted inputs. Exactly two calls in mathlib's `Cache/Requests.lean`, pruning `buildDir/lib` and `buildDir/ir`, are replaced by `pure ()` to retain downloaded files. The resulting helper SHA256 is `646fed31a48d85ed75746ec09d06c23f5abdaca455518b6760b0dcb2b10c47c0`. The exact replacements, hash assertion, and dependency diff are in the preserved workflow and log; this is not an entirely unmodified dependency checkout.

Reproduction uses the fixed mathematical commit and its exact source hashes. The workflow fetches pinned revisions, obtains caches, creates a previously absent `fresh-candidate/lib`, and compiles every project module in dependency order with `-j 1 -s 131072 -DElab.async=false`. It forbids pre-existing project artifacts in external cache/toolchain locations. Actual `lean --deps` output and hashes bind all 28 direct project imports to the new artifacts, with `Init.olean` as the additional direct dependency. This does not audit the complete external transitive import closure.

The probe prints 175 declaration types and transitive axiom lists, 40 definitions and one instance, and actual Field instances for integer- and rational-polynomial fraction fields. Final assertions check source integrity, complete declaration coverage and permitted axioms. The 30 supervised commands comprise 28 module compilations, the import check and the full probe.

The standard `ubuntu-24.04` runner retains the checked guards: initial total memory at least 14 GiB, available memory at least 12 GiB and disk at least 10 GiB; available memory at least 8 GiB before each Lean command; sampled group RSS at most 6 GiB and swap at most 512 MiB; system available memory at least 2 GiB; 180 seconds per command and 1,200 seconds cumulative Lean time. Cache acquisition has a 900-second limit, and the workflow a 40-minute limit. No guard was raised or triggered in the recorded run.

The workflow is restricted to ordinary pushes on `codex/w05-dyck-identification`; the older core workflow is restricted to `codex/w05-hankel-spine`. Default-branch documentation changes do not trigger them. This update claims no new build, mathematical suite, installation, or dependency-source replay.

## Evidence and byte identity

The [execution summary](verification/W05_signed_dyck_execution_summary.json) binds [run 38511499860](https://github.com/Aurantium-47/lecture-hall-polynomiality/actions/runs/38511499860) and job `115680821200` to the mathematical commit, source hashes, counts, and raw type excerpt. Later normal metadata confirmed one completed/success job and all seven completed/success steps. The initial in-progress snapshot remains a historical observation.

Complete logs and source checks establish coverage; an early uncompiled-candidate receipt records its earlier time. The terminal job response did not return `completed_at`, HTTP headers or a logs URL. The Python supervisor has no separately reported numeric exit field; child-process exits, final assertions and the successful workflow step are recorded. Missing fields remain null, not inferred from the run update time.

[PUBLIC_FILES.txt](PUBLIC_FILES.txt) lists the distributed files; [SHA256SUMS.txt](SHA256SUMS.txt) hashes every listed file other than itself, using committed bytes. The new signed-Dyck type excerpt preserves the original output bytes and line endings. The retained historical core summary's `main_type_sha256` refers to its original CRLF output; the historical committed core type has LF line endings, whose exact hash is in SHA256SUMS.txt. Neither historical file was rewritten.

No full external dependency source rebuild, full dependency replay, or independent kernel implementation was used. The Python scripts, computation data and TeX/PDF manuscripts remain historical artifacts with the scopes and commands in the [README](README.md). The v0.2.0 tag and release archive are not replaced or recompressed.

This work was completed with AI assistance.
