# Independent kernel verification

The recorded run compiled all 18 mathematical modules, `ShorSuite` and `AxiomAudit`. It exported all 251 public declarations, including 202 public theorems, and their recursive dependencies. Three checkers then consumed the same uncompressed byte stream. The table reports the successful original run on 23 November 2026, 04:57–05:00 UTC. [Machine-readable certificate](evidence/checker-record.json) · [Checker output and controls](evidence/checker-output.txt)

| Stage | Setting or result |
| --- | --- |
| Lean compiler | 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` |
| Mathlib | Commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` |
| Source build | 20 compilation units, all exit 0, zero warnings and zero errors |
| con-leche | `--verified --jobs=2 --progress=1000`, accepted 21,530 declarations, exit 0 |
| con-ron | `--verified --jobs=2 --progress=1000`, accepted 21,530 declarations, exit 0 |
| leanchecker | `--from-export`, “Lean default kernel accepts the solution”, exit 0 |
| Uncompressed export | 102,795,751 bytes, SHA-256 `9FD7D3EBAEF59685DFF011EF27079E442FAD103B5C7E3C7FFE5447ED4B1D705A` |

The 21,530 count includes imported dependencies. The 251 named research declarations are the roots explicitly passed to `leanexport`. Fifteen internal generator lemmas are present in the source and enter through the dependency closure. The complete axiom readback contains one entry per public root. Across them Lean reports `propext`, `Classical.choice` and `Quot.sound`. The individual dependencies range from none to all three. [All public roots and their source lines](THEOREMS.md) · [Original axiom transcript](evidence/axioms.txt)

The negative control changed the proof expression of an unrelated test theorem, `CheckerControl.swap_and`, to its type. The original test export passed all three checkers. Both independent checkers rejected the damaged copy with exit code 1 and identified a type mismatch at `CheckerControl.swap_and`. [Control logs](evidence/checker-output.txt)

A second build for this release compiled all 20 units with zero warnings and zero errors. The new export was byte-for-byte identical to the archived stream. Both independent checkers and Lean accepted it again, the two negative controls rejected the damaged fixture, and the per-declaration audit matched all 251 roots. A separate invocation of the direct archive checker below also passed on the compressed file distributed here. [Release recheck](evidence/release-recheck.json)

## Check the included export directly

The repository includes the original [compressed proof export](evidence/suite.ndjson.gz). Its compressed size is 17,021,771 bytes, and the SHA-256 digest of the archive is `C1D83B283C965A54ACF8FE89BA818FBA6DE9AB73CD1C7CB29485EE471CE6C974`. The digest in the table identifies the uncompressed stream actually checked.

With PowerShell 7 and the matching Lean checker binaries installed, run this command from the repository root. The script inflates the archived file, validates the uncompressed digest and invokes all three checkers. It also accepts `-LeanBin` followed by the directory containing the matching executables. [Export check script](Check-Export.ps1)

```powershell
pwsh -NoProfile -File ./Check-Export.ps1
```

The underlying checker commands are reproduced here with the input path made relative. After decompressing the archive to `suite.ndjson`, these commands accept the same input.

```text
con-leche --verified --jobs=2 --progress=1000 suite.ndjson
con-ron --verified --jobs=2 --progress=1000 suite.ndjson
leanchecker --from-export suite.ndjson
```

## Rebuild the proof from source

The [Lean pin](lean-toolchain), [Lake configuration](lakefile.toml) and [dependency lockfile](lake-manifest.json) specify the project. With Elan, Git and the pinned dependencies available, Lake builds the mathematical source and prints the axiom dependencies of the public declarations.

```text
lake exe cache get
lake build ShorSuite AxiomAudit
```

For the complete Windows verification run, use PowerShell 7, the matching `lean`, `leanexport`, `con-leche`, `con-ron` and `leanchecker` executables under the selected toolchain, and compiled Mathlib dependencies. From the repository root run:

```powershell
pwsh -NoProfile -File ./Verify-Suite.ps1 -RunNegativeControl
pwsh -NoProfile -File ./Check-Axioms.ps1
```

`Verify-Suite.ps1` accepts `-DependenciesRoot` for a separate pinned `.lake/packages` cache, `-LeanBin` for the checker directory, and `-DisplaySource` to print each source before compiling. The verifier makes new objects, regenerates the root list, exports it with `leanexport ShorSuite --` followed by the 251 names, checks the resulting stream, and records commands, exit codes, object hashes and tool hashes under `verification/`. The axiom script checks the entire root list and source hashes against that run. [Full verification script](Verify-Suite.ps1) · [Root list](declarations.txt) · [Axiom audit script](Check-Axioms.ps1)

The verification record gives SHA-256 digests for all 20 compiled source files and the binaries used for checking. The 18 mathematical modules, aggregate root and audit module in this release preserve the checked source bytes. The public environment script resolves the dependency cache inside the project or from an explicit path.
