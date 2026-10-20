# Retired Machine plumbing

On 2026-10-20, 21 `Machine/` modules were removed, totaling 2,676 source lines.
They follow the [Shared50 recursive tail](retired-shared50-recursive-tail.md):
no constant they define is reached from the completed theorem, the compact and
CRT checks, or the open `M6`, `M8`, `DFT` and `PR589` work, and no retained
module refers to them by name. Only the root imported them directly.

The [exact manifest](retired-machine-plumbing.json) records the files and
recovery baseline `c773bd68d616852f8b224545d93ce181f70be606`.

| Family | Modules |
| --- | ---: |
| `ArbitraryWidthHigh*`, `ArbitraryWidthSchedule`, `ActualAffineScalingDimensions` | 6 |
| `RadixAdd*`, `RadixLinearCombination*`, `RadixDivisionData`, `MarkedRadixRefresh` | 8 |
| `RecursiveMixed*`, `RecursiveCleanReturn`, `RecursiveRowDivisor` | 5 |
| `CompactGuardGrowth`, `OneHotCount` | 2 |

Eight unused modules stay because retained, unused declarations name them:
`FiniteDispatch`, `SharedPayloadFrames`, `SharedPayloadPair`,
`SharedPayloadStageSkeleton`, `RecursiveInterchangeVolume`,
`RecursiveDescriptorSize`, `RecursiveHeaderRestore` and the supplier seam
`BinaryInterchangeRun`.
