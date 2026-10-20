# Retired Shared50 recursive machine

On 2026-10-19, 65 modules were removed, totaling 7,934 source lines. PR 6 made
the recursive interchange machine generic in its bit network (`MathlibTM2/M8/Machine`)
and runs it on the PR97 node. Kenny's Shared50 copy of the arbitrary-width tail
(`Machine/ArbitraryWidth*`, the binary and radix run modules) and the three moved
modules `Shared50BinaryRadixEqualShared`, `Shared50BinaryInterchangeRun` and
`Shared50BinaryInterchangeBudget` were imported only by the root, as the `shared50`
choice of `scripts/s6/apply_seam.py`. That choice is removed; `m8` still runs
Shared50 as a bit network on the generic machine.

The [exact manifest](retired-shared50-machine.json) records the files and recovery
baseline `7633232bda87c227ab0119c14b8593e9becdd718`. The scope rule of the
[native compact stage record](retired-native-compact-stage.md) applies.
