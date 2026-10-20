# Retired compact framed scalar grid

On 2026-10-19, 9 modules were removed, totaling 781 source lines.
`MathlibTM2/Layer/NodeZ.lean` imported `Machine/CompactFramedScalarGrid.lean`
without using it. Removing that import left the scalar grid and the network
modules reachable only through it (`CircuitCoefficients`,
`GaussianBoundedArithmetic`, `GaussianBoundedMotif`, `GaussianCircuit`,
`GaussianFrameGrid`, `GaussianPrecision`, `GroupedCoefficients`,
`RationalScalarGrid`) outside the theorem and the focused checks.

The [exact manifest](retired-scalar-grid.json) records the files and recovery
baseline `bd4e13cdff66ee9037a0c22076b703ec35fdb4f5`. The scope rule of the
[native compact stage record](retired-native-compact-stage.md) applies.
