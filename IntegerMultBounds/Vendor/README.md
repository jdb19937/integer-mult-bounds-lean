# Vendored strong prime number theorem

`StrongPNT/` and `PrimeNumberTheoremAnd/` hold the strong prime number theorem
`Erdos970.Strong_PNT`:

```
∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * Real.exp (-c * (Real.log x) ^ (1/2))
```

together with the complex-analytic and zeta-function results it depends on, 21 modules in all.

Sources:
- math-inc/strongpnt at `2f5835c322314f55f1026ec2f139d704b7c45c69`;
- AlexKontorovich/PrimeNumberTheoremAnd at `c39a751132c88b6e8080b74c74023fd95b3d8be0`;
- both as ported to Lean `v4.34.1` and Mathlib `d13f23b7` by openai/math (`lean/patches/StrongPNT-lean4341.patch`
  and `lean/patches/PrimeNumberTheoremAnd-lean4341.patch`, openai/math commit `1581d4cbd`, Apache-2.0).

The module paths move from `StrongPNT.Erdos970.*` and `PrimeNumberTheoremAnd.Erdos970.*` to
`IntegerMultBounds.Vendor.StrongPNT.*` and `IntegerMultBounds.Vendor.PrimeNumberTheoremAnd.*`.
Each file is a `module` with public imports and an exposed public section (a public meta section
for `Tactic/AdditiveCombination.lean`). Declaration names are unchanged.
