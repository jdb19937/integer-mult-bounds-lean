module

public import Mathlib.Data.Fin.Basic

/-!
# The registers of the pipeline

The pipeline runs on `50` DFT registers, named here as numerals of `Fin 50` (`open scoped
IntegerMultBounds.MathlibTM2.DFT.Reg`), so that `simp` decides every disequality between them.

| registers | use |
|---|---|
| `rIn`, `rEnt`, `rPw`, `rWm`, `rT` | `parse`: input, entries `fieldSyms w a`, `p`, `ω`, scratch |
| `rWR`, `rW3` | width registers of `2 w` and `3 w` symbols |
| `rCnt` … `rYn` | the Newton reciprocal (`recipProg`); `μ` stays in `rAa`, `k'` symbols in `rWK` |
| `rt1` … `rt5` | scratch of every block |
| `rZ`, `rQ1`, `rQ2`, `rP3`, `rO` | `modMulProg`, `barrettProg`; `rO` is the result |
| `rF`, `rFt`, `rFu` | a copy of the entries as the counter of a chirp loop |
| `rC`, `rE`, `rWinv` | the chirp `c m`, the power `ω ^ m`, the inverse root |
| `rV`, `rCw`, `rWc`, `rV2` | the chirp pack, reversed and in order; widening scratch |
| `rXa`, `rUp`, `rNcnt` | an entry, the chirped input pack, a counter of `n` ticks |
| `rZp`, `rDw`, `rTk`, `rO2`, `rOut` | the product, a width of `n s`, a digit, a value, the output |
-/

namespace IntegerMultBounds.MathlibTM2.DFT.Reg

scoped notation "rIn" => (0 : Fin 50)
scoped notation "rEnt" => (1 : Fin 50)
scoped notation "rPw" => (2 : Fin 50)
scoped notation "rWm" => (3 : Fin 50)
scoped notation "rT" => (4 : Fin 50)
scoped notation "rWR" => (5 : Fin 50)
scoped notation "rW3" => (6 : Fin 50)
scoped notation "rCnt" => (7 : Fin 50)
scoped notation "rDp" => (8 : Fin 50)
scoped notation "rWK" => (9 : Fin 50)
scoped notation "rW2K" => (10 : Fin 50)
scoped notation "rWL" => (11 : Fin 50)
scoped notation "rONE" => (12 : Fin 50)
scoped notation "rSIX" => (13 : Fin 50)
scoped notation "rB1" => (14 : Fin 50)
scoped notation "rDd" => (15 : Fin 50)
scoped notation "rAa" => (16 : Fin 50)
scoped notation "rB2" => (17 : Fin 50)
scoped notation "rB3" => (18 : Fin 50)
scoped notation "rY" => (19 : Fin 50)
scoped notation "rYn" => (20 : Fin 50)
scoped notation "rt1" => (21 : Fin 50)
scoped notation "rt2" => (22 : Fin 50)
scoped notation "rt3" => (23 : Fin 50)
scoped notation "rt4" => (24 : Fin 50)
scoped notation "rt5" => (25 : Fin 50)
scoped notation "rZ" => (26 : Fin 50)
scoped notation "rQ1" => (27 : Fin 50)
scoped notation "rQ2" => (28 : Fin 50)
scoped notation "rP3" => (29 : Fin 50)
scoped notation "rO" => (30 : Fin 50)
scoped notation "rF" => (31 : Fin 50)
scoped notation "rFt" => (32 : Fin 50)
scoped notation "rFu" => (33 : Fin 50)
scoped notation "rC" => (34 : Fin 50)
scoped notation "rE" => (35 : Fin 50)
scoped notation "rWinv" => (36 : Fin 50)
scoped notation "rV" => (37 : Fin 50)
scoped notation "rCw" => (38 : Fin 50)
scoped notation "rWc" => (39 : Fin 50)
scoped notation "rV2" => (40 : Fin 50)
scoped notation "rXa" => (41 : Fin 50)
scoped notation "rUp" => (42 : Fin 50)
scoped notation "rNcnt" => (43 : Fin 50)
scoped notation "rZp" => (44 : Fin 50)
scoped notation "rDw" => (45 : Fin 50)
scoped notation "rTk" => (46 : Fin 50)
scoped notation "rO2" => (47 : Fin 50)
scoped notation "rOut" => (48 : Fin 50)

end IntegerMultBounds.MathlibTM2.DFT.Reg
