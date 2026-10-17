module
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
public import IntegerMultBounds.MathlibTM2.Mult.BandSpec
public import IntegerMultBounds.MathlibTM2.Fast.TableExp
public import IntegerMultBounds.MathlibTM2.Fast.TableNum
public import IntegerMultBounds.Machine


/-!
# Host machines for the integer tables of the numeric pipeline

The tables of `Mult/Pipeline.lean` are computed by programs of a binary register machine that
runs on the host registers (`IntegerMultBounds.MathlibTM2.Host`):

* `Fast/TableVM.lean`: the machine. Programs `TblCode n` over `n` variables, held as `W`-bit
  numerals in host registers; arithmetic instructions, comparisons, loops, and an emission
  instruction pushing the pair symbols `coeffSyms A w` of a coefficient. `tblCompile_runs`: a run
  of `k` atoms costs at most `k · tblC W w` host steps, `tblC W w = 32 (W + 4)² + 8 w`.
* `Fast/TableProg.lean`: contracts `TblDo` of programs (blocks in exact arithmetic, counting
  loops, renaming of variables), and `tblHost_runs`: a stream program followed by a move of the
  emitted symbols onto an output register.
* `Fast/TableLoad.lean`: loading variables from unary parameter registers.

## Machin's `π`

`Fast/TablePi.lean`: `tblPiCode` computes `piN P = piQ P` (`tblPi_eq_piQ`, `P ≥ 2`) in binary
(`tblPi_do`, `150 P + 400` atoms; `tblPi_host`, at most
`(150 P + 400) (32 (5 P + 20)² + 8 w)` host steps with `W = 5 P + 16`).

## Exponentials and Taylor sums

* `Fast/TableNum.lean`: the integer numerators of the real-valued definitions —
  `tbl_taylorExpI` (`taylorExpI`), `tbl_roundC`, `tbl_diskPhase`, `tbl_axisPhase`,
  `tbl_twistPlus`, `tbl_twistMinus`.
* `Fast/TableExp.lean`: the magnitude loop `tblMagCode` (`tblMag_do`, the residue-class sums
  `tblSum` of the Taylor magnitudes, `39 N + 30` atoms); the weight routine `tblExpCode`
  computing `expPiNat neg p a b = expPi neg p a b` (`tblExp_do`, `tblExp_do_expPi`,
  `310 p + 100` atoms), with `tbl_expApprox_neg`, `tbl_expApprox_pos` relating `expApprox` to the
  computed sums.
* `Fast/TablePhase.lean`: the Taylor machine `tblTaylorCode` (`tblTaylor_do`, `tblTaylor_exp`:
  the numerators of `taylorExpI q (X / 2^Q) n`, `39 n + 56` atoms) and the rounding machines
  `tblRound_do` (`roundC`) and `tblDisk_do` (`diskPhase`).

## Table streams

Each stream program emits its entries in the order the pipeline consumes them; an entry is
`coeffSyms A w (red w z)` for its numerator `z : GaussianInt` (imaginary part `0` for the weight
tables). With `#E` entries the atom count is `#E · O(p) + O(p)`, and the host theorem bounds the
steps by `atoms · tblC W w + 2 |stream| + 2`; the output register gains exactly the stream.

* `Fast/TableWeight.lean` (per axis `s, t, α, p`, window `m`):
  `tblStreamA` (`k = 0 … t − 1`, then `truncWindow s t m k` increasing), `tblStreamE`
  (`ℓ = 0 … s − 1`, then `offDiagWindow m` increasing), `tblStreamD` (`ℓ = 0 … s − 1`);
  `tblStreamA_host`, `tblStreamE_host`, `tblStreamD_host`.
* `Fast/TablePhaseChirp.lean`: `tblChirpStream` (`j = 0 … N − 1`, the numerators of
  `axisPhase p g N s j` at `p + g` bits); `tblChirp_host`.
* `Fast/TablePhaseTwist.lean`: `tblTwistStream` (`k = 0 … r − 1`, the numerators of
  `twistPlus p r k`, or of `twistMinus p r k` for `conj = true`, at `p` bits); `tblTwist_host`.
-/

@[expose] public section

