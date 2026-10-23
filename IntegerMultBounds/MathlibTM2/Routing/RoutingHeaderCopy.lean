module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderValue
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelective

/-! Executed canonical-header generation for the exact R2 configuration.
The operand is a live padded binary word; no header bits enter the program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem routingHeaderCopy_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (p : Par) (X rb R B : ℕ) (c : Fin 2) (k : Fin 5)
    (src dst tmp work : Fin T) (hregs : [src, dst, tmp, work].Nodup)
    (L : ℕ) (hfit : selectiveSwapValues p X R (fieldsLen (selectiveKeyLen p X rb) + B) c k < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms L (selectiveSwapValues p X R (fieldsLen (selectiveKeyLen p X rb) + B) c k))
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryCanonicalCopyProgram src dst tmp work) (mk v S) (10 * L + 12)
        (mk v' { S with R := Function.update S.R dst ((repairCanonicalHeaders p X rb R B c k).map bitSymbol) }) := by
  exact binaryCanonicalHeaderCopy_exec body src dst tmp work hregs L _ hfit v S hsrc hdst htmp hwork

end IntegerMultBounds.MathlibTM2.Routing
