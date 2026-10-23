module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderGenerate
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderValue

/-! Prepare canonical row-count and interval-width sources from padded binary
inputs. The inputs and shared scratch are restored; only two sources change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def repairHeaderSourceProgram {T Q A : ℕ} {P U : Type}
    (src : Fin 2 → Fin T) (bank : RepairHeaderReg → Fin T) : Pr P T Q A U :=
  .seq (binaryCanonicalCopyProgram (src 0) (bank (.exchange (.base .rows)))
    (bank (.exchange (.base (.scratch 1)))) (bank (.exchange (.base (.scratch 2)))))
    (binaryCanonicalCopyProgram (src 1) (bank (.exchange (.base .target)))
      (bank (.exchange (.base (.scratch 1)))) (bank (.exchange (.base (.scratch 2)))))

def repairHeaderSourceBank {T A : ℕ} (bank : RepairHeaderReg → Fin T) (R w : ℕ)
    (tapes : Fin T → List (Fin (A + 4))) :=
  Function.update (Function.update tapes (bank (.exchange (.base .rows)))
    ((GrowingCounterData.advance R []).map bitSymbol)) (bank (.exchange (.base .target)))
    ((GrowingCounterData.advance w []).map bitSymbol)

theorem repairHeaderSources_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src : Fin 2 → Fin T) (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) (hsep : ∀ i r, src i ≠ bank r)
    (Lr Lw R w : ℕ) (hR : R < 2 ^ Lr) (hw : w < 2 ^ Lw)
    (v : HS T Q A U) (S : Stacks T A)
    (hrowInput : S.R (src 0) = binSyms Lr R) (hwidthInput : S.R (src 1) = binSyms Lw w)
    (hrows : S.R (bank (.exchange (.base .rows))) = [])
    (htarget : S.R (bank (.exchange (.base .target))) = [])
    (htmp : S.R (bank (.exchange (.base (.scratch 1)))) = [])
    (hwork : S.R (bank (.exchange (.base (.scratch 2)))) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (repairHeaderSourceProgram src bank) (mk v S) ((10 * Lr + 12) + (10 * Lw + 12))
        (mk v' { S with R := repairHeaderSourceBank bank R w S.R }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := binaryCanonicalHeaderCopy_exec body (src 0) (bank (.exchange (.base .rows)))
    (bank (.exchange (.base (.scratch 1)))) (bank (.exchange (.base (.scratch 2))))
    (by simp [List.nodup_cons, hbank.eq_iff, hsep]) Lr R hR v S hrowInput hrows htmp hwork
  let S₁ : Stacks T A := { S with R := Function.update S.R (bank (.exchange (.base .rows))) ((GrowingCounterData.advance R []).map bitSymbol) }
  obtain ⟨v₂, hu₂, he₂⟩ := binaryCanonicalHeaderCopy_exec body (src 1) (bank (.exchange (.base .target)))
    (bank (.exchange (.base (.scratch 1)))) (bank (.exchange (.base (.scratch 2))))
    (by simp [List.nodup_cons, hbank.eq_iff, hsep]) Lw w hw v₁ S₁
    (by simp [S₁, hsep, hwidthInput])
    (by simp [S₁, hbank.eq_iff, htarget]) (by simp [S₁, hbank.eq_iff, htmp])
    (by simp [S₁, hbank.eq_iff, hwork])
  exact ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
