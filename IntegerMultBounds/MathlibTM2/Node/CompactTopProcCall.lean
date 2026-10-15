module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcRegs

/-! Actual layer-call cleanup for arbitrary basis banks and persistent rest
predicates. CallSpec is the existing recursive layer boundary, not a top-program oracle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {BReg : Type} [Fintype BReg] {A Q : ℕ} {U P : Type}

local macro "compactTopFupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj,
  reduceCtorEq, ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.ph.injEq, LReg.lf.injEq,
  IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue]))

/-- Call the layer procedure and clear `lev`, `u`, `a₀`, `L`, `rows`. -/
noncomputable def compactTopCallClr (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq cp
  (.seq (uclear (reg .lev)) (.seq (uclear (reg .u)) (.seq (uclear (reg .a₀))
  (.seq (uclear (reg .L)) (uclear (reg .rows))))))

/-- **One call.** From the parameters of level `j` (`ParState`), every register at rest for `N`
address bits and `io` holding the stream of `Z`, the layer replaces `Z` on `io` and the five
per-call parameters are emptied; every other register ends as it started. -/
theorem compactTopCallClr_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions)
    {N r w K ρ R₀ j u a₀ cc : ℕ}
    (hfit : ∀ i < bits u j, a₀ + ρ + K * i < N)
    (hcall : CallSpec body cp bc ds R₀ j u K ρ a₀ (K*bits u j) N r w hfit cc)
    (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) N)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = []) (hpar : ParState S.R j u K ρ a₀ (K * bits u j) (rowsAt R₀ j) N w (r * w))
    (hrest : Rest bc N r w S.R) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ cc +
        (2 * j + 2 * u + 2 * a₀ + 2 * (K * bits u j) + 2 * rowsAt R₀ j + 10) ∧
      Exec body (compactTopCallClr cp) (mk v S) c
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update S.R (reg .io)
              (encZ A w (layerZ u ds R₀ j (actMap a₀ ρ K (bits u j) N hfit) Z)))
            (reg .lev) []) (reg .u) []) (reg .a₀) []) (reg .L) []) (reg .rows) [] }) := by
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := hcall Z v S hL hpar hrest hio
  set X := encZ A w (layerZ u ds R₀ j (actMap a₀ ρ K (bits u j) N hfit) Z)
  set R₁ := Function.update S.R (reg .io) X with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := uclear_exec body (reg .lev) v₁ { S with R := R₁ }
  obtain ⟨v₃, hu₃, e₃⟩ := uclear_exec body (reg .u) v₂
    { S with R := Function.update R₁ (reg .lev) [] }
  obtain ⟨v₄, hu₄, e₄⟩ := uclear_exec body (reg .a₀) v₃
    { S with R := Function.update (Function.update R₁ (reg .lev) []) (reg .u) [] }
  obtain ⟨v₅, hu₅, e₅⟩ := uclear_exec body (reg .L) v₄
    { S with
      R := Function.update (Function.update (Function.update R₁ (reg .lev) []) (reg .u) [])
        (reg .a₀) [] }
  obtain ⟨v₆, hu₆, e₆⟩ := uclear_exec body (reg .rows) v₅
    { S with
      R := Function.update (Function.update (Function.update (Function.update R₁
        (reg .lev) []) (reg .u) []) (reg .a₀) []) (reg .L) [] }
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆))))⟩
  have h1 := hpar .lev
  have h2 := hpar .u
  have h3 := hpar .a₀
  have h4 := hpar .L
  have h5 := hpar .rows
  simp only [parSpec] at h1 h2 h3 h4 h5
  dsimp only
  simp only [hR₁]
  compactTopFupd
  rw [h1, h2, h3, h4, h5]
  omega

end
end IntegerMultBounds.MathlibTM2.LayerMachine
