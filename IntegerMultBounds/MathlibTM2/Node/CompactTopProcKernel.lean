module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcCall

/-! Concrete top-kernel stage on an arbitrary basis bank, with persistent basis
rest state. Only the existing per-layer CallSpec is an induction boundary;
field reads, branching, call cleanup and framing are proved here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {BReg : Type} [Fintype BReg] {A Q : ℕ} {U P : Type}

/-- The top kernels: `q` (field `5`) leaf bits at offset `aT` (field `6`), `L = K q` (field `7`),
`R` rows (field `3`); one call of the layer procedure at level `0`, skipped when `q = 0`. -/
noncomputable def compactTopKerS (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg .u) 5)
  (.seq (.act (peekR (reg .u)))
  (.cond (·.flag)
    (.seq (compactTopRd (reg .a₀) 6) (.seq (compactTopRd (reg .L) 7) (.seq (compactTopRd (reg .rows) 3) (compactTopCallClr cp))))
    (uclear (reg .u))))

/-- The step bound of `compactTopKerS`. -/
def compactTopKerSCost (cfg : List ℕ) (K R q aT cc : ℕ) : ℕ :=
  4*topGetCost cfg+cc+(2*q+2*aT+2*(K*q)+2*R+16)

theorem compactTopKerS_exec (body : P → Pr P (nT BReg) Q A U)
    (cp : Pr P (nT BReg) Q A U) (bc : BReg → List (Fin (A+4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (cc : ℕ)
    {cfg pfs : List ℕ} {N R r w K ρ q aT : ℕ} (h3 : cfg[3]? = some R) (h5 : cfg[5]? = some q)
    (h6 : cfg[6]? = some aT) (h7 : cfg[7]? = some (K * q))
    (hfitT : ∀ i < q, aT + ρ + K * i < N)
    (hcall : 1≤q → CallSpec body cp bc ds R 0 q K ρ aT (K*q) N r w
      (by simpa only [bits] using hfitT) cc)
    (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = []) (hT : CompactTopRegs bc S.R N r w K ρ) (hI : CompactTopIn (BReg := BReg) S.R cfg pfs)
    (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopKerSCost cfg K R q aT cc ∧
      Exec body (compactTopKerS cp) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ A w (k2s ((List.finRange q).map (actMap aT ρ K q N hfitT)) Z)) }) := by
  have hl3 : 3 < cfg.length := (List.getElem?_eq_some_iff.1 h3).1
  have hl5 : 5 < cfg.length := (List.getElem?_eq_some_iff.1 h5).1
  have hl6 : 6 < cfg.length := (List.getElem?_eq_some_iff.1 h6).1
  have hl7 : 7 < cfg.length := (List.getElem?_eq_some_iff.1 h7).1
  have hc3 : cfg[3] = R := (List.getElem?_eq_some_iff.1 h3).2
  have hc5 : cfg[5] = q := (List.getElem?_eq_some_iff.1 h5).2
  have hc6 : cfg[6] = aT := (List.getElem?_eq_some_iff.1 h6).2
  have hc7 : cfg[7] = K * q := (List.getElem?_eq_some_iff.1 h7).2
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .u) (by simp) (by simp) 5 hl5 v S
    hlc hI.cf
  rw [hc5, hT.hu, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg .u) (List.replicate q tick) with hR₁
  have e₂ := Exec.act (body := body) (peekR (reg .u) : Act _ _ _ _) (mk v₁ { S with R := R₁ })
  rw [peekR_run] at e₂
  dsimp only at e₂
  have hu₁' : R₁ (reg .u) = List.replicate q tick := by simp [hR₁]
  cases q with
  | zero =>
      rw [hu₁'] at e₂
      simp only [List.replicate_zero, List.head?_nil, Option.isSome_none] at e₂
      obtain ⟨v₃, hu₃, e₃⟩ := uclear_exec body (reg .u) { v₁ with flag := false } { S with R := R₁ }
      have e₃' := Exec.cond_false (body := body) (f := (·.flag))
        (p := .seq (compactTopRd (reg .a₀) 6) (.seq (compactTopRd (reg .L) 7) (.seq (compactTopRd (reg .rows) 3)
          (compactTopCallClr cp)))) (by rfl) e₃
      refine ⟨v₃, _, by rw [hu₃, hu₁], ?_, Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃')) rfl ?_⟩
      · unfold compactTopKerSCost; simp [hR₁]; omega
      · congr 2
        funext k
        by_cases hk : k = reg .u
        · subst hk; simp [hR₁, hT.hu]
        · by_cases hk' : k = reg .io
          · subst hk'; simp [hR₁, hk, hio]; rfl
          · simp [hR₁, hk, hk']
  | succ q =>
      rw [hu₁'] at e₂
      simp only [List.replicate_succ, List.head?_cons, Option.isSome_some] at e₂
      obtain ⟨v₃, c₃, hu₃, hc₃', e₃⟩ := compactTopRd_exec body (x := .a₀) (by simp) (by simp) 6 hl6
        { v₁ with flag := true } { S with R := R₁ } (by simp [hR₁, hlc])
        (by simpa [hR₁] using hI.cf)
      dsimp only at e₃
      rw [hc6, show R₁ (reg .a₀) = [] by simp [hR₁, hT.ha₀], List.append_nil] at e₃
      set R₃ := Function.update R₁ (reg .a₀) (List.replicate aT tick) with hR₃
      obtain ⟨v₄, c₄, hu₄, hc₄', e₄⟩ := compactTopRd_exec body (x := .L) (by simp) (by simp) 7 hl7
        v₃ { S with R := R₃ } (by simp [hR₃, hR₁, hlc]) (by simpa [hR₃, hR₁] using hI.cf)
      dsimp only at e₄
      rw [hc7, show R₃ (reg .L) = [] by simp [hR₃, hR₁, hT.hL], List.append_nil] at e₄
      set R₄ := Function.update R₃ (reg .L) (List.replicate (K * (q + 1)) tick) with hR₄
      obtain ⟨v₅, c₅, hu₅, hc₅', e₅⟩ := compactTopRd_exec body (x := .rows) (by simp) (by simp) 3 hl3
        v₄ { S with R := R₄ } (by simp [hR₄, hR₃, hR₁, hlc])
        (by simpa [hR₄, hR₃, hR₁] using hI.cf)
      dsimp only at e₅
      rw [hc3, show R₄ (reg .rows) = [] by simp [hR₄, hR₃, hR₁, hT.hrows], List.append_nil] at e₅
      set R₅ := Function.update R₄ (reg .rows) (List.replicate R tick) with hR₅
      have hR₅o : ∀ x : LReg BReg, x ≠ .u → x ≠ .a₀ → x ≠ .L → x ≠ .rows →
          R₅ (reg x) = S.R (reg x) := by
        intro x h1 h2 h3 h4
        simp [hR₅, hR₄, hR₃, hR₁, h1, h2, h3, h4]
      have hpar : ParState R₅ 0 (q + 1) K ρ aT (K * bits (q + 1) 0) (rowsAt R 0) N w (r * w) := by
        have hh : ∀ x : LReg BReg, x ∈ [LReg.lev, .K, .ρ, .n, .w, .rw] →
            R₅ (reg x) = S.R (reg x) := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact hR₅o _ (by simp) (by simp) (by simp) (by simp)
        refine compactTopParState ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hh _ (by simp), hT.hlev]; rfl
        · simp [hR₅, hR₄, hR₃, hR₁]
        · rw [hh _ (by simp)]; exact hT.hK
        · rw [hh _ (by simp)]; exact hT.hρ
        · simp [hR₅, hR₄, hR₃]
        · simp [hR₅, hR₄, bits]
        · simp [hR₅, rowsAt]
        · rw [hh _ (by simp)]; exact hT.hn
        · rw [hh _ (by simp)]; exact hT.hw
        · rw [hh _ (by simp)]; exact hT.hrw
      have hrest₅ : Rest bc N r w R₅ := compactTopRest_par hT.rest fun x hx =>
        hR₅o x (fun h => hx (by simp [h, parRegs])) (fun h => hx (by simp [h, parRegs]))
          (fun h => hx (by simp [h, parRegs])) (fun h => hx (by simp [h, parRegs]))
      obtain ⟨v₆, c₆, hu₆, hc₆, e₆⟩ := compactTopCallClr_exec body cp bc ds
        (j := 0) (u := q+1) (R₀ := R)
        (by simpa only [bits] using hfitT) (hcall (by omega)) Z v₅
        { S with R := R₅ } hL hpar hrest₅
        ((hR₅o .io (by simp) (by simp) (by simp) (by simp)).trans hio)
      have e₇ := Exec.cond_true (body := body) (f := (·.flag)) (q := uclear (reg .u))
        (show ({ v₁ with flag := true } : HS _ _ _ _).flag = true from rfl)
        (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))
      refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₁], ?_,
        Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₇)) rfl ?_⟩
      · unfold compactTopKerSCost
        simp only [bits, rowsAt] at hc₆
        omega
      · congr 2
        funext k
        by_cases h1 : k = reg .u
        · subst h1; simp [hT.hu]
        by_cases h2 : k = reg .a₀
        · subst h2; simp [hT.ha₀]
        by_cases h3 : k = reg .L
        · subst h3; simp [hT.hL]
        by_cases h4 : k = reg .rows
        · subst h4; simp [hT.hrows]
        by_cases h5 : k = reg .lev
        · subst h5; simp [hT.hlev]
        simp only [Function.update_apply, h1, h2, h3, h4, h5, ↓reduceIte]
        by_cases h6 : k = reg .io
        · simp [h6]; rfl
        · simp only [h6, ↓reduceIte, hR₅, hR₄, hR₃, hR₁, Function.update_apply, h1, h2, h3, h4]

end
end IntegerMultBounds.MathlibTM2.LayerMachine
