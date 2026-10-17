module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcRegs
public import IntegerMultBounds.MathlibTM2.Node.TopProc
import Mathlib.Tactic.Positivity.Finset

/-! Actual widening, phases, Gaussian unit multiplication and final shift for
arbitrary basis banks, preserving persistent basis-rest state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {BReg : Type} [Fintype BReg] {A Q : ℕ} {U P : Type}
variable {bc : BReg → List (Fin (A+4)) → Prop}
variable (body : P → Pr P (nT BReg) Q A U)

local macro "compactTopStagesFupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj,
  reduceCtorEq, ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.ph.injEq, LReg.lf.injEq,
  IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue]))


/-- Widening from the input width `w` (field `0`) to the working width `w'` (register `w`). -/
noncomputable def compactTopWidenS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 0)
  (.seq (ucopy (reg .w) (reg (.sc 1)) (reg .tS))
  (.seq (usub (reg (.sc 0)) (reg (.sc 1)) (reg .tS))
  (.seq (topPass (reg .io) (reg .racc)
      (topWidenWord (reg .io) (reg .racc) (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 3))))
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1)))))))

/-- The step bound of `compactTopWidenS`. -/
def compactTopWidenSCost (cfg : List ℕ) (R N r w w' : ℕ) : ℕ :=
  topGetCost cfg + (4 * w' + 4) + (4 * w + 4) + topWidenCost R N r w w' + (2 * w + 2) +
    (2 * (w' - w) + 2)

theorem compactTopWidenS_exec {cfg pfs : List ℕ} {R N r w w' K ρ : ℕ} (hcfg : cfg[0]? = some w)
    (hw : 1 ≤ w) (hww : w ≤ w') (Z : ZArr (Fin R × Fin r) N) (hZ : ∀ p, TopFitsZ w (Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ compactTopWidenSCost cfg R N r w w' ∧
      Exec body compactTopWidenS (mk v S) c
        (mk v' { S with R := Function.update S.R (reg .io) (encZ A w' Z) }) := by
  have hi : 0 < cfg.length := by
    rcases cfg with _ | ⟨x, l⟩
    · simp at hcfg
    · simp
  have hc0 : cfg[0] = w := by
    rw [List.getElem?_eq_getElem hi] at hcfg; exact Option.some.inj hcfg
  have hs0 : S.R (reg (.sc 0)) = [] := hT.rest (.sc 0)
  have hs1 : S.R (reg (.sc 1)) = [] := hT.rest (.sc 1)
  have hs3 : S.R (reg (.sc 3)) = [] := hT.rest (.sc 3)
  have htS : S.R (reg .tS) = [] := hT.rest .tS
  have hracc : S.R (reg .racc) = [] := hT.rest .racc
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 0 hi v S
    (hT.rest .lenctr) hI.cf
  rw [hc0, hs0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate w tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := ucopy_exec body (a := reg .w) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp [hR₁, htS])
  have hw₁ : (R₁ (reg .w)).length = w' := by simp [hR₁]; exact hT.hw
  have hs1' : R₁ (reg (.sc 1)) = [] := by simp [hR₁, hs1]
  dsimp only at e₂
  rw [hw₁, hs1', List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate w' tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  have h0₂ : R₂ (reg (.sc 0)) = List.replicate w tick := by simp [hR₂, hR₁]
  rw [h0₂, show R₂ (reg (.sc 1)) = List.replicate w' tick by simp [hR₂], List.length_replicate,
    List.drop_replicate] at e₃
  set R₃ := Function.update R₂ (reg (.sc 1)) (List.replicate (w' - w) tick) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := topWidenP_exec body (src := reg .io) (dst := reg .racc)
    (c₁ := reg (.sc 0)) (c₂ := reg (.sc 1)) (sp := reg (.sc 3))
    (nodup_map_reg (l := [.io, .racc, .sc 0, .sc 1, .sc 3]) (by simp)) hw hww Z hZ v₃
    { S with R := R₃ } (by simp [hR₃, hR₂, hR₁, hio]) (by simp [hR₃, hR₂, hR₁, hracc])
    ⟨by simp [hR₃, hR₂, hR₁], by simp [hR₃], by simp [hR₃, hR₂, hR₁, hs3]⟩
  set R₄ := Function.update R₃ (reg .io) (encZ A w' Z) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := uclear_exec body (reg (.sc 0)) v₄ { S with R := R₄ }
  obtain ⟨v₆, hu₆, e₆⟩ := uclear_exec body (reg (.sc 1)) v₅
    { S with R := Function.update R₄ (reg (.sc 0)) [] }
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆))))) rfl ?_⟩
  · simp only [hR₄, hR₃, hR₂, hR₁]
    compactTopStagesFupd
    simp only [List.length_replicate]
    unfold compactTopWidenSCost
    omega
  · congr 2
    funext k
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hs1]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hs0]
    simp [hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1]

/-- The phase stage: the strided mask of the selected bits `oS + ρ + K i`, `i < D` (fields `8`,
`9`) on `ph .msk`, the record count `R 2^N` (field `3`) on `ph .cnt`, `phaseProg` with `c = 1`
on `io`, and the scratch registers cleared. -/
noncomputable def compactTopPhaseS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 8)
  (.seq (uadd (reg .ρ) (reg (.sc 0)) (reg .tS))
  (.seq (compactTopRd (reg (.sc 1)) 9)
  (.seq (strideMask (reg .n) (reg (.sc 0)) (reg .K) (reg (.sc 1)) (reg (.ph .msk)) (reg (.sc 2))
      (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5)) 1 (fun _ => true))
  (.seq (compactTopRd (reg (.ph .cnt)) 3)
  (.seq (upow2 (reg .n) (reg (.ph .cnt)) (reg (.sc 4)) (reg (.sc 5)))
  (.seq (phaseProg (phMap (reg .io)) (reg .st) 1)
  (.seq (uclear (reg (.ph .msk))) (.seq (uclear (reg (.ph .cnt)))
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1))))))))))))

/-- The step bound of `compactTopPhaseS`. -/
def compactTopPhaseSCost (cfg : List ℕ) (N R r w K ρ oS D : ℕ) : ℕ :=
  3 * topGetCost cfg + (4 * ρ + 4) + (10 * N + 4 * (ρ + oS) + (D * (4 * K + 9) + 4) + 15) +
    (4 * (2 ^ N * R) + 9 * N + 4) + (R * 2 ^ N * (25 * r * w + 20 * N + 36) + 33) +
    (2 * N + 2) + (2 * (2 ^ N * R) + 2) + (2 * (ρ + oS) + 2) + (2 * D + 2)

theorem compactTopPhaseS_exec (hA : 5 ≤ A) {cfg pfs : List ℕ} {R N r w K ρ oS D : ℕ}
    (h3 : cfg[3]? = some R) (h8 : cfg[8]? = some oS) (h9 : cfg[9]? = some D)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K) (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ compactTopPhaseSCost cfg N R r w K ρ oS D ∧
      Exec body compactTopPhaseS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ A w (phaseZ (topMaskOf N ρ K oS D) 1 Z)) }) := by
  have hl3 : 3 < cfg.length := (List.getElem?_eq_some_iff.1 h3).1
  have hl8 : 8 < cfg.length := (List.getElem?_eq_some_iff.1 h8).1
  have hl9 : 9 < cfg.length := (List.getElem?_eq_some_iff.1 h9).1
  have hc3 : cfg[3] = R := (List.getElem?_eq_some_iff.1 h3).2
  have hc8 : cfg[8] = oS := (List.getElem?_eq_some_iff.1 h8).2
  have hc9 : cfg[9] = D := (List.getElem?_eq_some_iff.1 h9).2
  have hrest := hT.rest
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hrest (.sc i)
  have htS : S.R (reg .tS) = [] := hrest .tS
  have hlc : S.R (reg .lenctr) = [] := hrest .lenctr
  have hmsk : S.R (reg (.ph .msk)) = [] := hrest (.ph .msk)
  have hcnt : S.R (reg (.ph .cnt)) = [] := hrest (.ph .cnt)
  have hph : ∀ x, x ≠ PhaseReg.arr → phMap (reg (BReg := BReg) .io) x = reg (.ph x) :=
    fun x hx => phMap_of_ne _ hx
  -- `sc 0 := ρ + oS`
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 8 hl8 v S
    hlc hI.cf
  rw [hc8, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate oS tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := uadd_exec body (a := reg .ρ) (b := reg (.sc 0)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp [hR₁, htS])
  dsimp only at e₂
  rw [show (R₁ (reg .ρ)).length = ρ by simp [hR₁]; exact hT.hρ,
    show R₁ (reg (.sc 0)) = List.replicate oS tick by simp [hR₁],
    List.replicate_append_replicate] at e₂
  set R₂ := Function.update R₁ (reg (.sc 0)) (List.replicate (ρ + oS) tick) with hR₂
  -- `sc 1 := D`
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := compactTopRd_exec body (x := .sc 1) (by simp) (by simp) 9 hl9 v₂
    { S with R := R₂ } (by simp [hR₂, hR₁, hlc]) (by simpa [hR₂, hR₁] using hI.cf)
  dsimp only at e₃
  rw [hc9, show R₂ (reg (.sc 1)) = [] by simp [hR₂, hR₁, hsc], List.append_nil] at e₃
  set R₃ := Function.update R₂ (reg (.sc 1)) (List.replicate D tick) with hR₃
  -- the mask
  obtain ⟨v₄, m₄, hu₄, hm₄, e₄⟩ := strideMask_exec body (nR := reg .n) (oR := reg (.sc 0))
    (KR := reg .K) (kR := reg (.sc 1)) (z := reg (.ph .msk)) (cnt := reg (.sc 2))
    (w := reg (.sc 3)) (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5))
    (nodup_map_reg (l := [.n, .sc 0, .K, .sc 1, .ph .msk, .sc 2, .sc 3, .sc 4, .sc 5])
      (by simp)) 1 (fun _ => true) (n := N) (o := ρ + oS) (K := K) (k := D) v₃
    { S with R := R₃ } (by simp [hR₃, hR₂, hR₁]; exact hT.hn) (by simp [hR₃, hR₂])
    (by simp [hR₃, hR₂, hR₁]; exact hT.hK) (by simp [hR₃]) hK
    (by simp [hR₃, hR₂, hR₁, hsc]) (by simp [hR₃, hR₂, hR₁, hsc]) (by simp [hR₃, hR₂, hR₁, hsc])
    (by simp [hR₃, hR₂, hR₁, hsc])
  dsimp only at e₄
  rw [show R₃ (reg (.ph .msk)) = [] by simp [hR₃, hR₂, hR₁, hmsk], List.append_nil] at e₄
  set mnum := maskVal (ρ + oS) K D 1 (fun _ => true) with hmnum
  set R₄ := Function.update R₃ (reg (.ph .msk)) (binSyms N mnum) with hR₄
  -- the record count
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := compactTopRd_exec body (x := .ph .cnt) (by simp) (by simp) 3 hl3 v₄
    { S with R := R₄ } (by simp [hR₄, hR₃, hR₂, hR₁, hlc])
    (by simpa [hR₄, hR₃, hR₂, hR₁] using hI.cf)
  dsimp only at e₅
  rw [hc3, show R₄ (reg (.ph .cnt)) = [] by simp [hR₄, hR₃, hR₂, hR₁, hcnt], List.append_nil] at e₅
  set R₅ := Function.update R₄ (reg (.ph .cnt)) (List.replicate R tick) with hR₅
  obtain ⟨v₆, m₆, hu₆, hm₆, e₆⟩ := upow2_exec body (a := reg .n) (b := reg (.ph .cnt))
    (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5))
    (nodup_map_reg (l := [.n, .ph .cnt, .sc 4, .sc 5]) (by simp)) v₅ { S with R := R₅ }
    (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc]) (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc])
  dsimp only at e₆ hm₆
  have hn₅ : (R₅ (reg .n)).length = N := by simp [hR₅, hR₄, hR₃, hR₂, hR₁]; exact hT.hn
  have hc₅' : R₅ (reg (.ph .cnt)) = List.replicate R tick := by simp [hR₅]
  rw [hn₅, hc₅'] at e₆ hm₆
  set kk := (List.replicate R tick).flatMap (List.replicate (2 ^ N)) with hkk
  have hkkl : kk.length = R * 2 ^ N := by
    rw [hkk, length_flatMap_replicate, List.length_replicate, Nat.mul_comm]
  set R₆ := Function.update R₅ (reg (.ph .cnt)) kk with hR₆
  -- the phase
  have hR₆o : ∀ x : LReg BReg, x ≠ .sc 0 → x ≠ .sc 1 → x ≠ .ph .msk → x ≠ .ph .cnt →
      R₆ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3 h4
    simp [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, h1, h2, h3, h4]
  have hP : ∀ x, x ≠ PhaseReg.arr → x ≠ .msk → x ≠ .cnt →
      R₆ (phMap (reg .io) x) = S.R (reg (.ph x)) :=
    fun x h1 h2 h3 => by
      rw [hph x h1, hR₆o _ (by simp) (by simp) (by simpa using h2) (by simpa using h3)]
  obtain ⟨v₇, m₇, hu₇, hm₇, e₇⟩ := phaseProg_exec body
    (ρ := phMap (reg (BReg := BReg) .io)) (st := reg .st)
    (phMap_injective (fun x => reg_ne (by simp)))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        (rw [hph _ (by decide)]; exact reg_ne (by simp)))
    hA hr hw 1 (topMaskOf N ρ K oS D) mnum rfl Z
    (cs := R₆ (reg (.ph .rc))) (ws := R₆ (reg (.ph .wc))) (kk := R₆ (reg (.ph .cnt)))
    (by rw [hR₆o _ (by simp) (by simp) (by simp) (by simp)]; exact hrest (.ph .rc))
    (by rw [hR₆o _ (by simp) (by simp) (by simp) (by simp)]; exact hrest (.ph .wc))
    (by simp [hR₆, hkkl]) v₆ { S with R := R₆ }
    (by dsimp only; rw [phMap_arr, hR₆o _ (by simp) (by simp) (by simp) (by simp)]; exact hio)
    (fun q => by
      dsimp only; rw [hP _ (by simp) (by simp) (by simp)]; exact hrest (.ph (.cls q)))
    (by dsimp only; rw [hph _ (by decide)])
    (by dsimp only; rw [hph _ (by decide)])
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .tmp))
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .aux))
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .aux2))
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .af))
    (by dsimp only; rw [hph _ (by decide)]; simp [hR₆, hR₅, hR₄])
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .t0))
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .t1))
    (by dsimp only; rw [hph _ (by decide)])
  rw [phMap_arr] at e₇
  set X := encZ A w (phaseZ (topMaskOf N ρ K oS D) 1 Z)
  set R₇ := Function.update R₆ (reg .io) X with hR₇
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.ph .msk)) v₇ { S with R := R₇ }
  obtain ⟨v₉, hu₉, e₉⟩ := uclear_exec body (reg (.ph .cnt)) v₈
    { S with R := Function.update R₇ (reg (.ph .msk)) [] }
  obtain ⟨v₁₀, hu₁₀, e₁₀⟩ := uclear_exec body (reg (.sc 0)) v₉
    { S with R := Function.update (Function.update R₇ (reg (.ph .msk)) []) (reg (.ph .cnt)) [] }
  obtain ⟨v₁₁, hu₁₁, e₁₁⟩ := uclear_exec body (reg (.sc 1)) v₁₀
    { S with
      R := Function.update (Function.update (Function.update R₇ (reg (.ph .msk)) [])
        (reg (.ph .cnt)) []) (reg (.sc 0)) [] }
  refine ⟨v₁₁, _, by rw [hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ e₁₁)))))))))) rfl ?_⟩
  · have hm : (R₆ (reg (.ph .msk))).length = N := by simp [hR₆, hR₅, hR₄]
    have hk : (R₆ (reg (.ph .cnt))).length = R * 2 ^ N := by simp [hR₆, hkkl]
    have h0 : (R₆ (reg (.sc 0))).length = ρ + oS := by simp [hR₆, hR₅, hR₄, hR₃, hR₂]
    have h1 : (R₆ (reg (.sc 1))).length = D := by simp [hR₆, hR₅, hR₄, hR₃]
    have hρ' : (R₁ (reg .ρ)).length = ρ := by simp [hR₁]; exact hT.hρ
    simp only [hR₇]
    compactTopStagesFupd
    rw [hm, hk, h0, h1]
    unfold compactTopPhaseSCost
    simp only [List.length_replicate] at hm₆
    linarith [hc₁, hc₃, hc₅, hm₄, hm₆, hm₇]
  · congr 2
    funext k
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    by_cases h2 : k = reg (.ph .cnt)
    · subst h2; simp [hcnt]
    by_cases h3 : k = reg (.ph .msk)
    · subst h3; simp [hmsk]
    simp only [Function.update_apply, h0, h1, h2, h3, ↓reduceIte, hR₇]
    by_cases h4 : k = reg .io
    · simp [h4]
    · simp only [h4, ↓reduceIte, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1, h2,
        h3]

/-- Multiply every coefficient of `io` by the Gaussian integer `g` (through `racc`). -/
noncomputable def compactTopUnit (g : GaussianInt) : Pr P (nT BReg) Q A U :=
  .seq (autoWords (fun _ : Fin 1 => reg (BReg := BReg) .io) (fun _ => reg .racc) (reg .st)
      (reg .ctr) (reg .tmp) (gaussAuto A ![![(g.re, g.im)]] (g.re.natAbs + g.im.natAbs) false))
    (moveR (reg .racc) (reg .io) id)

/-- The step bound of `compactTopUnit` on an array of `R` rows of `2^n` records of `r` coefficients. -/
def compactTopUnitCost (R n r w : ℕ) : ℕ :=
  (R * 2 ^ n * r * (5 * w + 6) + 2) + (2 * (R * 2 ^ n * r * w) + 2)

/-- **The unit.** `io` holding the stream of `Z` ends holding the stream of `g Z`. -/
theorem compactTopUnit_exec (hA : 4 ≤ A) (g : GaussianInt)
    (hg : (2 * (g.re.natAbs + g.im.natAbs) + 1) ^ 2 ≤ A + 4) {R r n w : ℕ} (hw : 1 ≤ w)
    (Z : ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hracc : S.R (reg .racc) = []) (hctr : (S.R (reg .ctr)).length = w)
    (htmp : S.R (reg .tmp) = []) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ compactTopUnitCost R n r w ∧
      Exec body (compactTopUnit g) (mk v S) c
        (mk v' { S with R := Function.update S.R (reg .io) (encZ A w (fun p => g * Z p)) }) := by
  have hne : reg (BReg := BReg) .io ≠ reg .racc := reg_ne (by simp)
  obtain ⟨v₁, m₁, S₁, hu₁, hm₁, e₁, hi₁, ho₁, hl₁, hin₁, hout₁, hoth₁⟩ := mulG_exec body
    (autoLayout_one (x := .io) (y := .racc) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp)) g.re g.im hA hg hw (ctrs := S.R (reg .ctr)) hctr (coeffList w Z) v S rfl
    htmp hio
  have hX : ((coeffList w Z).map (GR.mulG g.re g.im)).flatMap (coeffSyms A w) =
      encZ A w (fun p => g * Z p) := by
    rw [encZ, topCoeffList_mul]
  rw [hX, hracc, List.append_nil] at hout₁
  obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body (reg .racc) (reg .io) hne.symm id v₁ S₁
  have hS₁ : S₁ = { S with R := S₁.R } := by
    cases S₁; cases S; simp_all
  rw [hS₁] at e₁ e₂
  refine ⟨v₂, m₁ + (2 * (S₁.R (reg .racc)).length + 2), hu₂.trans hu₁, ?_,
    Exec.seq e₁ (Exec.cast e₂ rfl ?_)⟩
  · have hlen : (S₁.R (reg .racc)).length = R * 2 ^ n * r * w := by
      rw [hout₁, List.length_reverse, topEnc_length]
    rw [length_coeffList] at hm₁
    rw [hlen]
    unfold compactTopUnitCost
    omega
  · congr 2
    funext k
    by_cases h1 : k = reg .io
    · subst h1
      have hin' : S₁.R (reg .io) = [] := by simpa using hin₁
      simp [movedR, hout₁, hin']
    by_cases h2 : k = reg .racc
    · subst h2; simp [movedR, hne.symm, hracc]
    simp only [movedR, Function.update_apply, h1, h2, ↓reduceIte]
    exact hoth₁ k h1 h2



/-- The unit stage: `D` (field `9`) modulo `8` into the scan slot `lev`, then the multiplication
by `unitD D` chosen by an eight-way dispatch. -/
noncomputable def compactTopUnitS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 9)
  (.seq (topResid 8 (reg (.sc 0)) (reg (.sc 3)) (reg .lev))
  (.seq (topDisp8 (reg .lev) (fun q => compactTopUnit (unitD q.val))) (uclear (reg (.sc 0)))))

/-- The step bound of `compactTopUnitS`. -/
def compactTopUnitSCost (cfg : List ℕ) (R N r w D : ℕ) : ℕ :=
  topGetCost cfg + (4 * D + 4) + (compactTopUnitCost R N r w + 7) + (2 * D + 2)

theorem compactTopUnitS_exec (hA : 21 ≤ A) {cfg pfs : List ℕ} {R N r w K ρ D : ℕ}
    (h9 : cfg[9]? = some D) (hw : 1 ≤ w) (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ compactTopUnitSCost cfg R N r w D ∧
      Exec body compactTopUnitS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (fun p => unitD D * Z p)) }) := by
  have hl9 : 9 < cfg.length := (List.getElem?_eq_some_iff.1 h9).1
  have hc9 : cfg[9] = D := (List.getElem?_eq_some_iff.1 h9).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 9 hl9 v S
    (hT.rest .lenctr) hI.cf
  rw [hc9, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate D tick) with hR₁
  obtain ⟨v₂, hu₂, hsc₂, e₂⟩ := topResid_exec body (W := 8) (by norm_num) (by omega)
    (i := reg (.sc 0)) (t := reg (.sc 3)) (reg_ne (by simp)) (reg .lev) v₁ { S with R := R₁ }
    (by simp [hR₁, hsc])
  simp only [hR₁, Function.update_self, List.length_replicate] at hsc₂ e₂
  have hg : (2 * ((unitD (D % 8)).re.natAbs + (unitD (D % 8)).im.natAbs) + 1) ^ 2 ≤ A + 4 := by
    have := topUnitD_bound (D % 8)
    have h25 : (2 * ((unitD (D % 8)).re.natAbs + (unitD (D % 8)).im.natAbs) + 1) ^ 2 ≤
        5 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := compactTopUnit_exec body (by omega) (unitD (D % 8)) hg hw Z v₂
    { S with R := R₁ } (by have h : S.R (reg .racc) = [] := hT.rest .racc; simp [hR₁, h])
    (by simp [hR₁]; exact hT.rest .ctr)
    (by have h : S.R (reg .tmp) = [] := hT.rest .tmp; simp [hR₁, h]) (by simp [hR₁, hio])
  obtain ⟨c₃', hc₃', e₃'⟩ := topDisp8_exec body (reg .lev) (fun q => compactTopUnit (unitD q.val))
    ⟨D % 8, Nat.mod_lt _ (by norm_num)⟩ v₂ { S with R := R₁ } hsc₂ e₃
  rw [← topUnitD_mod] at e₃'
  set R₃ := Function.update R₁ (reg .io) (encZ A w (fun p => unitD D * Z p)) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := uclear_exec body (reg (.sc 0)) v₃ { S with R := R₃ }
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃' e₄))) rfl ?_⟩
  · simp only [hR₃, hR₁]
    compactTopStagesFupd
    simp only [List.length_replicate]
    unfold compactTopUnitSCost
    omega
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    simp [hR₃, hR₁, Function.update_apply, h0]

/-- The shift stage: `s` (field `1`), `w` (field `0`) and `w' - s - w` on `sc 0`, `sc 1`,
`sc 2`; the truncating shift pass (spares `racc`, `rctmp`, `sc 3`, `sc 4`, `sc 5`). -/
noncomputable def compactTopShiftS : Pr P (nT BReg) Q A U :=
  .seq (compactTopRd (reg (.sc 0)) 1)
  (.seq (compactTopRd (reg (.sc 1)) 0)
  (.seq (ucopy (reg .w) (reg (.sc 2)) (reg .tS))
  (.seq (usub (reg (.sc 0)) (reg (.sc 2)) (reg .tS))
  (.seq (usub (reg (.sc 1)) (reg (.sc 2)) (reg .tS))
  (.seq (topPass (reg .io) (reg .rctmp) (topShiftWord (reg .io) (reg .rctmp) (reg .racc) (reg .w)
      (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5))))
  (.seq (uclear (reg (.sc 0))) (.seq (uclear (reg (.sc 1))) (uclear (reg (.sc 2))))))))))

/-- The step bound of `compactTopShiftS`. -/
def compactTopShiftSCost (cfg : List ℕ) (R N r w' s w : ℕ) : ℕ :=
  2 * topGetCost cfg + (4 * w' + 4) + (4 * s + 4) + (4 * w + 4) + topShiftCost R N r w' s w +
    (2 * s + 2) + (2 * w + 2) + (2 * (w' - s - w) + 2)

theorem compactTopShiftS_exec (hA : 4 ≤ A) {cfg pfs : List ℕ} {R N r w' K ρ s w : ℕ}
    (h0 : cfg[0]? = some w) (h1 : cfg[1]? = some s) (hw' : 1 ≤ w') (hsw : s + w ≤ w')
    (Z : ZArr (Fin R × Fin r) N) (hZ : ∀ p, TopFitsZ w' (Z p))
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hT : CompactTopRegs bc S.R N r w' K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io) = encZ A w' Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ compactTopShiftSCost cfg R N r w' s w ∧
      Exec body compactTopShiftS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (fun p => tdivZ s (Z p))) }) := by
  have hl0 : 0 < cfg.length := (List.getElem?_eq_some_iff.1 h0).1
  have hl1 : 1 < cfg.length := (List.getElem?_eq_some_iff.1 h1).1
  have hc0 : cfg[0] = w := (List.getElem?_eq_some_iff.1 h0).2
  have hc1 : cfg[1] = s := (List.getElem?_eq_some_iff.1 h1).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have htS : S.R (reg .tS) = [] := hT.rest .tS
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := compactTopRd_exec body (x := .sc 0) (by simp) (by simp) 1 hl1 v S
    hlc hI.cf
  rw [hc1, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate s tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := compactTopRd_exec body (x := .sc 1) (by simp) (by simp) 0 hl0 v₁
    { S with R := R₁ } (by simp [hR₁, hlc]) (by simpa [hR₁] using hI.cf)
  dsimp only at e₂
  rw [hc0, show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate w tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := ucopy_exec body (a := reg .w) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  rw [show (R₂ (reg .w)).length = w' by simp [hR₂, hR₁]; exact hT.hw,
    show R₂ (reg (.sc 2)) = [] by simp [hR₂, hR₁, hsc], List.append_nil] at e₃
  set R₃ := Function.update R₂ (reg (.sc 2)) (List.replicate w' tick) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃ { S with R := R₃ }
    (by simp [hR₃, hR₂, hR₁, htS])
  dsimp only at e₄
  rw [show R₃ (reg (.sc 0)) = List.replicate s tick by simp [hR₃, hR₂, hR₁],
    show R₃ (reg (.sc 2)) = List.replicate w' tick by simp [hR₃], List.length_replicate,
    List.drop_replicate] at e₄
  set R₄ := Function.update R₃ (reg (.sc 2)) (List.replicate (w' - s) tick) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := usub_exec body (a := reg (.sc 1)) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄ { S with R := R₄ }
    (by simp [hR₄, hR₃, hR₂, hR₁, htS])
  dsimp only at e₅
  rw [show R₄ (reg (.sc 1)) = List.replicate w tick by simp [hR₄, hR₃, hR₂],
    show R₄ (reg (.sc 2)) = List.replicate (w' - s) tick by simp [hR₄], List.length_replicate,
    List.drop_replicate] at e₅
  set R₅ := Function.update R₄ (reg (.sc 2)) (List.replicate (w' - s - w) tick) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := topShiftP_exec body hA (src := reg .io) (dst := reg .rctmp)
    (tmp := reg .racc) (cW := reg .w) (cS := reg (.sc 0)) (cE := reg (.sc 1)) (cD := reg (.sc 2))
    (sp := reg (.sc 3)) (sg := reg (.sc 4)) (cy := reg (.sc 5))
    (nodup_map_reg (l := [.io, .rctmp, .racc, .w, .sc 0, .sc 1, .sc 2, .sc 3, .sc 4, .sc 5])
      (by simp)) hw' hsw Z hZ v₅ { S with R := R₅ }
    (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hio])
    (by have h : S.R (reg .rctmp) = [] := hT.rest .rctmp; simp [hR₅, hR₄, hR₃, hR₂, hR₁, h])
    ⟨by simp [hR₅, hR₄, hR₃, hR₂, hR₁]; exact hT.hw, by simp [hR₅, hR₄, hR₃, hR₂, hR₁],
      by simp [hR₅, hR₄, hR₃, hR₂], by simp [hR₅], by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc],
      by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc], by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc],
      by have h : S.R (reg .racc) = [] := hT.rest .racc; simp [hR₅, hR₄, hR₃, hR₂, hR₁, h]⟩
  set R₆ := Function.update R₅ (reg .io) (encZ A w (fun p => tdivZ s (Z p))) with hR₆
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 0)) v₆ { S with R := R₆ }
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.sc 1)) v₇
    { S with R := Function.update R₆ (reg (.sc 0)) [] }
  obtain ⟨v₉, hu₉, e₉⟩ := uclear_exec body (reg (.sc 2)) v₈
    { S with R := Function.update (Function.update R₆ (reg (.sc 0)) []) (reg (.sc 1)) [] }
  refine ⟨v₉, _, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ e₉)))))))) rfl ?_⟩
  · simp only [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁]
    compactTopStagesFupd
    simp only [List.length_replicate]
    unfold compactTopShiftSCost
    omega
  · congr 2
    funext k
    by_cases h2 : k = reg (.sc 2)
    · subst h2; simp [hsc]
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    simp [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1, h2]


end
end IntegerMultBounds.MathlibTM2.LayerMachine
