module

public import IntegerMultBounds.Schoenhage.TransformDriver
public import IntegerMultBounds.Schoenhage.BankWrap

/-! The transform drivers in the paper's bank format (§6). The word bank is the paper's four tapes
followed by the drivers' bank (`wst`). A generator from the header writes the round script, the
layout script and the drivers' constants (`FwdGen`, `OppGen`, hypotheses here); the input array is
copied to the drivers' array tape, the driver runs, the drivers' bank is cleared (`cleanD`) and the
result moved to the output tape (`fwdCore`, `oppCore`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct Resampling AxisDriver LayoutMachines
open Networks.Shared50ModularControl (prime)

variable {A tL nL : ℕ}

/-- Clear the drivers' bank except the array. -/
noncomputable def cleanD (A tL nL : ℕ) : Cmd A (DB tL nL) :=
  .seq (clear (nm tL nL 2)) <| .seq (clear (nm tL nL 6)) <| .seq (clear (nm tL nL 7)) <|
  .seq (clear (twT tL nL 3)) <| .seq (clear (twT tL nL 15)) <| .seq (clear (twT tL nL 17)) <|
  .seq (clear (twT tL nL 22)) <| .seq (clear (twT tL nL 23)) <| .seq (clear (twT tL nL 24))
    (clear (twT tL nL 25))

/-- Only the array on the named tapes. -/
def only0 (X : List Bool) : Fin 13 → WTape := fun i => if i = 0 then reg X else emp

theorem dstate_emp : dstate tL nL (fun _ => emp) (fun _ => emp) = fun _ => emp := by
  funext x; simp only [dstate]; split_ifs <;> rfl

set_option maxHeartbeats 8000000 in
theorem runs_cleanD (w : ℕ) (X : List Bool) (S6 S7 : WTape) (r n M : ℕ) :
    Runs (cleanD A tL nL) (dstate tL nL (rnamed w X S6 S7) (twRest r n M))
      (· = dstate tL nL (only0 X) (fun _ => emp))
      (2 * (clen S6.words + clen S7.words) + 2 * w + 2 * n + 2 * M + 40 * r + 60) := by
  set v := rnamed w X S6 S7
  set tw := twRest r n M
  have s1 := runs_clear (a := A) (nm tL nL 2) (dstate tL nL v tw); rw [update_nm] at s1
  have s2 := runs_clear (a := A) (nm tL nL 6) (dstate tL nL (Function.update v 2 ⟨[], []⟩) tw)
  rw [update_nm] at s2
  set v2 := Function.update (Function.update v 2 ⟨[], []⟩) 6 ⟨[], []⟩
  have s3 := runs_clear (a := A) (nm tL nL 7) (dstate tL nL v2 tw); rw [update_nm] at s3
  set v3 := Function.update v2 7 ⟨[], []⟩
  have s4 := runs_clear (a := A) (twT tL nL 3) (dstate tL nL v3 tw); rw [update_tw] at s4
  set t4' := Function.update tw 3 ⟨[], []⟩
  have s5 := runs_clear (a := A) (twT tL nL 15) (dstate tL nL v3 t4'); rw [update_tw] at s5
  set t5 := Function.update t4' 15 ⟨[], []⟩
  have s6 := runs_clear (a := A) (twT tL nL 17) (dstate tL nL v3 t5); rw [update_tw] at s6
  set t6 := Function.update t5 17 ⟨[], []⟩
  have s7 := runs_clear (a := A) (twT tL nL 22) (dstate tL nL v3 t6); rw [update_tw] at s7
  set t7 := Function.update t6 22 ⟨[], []⟩
  have s8 := runs_clear (a := A) (twT tL nL 23) (dstate tL nL v3 t7); rw [update_tw] at s8
  set t8 := Function.update t7 23 ⟨[], []⟩
  have s9 := runs_clear (a := A) (twT tL nL 24) (dstate tL nL v3 t8); rw [update_tw] at s9
  set t9 := Function.update t8 24 ⟨[], []⟩
  have s10 := runs_clear (a := A) (twT tL nL 25) (dstate tL nL v3 t9); rw [update_tw] at s10
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 (Runs.then s9 s10))))))))).mono (fun τ h => ?_) ?_
  · rw [h]
    congr 1
    · funext i
      fin_cases i <;> simp (config := {decide := true}) [v3, v2, v, rnamed, only0, emp]
    · funext j
      fin_cases j <;> simp (config := {decide := true}) [t9, t8, t7, t6, t5, t4', tw, twRest, 
        emp]
  · simp (config := {decide := true}) only [dstate_nm, dstate_twT, v3, v2, v, rnamed, t9, t8, t7, t6, t5, t4', tw,
      twRest, Function.update_apply, ite_true, ite_false, reg, WTape.words, List.reverse_nil, List.nil_append,
      clen_cons, clen_nil, length_ones, TwistDescriptors.clen_replicate_nil', length_bits]
    omega

/-! ### The word bank: the paper's four tapes, then the drivers' bank -/

/-- The paper's tapes `s`, then the drivers' bank `τ`. -/
def wst (s : Fin 4 → WTape) (τ : Fin (DB tL nL) → WTape) : Fin (4 + DB tL nL) → WTape := Fin.addCases s τ

/-- The drivers' bank inside the word bank. -/
def drv (tL nL : ℕ) : Fin (DB tL nL) → Fin (4 + DB tL nL) := Fin.natAdd 4

theorem drv_injective : Function.Injective (drv tL nL) := fun a b h => by
  have := congrArg Fin.val h; simp [drv] at this; exact Fin.ext this

/-- Paper tape `i` inside the word bank. -/
def pt (tL nL : ℕ) (i : Fin 4) : Fin (4 + DB tL nL) := Fin.castAdd _ i

theorem wst_comp_drv (s : Fin 4 → WTape) (τ : Fin (DB tL nL) → WTape) : wst s τ ∘ drv tL nL = τ := by
  funext x; simp [wst, drv]

theorem wst_drv (s : Fin 4 → WTape) (τ : Fin (DB tL nL) → WTape) (x : Fin (DB tL nL)) :
    wst s τ (drv tL nL x) = τ x := by simp [wst, drv]

theorem wst_pt (s : Fin 4 → WTape) (τ : Fin (DB tL nL) → WTape) (i : Fin 4) : wst s τ (pt tL nL i) = s i := by
  simp [wst, pt]

theorem update_wst_drv (s : Fin 4 → WTape) (τ : Fin (DB tL nL) → WTape) (x : Fin (DB tL nL)) (u : WTape) :
    Function.update (wst s τ) (drv tL nL x) u = wst s (Function.update τ x u) := by
  funext y
  refine Fin.addCases (fun i => ?_) (fun j => ?_) y
  · rw [Function.update_of_ne (fun e => by simp [drv, Fin.ext_iff] at e; omega)]
    simp [wst]
  · by_cases h : j = x
    · subst h; simp [wst, drv]
    · rw [Function.update_of_ne (show (Fin.natAdd 4 j : Fin (4 + DB tL nL)) ≠ drv tL nL x from
        fun e => h (drv_injective e))]
      simp [wst, Function.update_of_ne h]

theorem update_wst_pt (s : Fin 4 → WTape) (τ : Fin (DB tL nL) → WTape) (i : Fin 4) (u : WTape) :
    Function.update (wst s τ) (pt tL nL i) u = wst (Function.update s i u) τ := by
  funext y
  refine Fin.addCases (fun k => ?_) (fun j => ?_) y
  · by_cases h : k = i
    · subst h; simp [wst, pt]
    · rw [Function.update_of_ne (show (Fin.castAdd (DB tL nL) k : Fin (4 + DB tL nL)) ≠ pt tL nL i from
        fun e => h (Fin.ext (by have := congrArg Fin.val e; simpa [pt] using this)))]
      simp [wst, Function.update_of_ne h]
  · rw [Function.update_of_ne (fun e => by simp [pt, Fin.ext_iff] at e; omega)]
    simp [wst]

theorem w4_eq (hdr F : List Bool) (o : WTape) :
    w4 (4 + DB tL nL) hdr F o = wst ![reg hdr, reg F, emp, o] (fun _ => emp) := by
  funext y
  refine Fin.addCases (fun k => ?_) (fun j => ?_) y
  · fin_cases k <;> simp [w4, wst]
  · have h0 : (Fin.natAdd 4 j : Fin (4 + DB tL nL)).val ≠ 0 := by simp
    have h1 : (Fin.natAdd 4 j : Fin (4 + DB tL nL)).val ≠ 1 := by simp; omega
    have h3 : (Fin.natAdd 4 j : Fin (4 + DB tL nL)).val ≠ 3 := by simp; omega
    simp only [w4, h0, h1, h3, ite_false]
    simp [wst]

theorem pt_ne_drv (i : Fin 4) (x : Fin (DB tL nL)) : pt tL nL i ≠ drv tL nL x := fun e => by
  have := congrArg Fin.val e; simp [pt, drv] at this; omega

theorem rnamed_update0 (w : ℕ) (X : List Bool) (S6 S7 : WTape) :
    Function.update (Function.update (rnamed w [] S6 S7) 0 emp) 0 (reg X) = rnamed w X S6 S7 := by
  funext i; fin_cases i <;> simp (config := {decide := true}) [rnamed]

theorem only0_update0 (X : List Bool) : Function.update (only0 X) 0 emp = fun _ => emp := by
  funext i; fin_cases i <;> simp (config := {decide := true}) [only0]

variable {r : ℕ} [NeZero r]

/-- The forward generator's output on the drivers' bank: `fwdStart` without the array. -/
noncomputable def fwdGenOut {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w : ℕ) :
    Fin (DB tL NL) → WTape :=
  dstate tL NL (Function.update (rnamed w [] ⟨[], fwdScript p d r w (paperPerm hL) ts ℓ K⟩
    ⟨[], layoutWords r w ts ℓ K⟩) 0 emp) (rest r ts)

/-- The opposite generator's output on the drivers' bank: `oppStart` without the array. -/
noncomputable def oppGenOut {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w : ℕ) :
    Fin (DB tL NL) → WTape :=
  dstate tL NL (Function.update (rnamed w [] ⟨[], oppScript p d r w (paperPerm hL) ts ℓ K⟩
    ⟨[], undoWords r w ts ℓ K⟩) 0 emp) (rest r ts)

/-- A generator writes, from the header on paper tape 0, the drivers' bank for the forward driver
within `B` steps, whatever the input on paper tape 1. -/
def FwdGen (gen : Cmd A (4 + DB tL NL)) {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w : ℕ)
    (B : ℕ) : Prop :=
  ∀ F : List Bool, Runs gen (wst ![reg (transformHeader p d r K w ts), reg F, emp, emp] (fun _ => emp))
    (· = wst ![reg (transformHeader p d r K w ts), reg F, emp, emp] (fwdGenOut hL p d w)) B

/-- The same for the opposite driver. -/
def OppGen (gen : Cmd A (4 + DB tL NL)) {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w : ℕ)
    (B : ℕ) : Prop :=
  ∀ F : List Bool, Runs gen (wst ![reg (transformHeader p d r K w ts), reg F, emp, emp] (fun _ => emp))
    (· = wst ![reg (transformHeader p d r K w ts), reg F, emp, emp] (oppGenOut hL p d w)) B

/-- Generate, copy the input to the drivers' array, run the driver `D`, clear the drivers' bank, move
the result to the output tape. -/
noncomputable def coreOf (gen : Cmd A (4 + DB tL NL)) (D : Cmd A (DB tL NL)) : Cmd A (4 + DB tL NL) :=
  .seq gen <| .seq (regIn (pt tL NL 1) (drv tL NL (nm tL NL 0)) (pt_ne_drv _ _)) <|
  .seq (rewind (pt tL NL 1)) <| .seq ((Cmd.seq D (cleanD A tL NL)).map (drv tL NL) drv_injective) <|
  regMove (drv tL NL (nm tL NL 0)) (pt tL NL 3) (fun e => pt_ne_drv _ _ e.symm)

set_option maxHeartbeats 8000000 in
/-- `coreOf` from the paper's start tapes, given the generator and a driver run ending with the
result `G` in the drivers' end state. -/
theorem runs_coreOf (gen : Cmd A (4 + DB tL NL)) (D : Cmd A (DB tL NL)) {hdr F G : List Bool}
    {w : ℕ} {S6 S7 S6' S7' : WTape} {n M Bg kD : ℕ}
    (hgen : Runs gen (wst ![reg hdr, reg F, emp, emp] (fun _ => emp))
      (· = wst ![reg hdr, reg F, emp, emp]
        (dstate tL NL (Function.update (rnamed w [] S6 S7) 0 emp) (twRest r n M))) Bg)
    (hD : Runs D (dstate tL NL (rnamed w F S6 S7) (twRest r n M))
      (· = dstate tL NL (rnamed w G S6' S7') (twRest r n M)) kD) :
    Runs (coreOf gen D) (w4 (4 + DB tL NL) hdr F emp) (· = w4 (4 + DB tL NL) hdr F (reg G))
      (Bg + kD + 2 * (clen S6'.words + clen S7'.words) + 2 * w + 2 * n + 2 * M + 40 * r + 3 * F.length +
        4 * G.length + 120) := by
  set S0 : Fin 4 → WTape := ![reg hdr, reg F, emp, emp]
  rw [w4_eq, w4_eq]
  have s2 := runs_regIn (a := A) (pt_ne_drv (tL := tL) (nL := NL) 1 (nm tL NL 0))
    (wst S0 (dstate tL NL (Function.update (rnamed w [] S6 S7) 0 emp) (twRest r n M)))
    (L := []) (R := []) (w := F) (by rw [wst_pt]; rfl) (by rw [wst_drv, dstate_nm]; simp)
  rw [update_wst_pt, update_wst_drv, update_nm, rnamed_update0] at s2
  have s3 := runs_rewind (a := A) (pt tL NL 1)
    (wst (Function.update S0 1 ⟨[F], []⟩) (dstate tL NL (rnamed w F S6 S7) (twRest r n M)))
  rw [update_wst_pt, wst_pt] at s3
  have hS : Function.update (Function.update S0 1 ⟨[F], []⟩) 1
      ⟨[], (Function.update S0 1 (⟨[F], []⟩ : WTape) 1).left.reverse ++
        (Function.update S0 1 (⟨[F], []⟩ : WTape) 1).right⟩ = S0 := by
    funext i; fin_cases i <;> simp [S0, reg]
  rw [hS] at s3
  have sD := Runs.then hD (runs_cleanD (A := A) w G S6' S7' r n M)
  have s4 := TwistDescriptors.Runs.map_eq (drv tL NL) drv_injective (τ := wst S0 (dstate tL NL (rnamed w F S6 S7) (twRest r n M)))
    (c := Cmd.seq D (cleanD A tL NL)) (by rw [wst_comp_drv]; exact sD)
    (wst S0 (dstate tL NL (only0 G) (fun _ => emp))) (wst_comp_drv _ _) (fun x hx => by
      refine Fin.addCases (motive := fun x => (∀ y, drv tL NL y ≠ x) →
        wst S0 (dstate tL NL (only0 G) (fun _ => emp)) x = wst S0 (dstate tL NL (rnamed w F S6 S7) (twRest r n M)) x)
        (fun i _ => by simp [wst]) (fun j hj => absurd rfl (hj j)) x hx)
  have s5 := runs_regMove (a := A) (fun e => pt_ne_drv (tL := tL) (nL := NL) 3 (nm tL NL 0) e.symm)
    (wst S0 (dstate tL NL (only0 G) (fun _ => emp))) (w := G)
    (by rw [wst_drv, dstate_nm]; simp [only0]) (by rw [wst_pt]; rfl)
  rw [update_wst_drv, update_nm, only0_update0, dstate_emp, update_wst_pt] at s5
  refine (Runs.then hgen (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ h => ?_) ?_
  · rw [h]
    congr 1
    funext i; fin_cases i <;> simp [S0]
  · simp only [S0, Function.update_apply, reg, WTape.words, clen_cons, clen_nil, List.reverse_nil,
      List.nil_append, List.reverse_cons, List.append_nil, Matrix.cons_val_one, 
      ite_true] at *
    simp
    omega

theorem four_le_wb : 4 ≤ 4 + DB tL nL := by omega

/-- The forward transform program in the paper's format. -/
noncomputable def fwdProg (gen : Cmd A (4 + DB tL NL)) {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    (hP : prime ≤ A) :=
  wrapProg (coreOf gen (fwdDriver M ht haA hP)) four_le_wb

/-- The opposite transform program in the paper's format. -/
noncomputable def oppProg (gen : Cmd A (4 + DB tL NL)) {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    (hP : prime ≤ A) :=
  wrapProg (coreOf gen (oppDriver M ht haA hP)) four_le_wb

/-- The step bound of the forward program beyond the generator and the rounds. -/
noncomputable def wrapCost (r w : ℕ) (ts : List ℕ) (ℓ K : ℕ) (hdr : List Bool) (S6 S7 : List (List Bool)) : ℕ :=
  layoutCost r w ts ℓ K + 2 * (clen S6 + clen S7) + 2 * w + 2 * Nat.log 2 ts.prod + 2 * 2 ^ Nat.log 2 ts.prod +
    40 * r + 4 * hdr.length + 15 * (2 * r * w * ts.prod) + 200

set_option maxHeartbeats 8000000 in
/-- `fwd_bank`: the forward program meets the forward transform's contract in the paper's format. -/
theorem fwd_bank (gen : Cmd A (4 + DB tL NL)) {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    (hP : prime ≤ A) {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL Bg : ℕ} (hpw : p + 2 ≤ w)
    (hgen : FwdGen gen hL p d w Bg) (hLayer : LayerCalls M ht r p d w ts ℓ K CL) (fs : List (Rec r))
    (hfl : fs.length = ts.prod) (hfd : ∀ f ∈ fs, DiskGrid p f.1 f.2) :
    ∃ (gs : List (Rec r)) (k : ℕ), gs.length = ts.prod ∧ (∀ g ∈ gs, DiskGrid p g.1 g.2) ∧
      Close ts.prod (arrayVec p gs)
        (fwdExact ts ((paperPerm hL).toPerm (powAxes_prod_pow hL.1)) (arrayVec p fs)) (Real.sqrt 2 * ℓ / 2 ^ p) ∧
      k ≤ Bg + fwdRoundsCost hL p d w CL + wrapCost r w ts ℓ K (transformHeader p d r K w ts)
        (fwdScript p d r w (paperPerm hL) ts ℓ K) (layoutWords r w ts ℓ K) ∧
      HoareTime (fwdProg gen M ht haA hP) (· = bank (transformHeader p d r K w ts) (array w fs) [] [])
        (· = bank (transformHeader p d r K w ts) (array w fs) [] (array w gs)) k := by
  obtain ⟨σd, kd, hxd, ⟨gs, hgl, hgd, hcl, rfl⟩, hkd⟩ := runs_fwdDriver M ht haA hP hL hpw hLayer fs hfl hfd
  have hc := runs_coreOf (r := r) gen (fwdDriver M ht haA hP) (hgen (array w fs)) ⟨_, kd, hxd, rfl, le_rfl⟩
  refine ⟨gs, _, hgl, hgd, hcl, ?_, wrapProg_hoare _ four_le_wb hc⟩
  have h1 : (array w fs).length = 2 * r * w * ts.prod := by rw [length_array, hfl]
  have h2 : (array w gs).length = 2 * r * w * ts.prod := by rw [length_array, hgl]
  simp only [wrapCost, WTape.words, List.reverse_reverse, List.append_nil, 
    h1, h2] at hkd ⊢
  omega

set_option maxHeartbeats 8000000 in
/-- `opp_bank`: the opposite program meets the opposite transform's contract in the paper's format. -/
theorem opp_bank (gen : Cmd A (4 + DB tL NL)) {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    (hP : prime ≤ A) {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL Bg : ℕ} (hpw : p + 2 ≤ w)
    (hgen : OppGen gen hL p d w Bg) (hLayer : LayerCalls M ht r p d w ts ℓ K CL) (us : List (Rec r))
    (hul : us.length = ts.prod) (hud : ∀ u ∈ us, DiskGrid p u.1 u.2) :
    ∃ (gs : List (Rec r)) (k : ℕ), gs.length = ts.prod ∧ (∀ g ∈ gs, DiskGrid p g.1 g.2) ∧
      Close ts.prod (arrayVec p gs)
        (oppExact ts ((paperPerm hL).toPerm (powAxes_prod_pow hL.1)) (arrayVec p us)) (Real.sqrt 2 * ℓ / 2 ^ p) ∧
      k ≤ Bg + oppRoundsCost hL p d w CL + wrapCost r w ts ℓ K (transformHeader p d r K w ts)
        (oppScript p d r w (paperPerm hL) ts ℓ K) (undoWords r w ts ℓ K) ∧
      HoareTime (oppProg gen M ht haA hP) (· = bank (transformHeader p d r K w ts) (array w us) [] [])
        (· = bank (transformHeader p d r K w ts) (array w us) [] (array w gs)) k := by
  obtain ⟨σd, kd, hxd, ⟨gs, hgl, hgd, hcl, rfl⟩, hkd⟩ := runs_oppDriver M ht haA hP hL hpw hLayer us hul hud
  have hc := runs_coreOf (r := r) gen (oppDriver M ht haA hP) (hgen (array w us)) ⟨_, kd, hxd, rfl, le_rfl⟩
  refine ⟨gs, _, hgl, hgd, hcl, ?_, wrapProg_hoare _ four_le_wb hc⟩
  have h1 : (array w us).length = 2 * r * w * ts.prod := by rw [length_array, hul]
  have h2 : (array w gs).length = 2 * r * w * ts.prod := by rw [length_array, hgl]
  simp only [wrapCost, WTape.words, List.reverse_reverse, List.append_nil, 
    h1, h2] at hkd ⊢
  omega

end IntegerMultBounds.Schoenhage
