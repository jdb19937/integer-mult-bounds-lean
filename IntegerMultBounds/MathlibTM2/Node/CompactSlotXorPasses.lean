module

public import IntegerMultBounds.MathlibTM2.Node.CompactTiling

/-!
# The passes of the compact slot XOR on the built registers

The key pass, the interchanges, the prepared rotations, the compact repair and the fix pass, each
run on the register file after the setup (`cxFill … 37`), with the stream register `src` holding
the records and the rotation's computed register `comp` free.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor
  IntegerMultBounds.MathlibTM2.Layer.CompactXor

section Passes

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable {ι : CXReg → Fin T} {par : CXPar → Fin T} {src st : Fin T} {d : CxD}

/-- The register file during the passes: the built file over `R₁`, except at `comp`. -/
def CxState (ι : CXReg → Fin T) (d : CxD) (R₁ S : Fin T → List (Fin (A + 4))) : Prop :=
  ∀ k, k ≠ ι .comp → S k = cxFill ι (cxBc A d) 37 R₁ k

lemma CxState.fill_ι (henv : CxEnv ι par src) {R₁ S : Fin T → List (Fin (A + 4))}
    (h : CxState ι d R₁ S) (x : CXReg) (hx : x ≠ .comp) : S (ι x) = cxBc A d x := by
  rw [h _ (henv.ne hx), cxFill_ι henv.hι, if_pos (cxStage_le x)]

lemma CxState.srcVal (henv : CxEnv ι par src) {R₁ S : Fin T → List (Fin (A + 4))}
    (h : CxState ι d R₁ S) : S src = R₁ src := by
  rw [h _ (henv.hsrc _).symm, cxFill_out _ _ _ henv.hsrc]

lemma CxState.parVal (henv : CxEnv ι par src) {R₁ S : Fin T → List (Fin (A + 4))}
    (h : CxState ι d R₁ S) (p : CXPar) : S (par p) = R₁ (par p) := by
  rw [h _ (henv.hpι' _ _), cxFill_out _ _ _ (fun x => henv.hpι x p)]

lemma CxState.update_src (henv : CxEnv ι par src) {R₁ S : Fin T → List (Fin (A + 4))}
    (h : CxState ι d R₁ S) (X : List (Fin (A + 4))) :
    CxState ι d (Function.update R₁ src X) (Function.update S src X) := by
  intro k hk
  rw [← cxFill_update henv.hι _ _ _ henv.hsrc]
  by_cases hks : k = src
  · subst hks; simp
  · rw [Function.update_of_ne hks, Function.update_of_ne hks, h k hk]

lemma CxState.update_comp {R₁ S : Fin T → List (Fin (A + 4))}
    (h : CxState ι d R₁ S) (C : List (Fin (A + 4))) :
    CxState ι d R₁ (Function.update S (ι .comp) C) := by
  intro k hk
  rw [Function.update_of_ne hk, h k hk]

set_option hygiene false in
/-- Distinctness of named registers. -/
macro "cxne'" : tactic => `(tactic| first
  | exact henv.ne (by simp [Fin.ext_iff])
  | exact henv.hpι _ _
  | exact henv.hpι' _ _
  | exact henv.hpar.ne (by simp)
  | exact henv.hsrc _
  | exact (henv.hsrc _).symm
  | exact henv.hsrcp _
  | exact (henv.hsrcp _).symm)

/-! ### The key pass -/

/-- A list without duplicates followed by an injective family disjoint from it. -/
lemma nodup_append_ofFn {m : ℕ} {l : List (Fin T)} {f : Fin m → Fin T} (hl : l.Nodup)
    (hf : Function.Injective f) (h : ∀ a ∈ l, ∀ j, f j ≠ a) : (l ++ List.ofFn f).Nodup :=
  List.nodup_append.2 ⟨hl, List.nodup_ofFn.2 hf, fun a ha b hb => by
    rw [List.mem_ofFn] at hb
    obtain ⟨j, rfl⟩ := hb
    exact (h _ ha j).symm⟩

/-- The key pass of the machine. -/
noncomputable def cxKeyPass (ι : CXReg → Fin T) (d : CxD) (src st : Fin T) : Pr P T Q A U :=
  keyPassAt d.kY d.kX src (ι (.sx .kacc)) (ι (.sx .ctrB)) (ι (.sx .ktmp)) (ι .mselC)
    (ι (.sx (.kt 0))) (ι (.sx (.kt 1))) (ι (.sx (.kt 2))) st (fun j => ι (.kf j))

/-- The step bound of the key pass. -/
def cxKeyCost (d : CxD) : ℕ := d.M * (15 * d.kl + 6 * d.rw + 110) + 6 * d.kl + 40

lemma CxD.len8_kX (d : CxD) : d.len8 d.kX = d.L := by
  unfold CxD.kX CxD.len8; split_ifs <;> rfl

lemma CxD.len8_kY (d : CxD) : d.len8 d.kY = d.L := by
  unfold CxD.kY CxD.len8; split_ifs <;> rfl

/-- **The key pass** on the built registers: the records gain the keys of their ideal
destinations under the key tiling. -/
theorem cxKey_exec (henv : CxEnv ι par src) (hst : ∀ x, ι x ≠ st) (hsrcst : src ≠ st)
    (hv : d.Valid) (hsum8 : ∑ j, d.len8 j = d.kl) {l : List (List (Fin (A + 4)))}
    (hl : l.length = d.M) (hlB : ∀ r ∈ l, r.length = d.rw) {R₁ : Fin T → List (Fin (A + 4))}
    (v : HS T Q A U) (S : Stacks T A) (hS : S.R = cxFill ι (cxBc A d) 37 R₁)
    (hR₁ : R₁ src = l.flatten) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxKeyCost d ∧
      Exec body (cxKeyPass ι d src st) (mk v S) m
        (mk v' { S with R := cxFill ι (cxBc A d) 37 (Function.update R₁ src
          (keyedFrom (keyBitsAt d.kY d.kX d.len8 (selMask d.K d.ρ d.nn)) 0 l).flatten) }) := by
  have hF : ∀ x, S.R (ι x) = cxBc A d x := fun x => by
    rw [hS, cxFill_ι henv.hι, if_pos (cxStage_le x)]
  have hsrcR : S.R src = l.flatten := by rw [hS, cxFill_out _ _ _ henv.hsrc, hR₁]
  have hreg : KeyRegs src (ι (.sx .kacc)) (ι (.sx .ctrB)) (ι (.sx .ktmp)) (ι .mselC)
      (ι (.sx (.kt 0))) (ι (.sx (.kt 1))) (ι (.sx (.kt 2))) st (fun j => ι (.kf j)) := by
    apply KeyRegs.of_nodup
    · refine nodup_append_ofFn ?_ (fun a b h => by simpa using henv.hι h) ?_
      · simp [henv.hι.eq_iff, henv.hsrc, fun x => (henv.hsrc x).symm, Fin.ext_iff]
      · intro a ha j
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cxne'
    · simp only [List.mem_cons, List.mem_ofFn, not_or, not_exists]
      exact ⟨(hst _).symm, fun j e => hst _ e⟩
  obtain ⟨v', hu, he⟩ := keyPassAt_exec body d.kX_ne_kY.symm hreg (len := d.len8)
    (by rw [d.len8_kX, d.len8_kY]) (mm := selMask d.K d.ρ d.nn) hv.hrw l hlB v S hsrcR
    (by rw [hF]; rfl) (by rw [hF]; simp [cxBc, sxBc, CxD.swapD]) (by rw [hF]; rfl)
    ⟨fun g => by rw [hF]; rfl, by rw [hF, d.len8_kY]; rfl, by rw [hF]; rfl, by rw [hF]; rfl,
      by rw [hF]; rfl⟩
  refine ⟨v', _, hu, ?_, Exec.cast he rfl ?_⟩
  · rw [hl, hsum8]
    have hsum : ((List.finRange 8).map (keyCost d.kY d.len8)).sum ≤ 9 * d.kl + 64 := by
      rw [← Fin.sum_univ_def]
      calc ∑ j, keyCost d.kY d.len8 j ≤ ∑ j, (9 * d.len8 j + 8) :=
            Finset.sum_le_sum fun j _ => keyCost_le _ _ j
        _ = 9 * d.kl + 64 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum8]; simp
    have hrec : keyRecCost d.kY d.len8 d.rw ≤ 13 * d.kl + 4 * d.rw + 105 := by
      unfold keyRecCost
      rw [hsum8]
      omega
    have hM := Nat.mul_le_mul_left d.M hrec
    unfold cxKeyCost
    nlinarith [hM]
  · congr 2
    rw [hS, cxFill_update henv.hι _ _ _ henv.hsrc]

/-! ### The fix pass -/

/-- The fix pass of the machine. -/
noncomputable def cxFixPass (ι : CXReg → Fin T) (d : CxD) (src st : Fin T) : Pr P T Q A U :=
  fixPassC d.fX d.fY src (ι (.sx (.fr 0))) (ι (.sx (.fr 1))) (ι (.sx (.fr 2))) (ι (.sx (.fr 3)))
    (ι (.sx (.fq 0))) (ι (.sx (.fq 1))) (ι (.sx (.fq 2))) (ι (.sx (.fq 3))) (ι (.sx .ctrB))
    (ι (.sx .cnt)) (ι (.sx .ftmp)) (ι .mtopC) st (fun g => ι (.fld g)) (fun r => ι (.sx (.fus r)))

/-- The step bound of the fix pass. -/
def cxFixCost (d : CxD) : ℕ :=
  d.M * (18 * d.rw + 12 * d.L + 8 * d.n + 8 * 11 + 28) + 8 * d.n + 8 * 11 + 18

lemma CxD.len11_fX (d : CxD) : d.len11 d.fX = d.L := by
  unfold CxD.fX CxD.len11; split_ifs <;> rfl

lemma CxD.len11_fY (d : CxD) : d.len11 d.fY = d.L := by
  unfold CxD.fY CxD.len11; split_ifs <;> rfl

/-- **The fix pass** on the built registers. -/
theorem cxFix_exec (henv : CxEnv ι par src) (hst : ∀ x, ι x ≠ st) (hv : d.Valid)
    (hsum11 : ∑ g, d.len11 g = d.n) (hSY : foff d.len11 d.fY + d.len11 d.fY ≤ d.n)
    {l : List (List (Fin (A + 4)))} (hl : l.length = d.M) (hlB : ∀ r ∈ l, r.length = d.rw)
    {R₁ : Fin T → List (Fin (A + 4))} (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = cxFill ι (cxBc A d) 37 R₁) (hR₁ : R₁ src = l.flatten) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxFixCost d ∧
      Exec body (cxFixPass ι d src st) (mk v S) m
        (mk v' { S with R := cxFill ι (cxBc A d) 37 (Function.update R₁ src
          (moveRecs (topFixPermC d.len11 d.fX d.fY d.K d.ρ d.nn (R := d.R) d.fX_ne_fY
            (by rw [d.len11_fX, d.len11_fY]) hSY) l).flatten) }) := by
  have hF : ∀ x, S.R (ι x) = cxBc A d x := fun x => by
    rw [hS, cxFill_ι henv.hι, if_pos (cxStage_le x)]
  have hsrcR : S.R src = l.flatten := by rw [hS, cxFill_out _ _ _ henv.hsrc, hR₁]
  have hp : d.ρ + d.nn * d.K < d.len11 d.fY := by
    rw [d.len11_fY, hv.hLK]
    have hk := hv.hk; have hρ := hv.hρ
    unfold CxD.nn
    have : d.K * d.k = d.K * (d.k - 1) + d.K := by
      rw [← Nat.mul_succ]; congr 1; omega
    rw [this, Nat.mul_comm (d.k - 1)]
    omega
  obtain ⟨v', m, hu, hm, he⟩ := fixPassC_exec body d.len11 d.fX_ne_fY
    (by rw [d.len11_fX, d.len11_fY]) (R := d.R) (S := d.n) hSY hp
    (src := src) (r0 := ι (.sx (.fr 0))) (r1 := ι (.sx (.fr 1))) (r2 := ι (.sx (.fr 2)))
    (r3 := ι (.sx (.fr 3))) (q0 := ι (.sx (.fq 0))) (q1 := ι (.sx (.fq 1)))
    (q2 := ι (.sx (.fq 2))) (q3 := ι (.sx (.fq 3))) (ctrB := ι (.sx .ctrB)) (cnt := ι (.sx .cnt))
    (tmp := ι (.sx .ftmp)) (tm := ι .mtopC) (st := st) (cf := fun g => ι (.fld g))
    (us := fun r => ι (.sx (.fus r)))
    (by
      refine nodup_append_ofFn (nodup_append_ofFn ?_ ?_ ?_) (fun a b h => by simpa using henv.hι h)
        ?_
      · simp [henv.hι.eq_iff, henv.hsrc, fun x => (henv.hsrc x).symm, Fin.ext_iff]
      · intro a b h; have := henv.hι h; simpa [Fin.ext_iff] using this
      · intro a ha r
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;>
          cxne'
      · intro a ha j
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn] at ha
        rcases ha with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl)
          | ⟨r, rfl⟩ <;> cxne')
    (by
      simp only [List.mem_append, List.mem_singleton, List.mem_ofFn, not_or, not_exists]
      exact ⟨⟨(hst _).symm, fun r e => hst _ e⟩, fun j e => hst _ e⟩)
    hv.hrw l hl hlB v S hsrcR
    (by rw [hF]; rfl) (by rw [hF]; rfl) (by rw [hF]; rfl) (by rw [hF]; rfl)
    (by rw [hF]; rfl) (by rw [hF]; rfl) (by rw [hF]; rfl) (by rw [hF]; rfl)
    (by rw [hF]; simp [cxBc, sxBc, CxD.swapD]) (by rw [hF]; simp [cxBc, sxBc, CxD.swapD, SxD.M, CxD.M])
    (by rw [hF]; rfl) (by rw [hF, d.len11_fY]; rfl) (fun r => by rw [hF]; rfl)
    (fun j => by rw [hF]; rfl)
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · unfold cxFixCost
    rw [d.len11_fY, hsum11] at hm
    exact hm
  · congr 2
    rw [hS, cxFill_update henv.hι _ _ _ henv.hsrc]


/-! ### The rotations -/

/-- The register holding the length of the rotated field: `nG` for `B`, `L` for a slot. -/
def cxRotLenReg (ι : CXReg → Fin T) (par : CXPar → Fin T) (tf : Fin 11) : Fin T :=
  if tf = CxD.fB then ι (.val .nGa) else par .L

/-- Prepare `comp` for the rotation of `tf`: clear it and fill it with `len tf` zeros. -/
noncomputable def prepComp (ι : CXReg → Fin T) (par : CXPar → Fin T) (tf : Fin 11) :
    Pr P T Q A U :=
  .seq (uclear (ι .comp)) (zeroBits (cxRotLenReg ι par tf) (ι .comp) (ι (.sx .rtmp)))

/-- A rotation pass of the machine with preparation bank `t`. -/
noncomputable def cxRotPass (ι : CXReg → Fin T) (par : CXPar → Fin T) (src st : Fin T)
    (tf : Fin 11) (neg : Bool) (t : Fin 7) (useY useT : Bool) (fA fY fT : Fin 11) :
    Pr P T Q A U :=
  .seq (prepComp ι par tf)
    (rotGenPass (prepOff useY useT (rotι ι src t ∘ embedP fA fY fT)) tf neg (rotι ι src t) st)

lemma bankVal_injective (t : Fin 7) : Function.Injective (bankVal t) := by
  fin_cases t <;> decide

lemma rotι_injective (henv : CxEnv ι par src) (t : Fin 7) :
    Function.Injective (rotι ι src t) := by
  intro a b h
  cases a <;> cases b <;> simp only [rotι] at h <;>
    first
    | rfl
    | exact absurd h (henv.hsrc _)
    | exact absurd h.symm (henv.hsrc _)
    | (have := henv.hι h; simp only [CXReg.val.injEq] at this; rw [bankVal_injective t this])
    | (have := henv.hι h; simp_all [Fin.ext_iff])

lemma rotι_st (hst : ∀ x, ι x ≠ st) (t : Fin 7) :
    ∀ x : RotGReg 11 8 9, x.isIdx = true → rotι ι src t x ≠ st := by
  intro x hx
  cases x <;> simp [RotGReg.isIdx] at hx <;> simp [rotι] <;> exact hst _

/-- The step bound of one rotation pass. -/
def cxRotCost (d : CxD) (cP : ℕ) : ℕ :=
  2 * d.L + 2 + (4 * d.L + 4) +
    (d.M * (2 * cP + 2 * idxStepCost d.Bk d.L d.len11 + 4 * d.Bk + 4) + 13)

set_option maxHeartbeats 1000000 in
/-- **One rotation pass** on the built registers. -/
theorem cxRot_exec (henv : CxEnv ι par src) (hst : ∀ x, ι x ≠ st) (hv : d.Valid)
    (hsum11 : ∑ g, d.len11 g = d.n) (tf : Fin 11) (htf : d.len11 tf ≤ d.L)
    (hlenReg : d.len11 tf = if tf = CxD.fB then d.nG else d.L) (neg : Bool) (t : Fin 7)
    (useY useT : Bool) (fA fY fT : Fin 11) {off : ℕ → ℕ} (hoff : HighOff d.len11 tf off)
    (hob : ∀ i, off i < 2 ^ d.len11 tf) {cP : ℕ} {P₀ : Fin 9 → List (Fin (A + 4))}
    (hprep : PrepSpec body (prepOff useY useT (rotι ι src t ∘ embedP fA fY fT))
      (fun g => rotι ι src t (.fld g)) d.len11 (d.len11 tf)
      (fun r => rotι ι src t (RotGReg.rsRegG tf r)) (fun r => rotι ι src t (.spare r))
      (rsrcR tf off) (fun s => rotι ι src t (.scr s)) (fun q => rotι ι src t (.prm q)) P₀ cP)
    (hP₀ : ∀ q, cxBc A d (.val (bankVal t q)) = P₀ q)
    {X : List (List (Fin (A + 4)))} (hX : X.length = d.M) (hXB : ∀ r ∈ X, r.length = d.Bk)
    {R₁ : Fin T → List (Fin (A + 4))} (hpar : (R₁ (par .L)).length = d.L) (v : HS T Q A U)
    (S : Stacks T A) (hS : CxState ι d R₁ S.R) (hR₁ : R₁ src = X.flatten)
    (hcl : (S.R (ι .comp)).length ≤ d.L) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ cxRotCost d cP ∧
      Exec body (cxRotPass ι par src st tf neg t useY useT fA fY fT) (mk v S) m
        (mk v' { S with R := R' }) ∧
      R' src = (moveRecs (rotPerm d.len11 tf neg d.R hoff) X).flatten ∧
      CxState ι d (Function.update R₁ src (moveRecs (rotPerm d.len11 tf neg d.R hoff) X).flatten) R' ∧
      (R' (ι .comp)).length ≤ d.L := by
  have hF := hS.fill_ι henv
  have hP := hS.parVal henv
  have hsrcR : S.R src = X.flatten := by rw [hS.srcVal henv, hR₁]
  have hBk : 1 ≤ d.Bk := by unfold CxD.Bk; have := hv.hrw; omega
  -- preparing `comp`
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body (ι .comp) v S
  set Ra := Function.update S.R (ι .comp) [] with hRa
  have hRaf : ∀ k, k ≠ ι .comp → Ra k = S.R k := fun k hk => by
    rw [hRa, Function.update_of_ne hk]
  have hlr : (Ra (cxRotLenReg ι par tf)).length = d.len11 tf := by
    unfold cxRotLenReg
    split_ifs with h
    · rw [hRaf _ (henv.ne (by simp)), hF _ (by simp), h]
      simp [cxBc, CxD.valOf]
      rfl
    · rw [hRaf _ (henv.hpι' _ _), hP, hpar, hlenReg, if_neg h]
  have hlrc : cxRotLenReg ι par tf ≠ ι .comp := by
    unfold cxRotLenReg; split_ifs <;> cxne'
  have hlrt : cxRotLenReg ι par tf ≠ ι (.sx .rtmp) := by
    unfold cxRotLenReg; split_ifs <;> cxne'
  obtain ⟨v₂, hu₂, he₂⟩ := zeroBits_exec body hlrc hlrt (henv.ne (by simp)) v₁ { S with R := Ra }
    (by show Ra (ι (.sx .rtmp)) = []; rw [hRaf _ (henv.ne (by simp)), hF _ (by simp)]; rfl)
  rw [hlr] at he₂
  set Rb := Function.update Ra (ι .comp) (binSyms (d.len11 tf) 0 ++ Ra (ι .comp)) with hRb
  have hRbf : ∀ k, k ≠ ι .comp → Rb k = S.R k := fun k hk => by
    rw [hRb, Function.update_of_ne hk, hRaf _ hk]
  have hRbc : Rb (ι .comp) = binSyms (d.len11 tf) 0 := by
    rw [hRb, Function.update_self, hRa, Function.update_self, List.append_nil]
  have hRbι : ∀ x, x ≠ .comp → Rb (ι x) = cxBc A d x := fun x hx => by
    rw [hRbf _ (henv.ne hx), hF x hx]
  -- the rotation pass
  have hM : X.length = d.R * 2 ^ ∑ g, d.len11 g := by rw [hsum11]; exact hX
  obtain ⟨v₃, R', m, hu₃, hm, he₃, hsrc', hcomp', hoth⟩ := rotGenPass_exec body tf neg
    (rotι_injective henv t) (rotι_st hst t) d.len11 hoff hob hprep hBk hM hXB
    (c := List.replicate d.swapD.Bk tick) (kk := List.replicate d.swapD.M tick)
    (by simp [CxD.swapD, SxD.Bk, SxD.kl, CxD.Bk, CxD.kl, CxD.rb, SxD.rb])
    (by simp [CxD.swapD, SxD.M, hsum11]) v₂ { S with R := Rb }
    (by show Rb src = _; rw [hRbf _ (henv.hsrc _).symm, hsrcR])
    (by show Rb (ι (.sx .ctrKB)) = _; rw [hRbι _ (by simp)]; rfl)
    (by show Rb (ι (.sx .cnt)) = _; rw [hRbι _ (by simp)]; rfl)
    (by show Rb (ι (.sx .rtmp)) = _; rw [hRbι _ (by simp)]; rfl)
    (by show Rb (ι (.sx .rctmp)) = _; rw [hRbι _ (by simp)]; rfl)
    (by show Rb (ι (.sx .rout)) = _; rw [hRbι _ (by simp)]; rfl)
    (fun e => by show Rb (ι (.sx (.rdst e))) = _; rw [hRbι _ (by simp)]; rfl)
    (fun e => by show Rb (ι (.sx (.raux e))) = _; rw [hRbι _ (by simp)]; rfl)
    (fun g => by show Rb (ι (.fld g)) = _; rw [hRbι _ (by simp)]; rfl)
    (by show (Rb (ι .comp)).length = _; rw [hRbc, length_binSyms])
    (fun r => by show Rb (ι (.sx (.rsp _))) = _; rw [hRbι _ (by simp)]; rfl)
    (fun s' => by show Rb (ι (.rscr s')) = _; rw [hRbι _ (by simp)]; rfl)
    (fun q => by show Rb (ι (.val (bankVal t q))) = _; rw [hRbι _ (by simp), hP₀])
  have hsrc'' : R' src = (moveRecs (rotPerm d.len11 tf neg d.R hoff) X).flatten := hsrc'
  have hcomp'' : (R' (ι .comp)).length = d.len11 tf := hcomp'
  have hoth' : ∀ k, k ≠ src → k ≠ ι .comp → R' k = Rb k := fun k h1 h2 => hoth k h1 h2
  refine ⟨v₃, R', _, by rw [hu₃, hu₂, hu₁], ?_, Exec.seq (Exec.seq he₁ he₂) he₃, hsrc'', ?_, ?_⟩
  · show 2 * (S.R (ι .comp)).length + 2 + (4 * d.len11 tf + 4) + m ≤ _
    unfold cxRotCost
    have hmono : idxStepCost d.Bk (d.len11 tf) d.len11 ≤ idxStepCost d.Bk d.L d.len11 := by
      unfold idxStepCost; omega
    have hM' : d.R * 2 ^ ∑ g, d.len11 g = d.M := by rw [hsum11]; rfl
    rw [hM'] at hm
    have h2 := Nat.mul_le_mul_left d.M (show 2 * cP + 2 * idxStepCost d.Bk (d.len11 tf) d.len11 +
      4 * d.Bk + 4 ≤ 2 * cP + 2 * idxStepCost d.Bk d.L d.len11 + 4 * d.Bk + 4 by omega)
    omega
  · intro k hk
    by_cases hks : k = src
    · subst hks
      rw [hsrc'', cxFill_out _ _ _ henv.hsrc, Function.update_self]
    · rw [hoth' k hks hk, hRbf k hk, hS k hk, ← cxFill_update henv.hι _ _ _ henv.hsrc,
        Function.update_of_ne hks]
  · rw [hcomp'']; exact htf


/-! ### The interchanges -/

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- An interchange of the machine: the old interchange on the bank of the chunk pair. -/
noncomputable def cxSwapPass {Ka : ℕ} (henv : CxEnv ι par src)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (st : Fin T) (a b : Fin 3) :
    Pr P T Q (prime + Ka) U :=
  sxInstr (ι := sxι ι) (cxSxEnv henv).hι hQ src st (.swap a b)

/-- The fields of the three chunks of the interchange rectangle. -/
abbrev cxChunk : Fin 3 → Fin 11 := ![CxD.fU, CxD.fT, CxD.fB]

/-- The built file is an interchange fill over itself. -/
lemma sxFill_self_of (hι : Function.Injective (sxι ι)) {R : Fin T → List (Fin (A + 4))}
    (h : ∀ x, R (sxι ι x) = sxBc A d.swapD x) : sxFill (sxι ι) (sxBc A d.swapD) 38 R = R := by
  funext t
  by_cases ht : ∃ x, sxι ι x = t
  · obtain ⟨x, rfl⟩ := ht
    rw [sxFill_ι hι, if_pos (sxStage_le x), h]
  · simp only [not_exists] at ht
    rw [sxFill_out (ι := sxι ι) _ _ _ ht]

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
set_option maxHeartbeats 1000000 in
/-- **One interchange** on the built registers: the fields of the two chunks are exchanged. -/
theorem cxSwap_exec {Ka : ℕ} (body : P → Pr P T Q (prime + Ka) U) (henv : CxEnv ι par src)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (hv : d.Valid)
    (hf1 : foff d.len11 CxD.fB = d.bB) (hf7 : foff d.len11 CxD.fT = d.bT)
    (hf9 : foff d.len11 CxD.fU = d.bU) {a b : Fin 3}
    (hWF : CInstr.WF d.len11 d.n (.swap (cxChunk a) (cxChunk b)))
    {X : List (List (Fin (prime + Ka + 4)))} (hX : X.length = d.M)
    (hXB : ∀ r ∈ X, r.length = d.Bk) (hX8 : ∀ r ∈ X, ∀ s ∈ r, s.val < 8)
    {R₁ : Fin T → List (Fin (prime + Ka + 4))} (v : HS T Q (prime + Ka) U)
    (S : Stacks T (prime + Ka)) (hL : ∀ y, S.L y = []) (hS : CxState ι d R₁ S.R)
    (hR₁ : R₁ src = X.flatten) :
    ∃ (v' : HS T Q (prime + Ka) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ sxSwapCost d.swapD T ∧
      Exec body (cxSwapPass henv hQ st a b) (mk v S) m
        (mk v' { S with
          R := Function.update S.R src
                (moveRecs (Layer.CompactXor.instrPerm d.len11 (R := d.R) (S := d.n) hWF)
                  X).flatten }) := by
  have hsx := cxSxEnv henv
  have hF := hS.fill_ι henv
  have hself : ∀ R : Fin T → List (Fin (prime + Ka + 4)),
      (∀ x, R (sxι ι x) = sxBc (prime + Ka) d.swapD x) →
        sxFill (sxι ι) (sxBc (prime + Ka) d.swapD) 38 R = R := fun R h => sxFill_self_of hsx.hι h
  have hSsx : ∀ x, S.R (sxι ι x) = sxBc (prime + Ka) d.swapD x := fun x => hF (.sx x) (by simp)
  have hsrcR : S.R src = X.flatten := by rw [hS.srcVal henv, hR₁]
  have hab : a ≠ b := hWF.1 ∘ fun e => by rw [e]
  obtain ⟨v', m, hu, hm, he⟩ := sxSwap_exec body hsx (fun x => henv.hsrc _) (swapD_valid hv) hQ
    hab hX hXB hX8 (R₁ := S.R) v S hL (hself S.R hSsx).symm hsrcR
  refine ⟨v', m, hu, hm, Exec.cast he rfl ?_⟩
  congr 2
  rw [hself _ (fun x => by
    show Function.update S.R src _ (ι (CXReg.sx x)) = _
    rw [Function.update_of_ne (henv.hsrc _)]; exact hSsx x)]
  congr 1
  -- the rectangle swap is the field swap
  obtain ⟨hp0, hp1, hp2⟩ := swapD_pos hv
  have hfit : d.swapD.a₀ + (sxPos d.swapD.x d.swapD.y d.swapD.z 0 + 1) * d.swapD.L ≤ d.swapD.n :=
    (swapD_valid hv).hfit
  have hsum := sx_sum (swapD_valid hv).hxy (swapD_valid hv).hxz (swapD_valid hv).hyz hfit
  simp only [CxD.swapD] at hp0 hp1 hp2 hsum ⊢
  have hn3 : sxN3 d.bB d.nG d.pU d.pT 0 = d.bB := by simp [sxN3, hp2]
  have hn2 : sxN2 d.nG d.pU d.pT 0 = (d.pT - 1) * d.nG := by simp [sxN2, hp1, hp2]
  have hn1 : sxN1 d.nG d.pU d.pT 0 = (d.pU - d.pT - 1) * d.nG := by simp [sxN1, hp0, hp1]
  have hbT : d.bT = d.bB + d.nG + (d.pT - 1) * d.nG := by
    unfold CxD.bT
    have := hv.hpT
    have : d.pT * d.nG = d.nG + (d.pT - 1) * d.nG := by
      conv_lhs => rw [show d.pT = 1 + (d.pT - 1) by omega]
      ring
    omega
  have hbU : d.bU = d.bB + d.nG + (d.pT - 1) * d.nG + d.nG + (d.pU - d.pT - 1) * d.nG := by
    unfold CxD.bU
    have := hv.hpT; have := hv.hpTU
    have : d.pU * d.nG = d.nG + (d.pT - 1) * d.nG + d.nG + (d.pU - d.pT - 1) * d.nG := by
      conv_lhs => rw [show d.pU = 1 + (d.pT - 1) + 1 + (d.pU - d.pT - 1) by omega]
      ring
    omega
  have key := moveRecs_rankPerm_swap d.len11 CxD.fB CxD.fT CxD.fU
    (sxN0 d.bB d.nG d.n d.pU d.pT 0) (sxN1 d.nG d.pU d.pT 0) (sxN2 d.nG d.pU d.pT 0)
    (sxN3 d.bB d.nG d.pU d.pT 0) d.nG d.R d.n rfl rfl rfl (by rw [hf1, hn3])
    (by rw [hf7, hn3, hn2, hbT]) (by rw [hf9, hn3, hn2, hn1, hbU]) (by rw [hn3, hn2, hn1] at hsum; omega)
    hWF X d.nG 0 0
  show (moveRecs (rankPerm (d.R * 2 ^ sxN0 d.bB d.nG d.n d.pU d.pT 0) (2 ^ sxN1 d.nG d.pU d.pT 0)
    (2 ^ sxN2 d.nG d.pU d.pT 0) (2 ^ sxN3 d.bB d.nG d.pU d.pT 0) d.nG d.nG 0 0 [.swap a b]) X).flatten = _
  rw [key]


/-! ### The repair -/

/-- The repair pass of the machine: one symbol into the indicator register, the prepared repair
with the indicator preparation, the indicator register cleared. -/
noncomputable def cxRepairPass (ι : CXReg → Fin T) (d : CxD) (src st : Fin T) : Pr P T Q A U :=
  .seq (.seq (.act (.push (.rt (ι (.breg .comp))) (fun _ => bitSymbol false) .done))
    (repairAtP (badPrep (decide (d.x < d.y)) (fun g => ι (.fld g)) CxD.fT CxD.fU d.fY (badι ι) st)
      src (ι (.sx .pgR)) (ι (.sx .pbR)) (ι (.sx .pg)) (ι (.sx .pb)) (ι (.sx .ctrKB))
      (ι (.sx .ctrB)) (ι (.sx .ctrK)) (ι (.sx .cnt)) (ι (.sx .ptmp)) st (fun g => ι (.fld g))
      ![badι ι .comp] ![badι ι .t₁] (fun r => ι (.sx (.pus r))) (cxBitAuto A)))
    (uclear (ι (.breg .comp)))

/-- The step bound of the repair pass with `bad` exceptional indices. -/
def cxRepairCost (d : CxD) (bad : ℕ) : ℕ :=
  d.M * (2 * badPrepCost d.L d.nG 1 + 16 * (d.kl + d.rw) + 12 + 8 * d.n + 8 * 11 + 39) +
    d.kl * (bad * (12 * d.kl + 6 * d.rw + 13)) + 10 * d.kl + 8 * d.n + 8 * 11 + 18 + 5

lemma CxD.M_le_pow_kl (d : CxD) : d.M ≤ 2 ^ d.kl := by
  unfold CxD.M CxD.kl CxD.rb
  rw [pow_add, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (lt_two_pow_length_sxBits d.R).le

lemma badι_ne_fld (henv : CxEnv ι par src) (x : BReg) (f : Fin 11) : badι ι x ≠ ι (.fld f) := by
  cases x <;> simp [badι, henv.hι.eq_iff]

lemma badι_injective (henv : CxEnv ι par src) : Function.Injective (badι ι) := by
  intro a b h
  cases a <;> cases b <;> simp_all [badι, henv.hι.eq_iff]

/-- The index layout of the repair's route and merge loops. -/
lemma cxRepairLayout (henv : CxEnv ι par src) (hst : ∀ x, ι x ≠ st) (hsrcst : src ≠ st) :
    RepairLayoutP src (ι (.sx .pgR)) (ι (.sx .pbR)) (ι (.sx .pg)) (ι (.sx .pb)) (ι (.sx .ctrKB))
      (ι (.sx .ctrB)) (ι (.sx .ctrK)) (ι (.sx .cnt)) (ι (.sx .ptmp)) st (fun g => ι (.fld g))
      d.len11 1 ![badι ι .comp] ![badι ι .t₁]
      ![.inr (cbadN d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn)]
      (scrB (badι ι)) (prmB (badι ι)) (fun r => ι (.sx (.pus r))) := by
  have hb := badι_injective henv
  have hbf := badι_ne_fld henv
  have hbst : ∀ x, badι ι x ≠ st := fun x => by cases x <;> simp [badι, hst]
  have hbsx : ∀ x r, badι ι x ≠ ι (.sx r) := fun x r => by cases x <;> simp [badι, henv.hι.eq_iff]
  have hbsrc : ∀ x, badι ι x ≠ src := fun x => by cases x <;> simp [badι, henv.hsrc]
  have hcf_inj : Function.Injective (fun g : Fin 11 => ι (.fld g)) := fun a b h => by
    simpa using henv.hι h
  -- the two index layouts
  have hlay : ∀ (X : Fin T → Prop), (∀ f, ¬ X (ι (.fld f))) → (∀ x, ¬ X (badι ι x)) →
      IdxLayoutP (fun g => ι (.fld g)) d.len11 1 ![badι ι .comp] ![badι ι .t₁]
        ![.inr (cbadN d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn)]
        (scrB (badι ι)) (prmB (badι ι)) st X := fun X hXf hXb =>
    { rs_inj := fun a b _ => Fin.ext (by omega)
      tmps_inj := fun a b _ => Fin.ext (by omega)
      rs_tmps := fun r r' => by fin_cases r; fin_cases r'; simp [hb.eq_iff]
      rs_st := fun r => by fin_cases r; simp [hbst]
      tmps_st := fun r => by fin_cases r; simp [hbst]
      cf_inj := hcf_inj
      tmps_cf := fun r f => by fin_cases r; simp [hbf]
      field := fun r f h => by fin_cases r; cases h
      param := fun r g f _ => by fin_cases r; simp [hbf]
      scr_cf := fun s' f => by fin_cases s' <;> simp [scrB, hbf]
      scr_rs := fun s' r => by fin_cases s' <;> fin_cases r <;> simp [scrB, hb.eq_iff]
      prm_cf := fun q f => by fin_cases q <;> simp [prmB, hbf]
      prm_rs := fun q r => by fin_cases q <;> fin_cases r <;> simp [prmB, hb.eq_iff]
      prm_X := fun q => by fin_cases q <;> simp [prmB, hXb]
      cf_X := hXf
      rs_X := fun r => by fin_cases r; simp [hXb]
      tmps_X := fun r => by fin_cases r; simp [hXb]
      scr_X := fun s' => by fin_cases s' <;> simp [scrB, hXb] }
  have hsrc' := henv.hsrc
  have hsrc'' : ∀ x, src ≠ ι x := fun x => (henv.hsrc x).symm
  have hst' : ∀ x, st ≠ ι x := fun x => (hst x).symm
  refine ⟨hlay _ ?_ ?_, hlay _ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f; simp [routeRegs, henv.hι.eq_iff, hsrc', hsrc'', Fin.exists_fin_two]
  · intro x; cases x <;> simp [routeRegs, badι, henv.hι.eq_iff, hsrc', hsrc'', Fin.exists_fin_two]
  · intro f; simp [mergeRegs, henv.hι.eq_iff, hsrc', hsrc'', Fin.exists_fin_two]
  · intro x; cases x <;> simp [mergeRegs, badι, henv.hι.eq_iff, hsrc', hsrc'', Fin.exists_fin_two]
  · simp [henv.hι.eq_iff, hsrc', hsrc'']
  · intro f; simp [henv.hι.eq_iff, hsrc', hsrc'']
  · intro r; fin_cases r; simp [badι, henv.hι.eq_iff, hsrc', hsrc'']
  · intro r; simp [henv.hι.eq_iff, hsrc', hsrc'']
  · intro a b h; have := henv.hι h; simpa using this
  · intro r f; simp [henv.hι.eq_iff]
  · intro r r'; fin_cases r'; simp [badι, henv.hι.eq_iff]
  · intro r r'; fin_cases r'; simp [badι, henv.hι.eq_iff]
  · intro r s'; fin_cases s' <;> simp [scrB, badι, henv.hι.eq_iff]
  · intro r q; fin_cases q <;> simp [prmB, badι, henv.hι.eq_iff]
  · intro r; exact hst _
  · intro s'; fin_cases s' <;> simp [scrB, badι, henv.hι.eq_iff, hsrc', hsrc'']
  · intro q; fin_cases q <;> simp [prmB, badι, henv.hι.eq_iff, hsrc', hsrc'']
  · intro r g _; fin_cases r; simp [badι, henv.hι.eq_iff, hsrc', hsrc'']


lemma CxD.fT_ne_fY (d : CxD) : CxD.fT ≠ d.fY := by unfold CxD.fY; split_ifs <;> decide
lemma CxD.fU_ne_fY (d : CxD) : CxD.fU ≠ d.fY := by unfold CxD.fY; split_ifs <;> decide

set_option maxHeartbeats 1000000 in
/-- **The repair pass** on the built registers: the stream moved by an actual permutation
`πS` agreeing with the ideal `πT` off the exceptional set is replaced by the stream moved by
`πT`, keys stripped. -/
theorem cxRepair_exec (hA : 12 ≤ A) (henv : CxEnv ι par src) (hst : ∀ x, ι x ≠ st)
    (hsrcst : src ≠ st) (hv : d.Valid) (hsum11 : ∑ g, d.len11 g = d.n)
    {πS πT : Equiv.Perm (Fin d.M)}
    (hT : ∀ x : Fin d.M, CBad d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn (πT x) ↔
      CBad d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn x)
    (agree : ∀ x : Fin d.M, ¬ CBad d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn x →
      πS x = πT x)
    (l : List (List (Fin (A + 4)))) (hl : l.length = d.M) (hlB : ∀ r ∈ l, r.length = d.rw)
    {R₁ : Fin T → List (Fin (A + 4))} (v : HS T Q A U) (S : Stacks T A) (hS : CxState ι d R₁ S.R)
    (hR₁ : R₁ src = (moveRecs πS (keyRecs d.kl πT l)).flatten) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ cxRepairCost d
        (Fintype.card {j : Fin d.M // CBad d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn j}) ∧
      Exec body (cxRepairPass ι d src st) (mk v S) m (mk v' { S with R := R' }) ∧
      R' src = (moveRecs πT l).flatten ∧
      CxState ι d (Function.update R₁ src (moveRecs πT l).flatten) R' ∧
      R' (ι .comp) = S.R (ι .comp) := by
  have hF := hS.fill_ι henv
  have hsrcR : S.R src = (moveRecs πS (keyRecs d.kl πT l)).flatten := by rw [hS.srcVal henv, hR₁]
  have hLeq := d.L_eq hv
  have hcomp0 : S.R (ι (.breg .comp)) = [] := by rw [hF _ (by simp)]; rfl
  -- the indicator register
  have he₁ := sx_push_exec body v S (ι (.breg .comp)) (bitSymbol false)
  rw [hcomp0] at he₁
  set S₁ := Function.update S.R (ι (.breg .comp)) [bitSymbol false] with hS₁
  have hS₁f : ∀ k, k ≠ ι (.breg .comp) → S₁ k = S.R k := fun k hk => by
    rw [hS₁, Function.update_of_ne hk]
  have hS₁ι : ∀ x, x ≠ .breg .comp → x ≠ .comp → S₁ (ι x) = cxBc A d x := fun x h1 h2 => by
    rw [hS₁f _ (henv.ne h1), hF x h2]
  have hbst : ∀ x, badι ι x ≠ st := fun x => by cases x <;> simp [badι, hst]
  -- the repair
  obtain ⟨v₂, R₂, m₂, hu₂, hm₂, he₂, hsrc₂, hcomp₂, hoth₂⟩ := compactRepair_exec body hA
    (decide (d.x < d.y)) (cf := fun g => ι (.fld g)) (fT := CxD.fT) (fU := CxD.fU) (fY := d.fY)
    (badι_injective henv) (st := st) (badι_ne_fld henv) hbst (fun f => hst _)
    (henv.ne (by simp [d.fT_ne_fY])) (fun _ => henv.ne (by simp [d.fU_ne_fY]))
    (fun _ => henv.ne (by simp [CxD.fT, CxD.fU])) d.len11 hv.hG hv.hGK hv.hρ rfl (fun _ => rfl)
    (by rw [d.len11_fY, hLeq]) (cxRepairLayout henv hst hsrcst) (k := d.kl) (B := d.rw)
    d.M_le_pow_kl hv.hrw hT agree l hl hlB v { S with R := S₁ }
    (by show S₁ src = _; rw [hS₁f _ (henv.hsrc _).symm, hsrcR])
    (by show S₁ (ι (.sx .pgR)) = []; rw [hS₁ι _ (by simp) (by simp)]; rfl)
    (by show S₁ (ι (.sx .pbR)) = []; rw [hS₁ι _ (by simp) (by simp)]; rfl)
    (by show S₁ (ι (.sx .pg)) = []; rw [hS₁ι _ (by simp) (by simp)]; rfl)
    (by show S₁ (ι (.sx .pb)) = []; rw [hS₁ι _ (by simp) (by simp)]; rfl)
    (by show (S₁ (ι (.sx .ctrKB))).length = _
        rw [hS₁ι _ (by simp) (by simp)]
        simp [cxBc, sxBc, CxD.swapD, SxD.Bk, SxD.kl, CxD.kl, CxD.rb, SxD.rb]; omega)
    (by show (S₁ (ι (.sx .ctrB))).length = _; rw [hS₁ι _ (by simp) (by simp)]; simp [cxBc, sxBc, CxD.swapD])
    (by show (S₁ (ι (.sx .ctrK))).length = _
        rw [hS₁ι _ (by simp) (by simp)]
        simp [cxBc, sxBc, CxD.swapD, SxD.kl, CxD.kl, CxD.rb, SxD.rb])
    (by show (S₁ (ι (.sx .cnt))).length = _
        rw [hS₁ι _ (by simp) (by simp)]; simp [cxBc, sxBc, CxD.swapD, SxD.M, CxD.M])
    (by show S₁ (ι (.sx .ptmp)) = []; rw [hS₁ι _ (by simp) (by simp)]; rfl)
    (fun r => by show S₁ (ι (.sx (.pus r))) = []; rw [hS₁ι _ (by simp) (by simp)]; rfl)
    ⟨fun f => by
        show S₁ (ι (.fld f)) = _
        rw [hS₁ι _ (by simp) (by simp)]
        simp [cxBc, digit],
      fun r g _ => by
        fin_cases r
        show (S₁ (ι (.breg .comp))).length = 1
        rw [hS₁, Function.update_self]; rfl,
      fun r => by fin_cases r; show S₁ (ι (.breg .t₁)) = []; rw [hS₁ι _ (by simp) (by simp)]; rfl,
      fun s' => by
        fin_cases s' <;> simp only [scrB, badι, Matrix.cons_val] <;>
          first
          | (show S₁ (ι (.breg _)) = []; rw [hS₁ι _ (by simp) (by simp)]; rfl),
      fun q => by
        fin_cases q
        · show S₁ (ι .mD) = binSyms _ (altMask _ _)
          rw [hS₁ι _ (by simp) (by simp)]; simp [cxBc, hLeq]
        · show S₁ (ι .mG) = binSyms _ (highMask _ _ _ _ _)
          rw [hS₁ι _ (by simp) (by simp)]; simp [cxBc, hLeq]
        · show S₁ (ι .padR) = List.replicate _ tick
          rw [hS₁ι _ (by simp) (by simp)]; simp [cxBc, hLeq]; rfl⟩
  -- clearing the indicator register
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (ι (.breg .comp)) v₂ { S with R := R₂ }
  have hcomp₂' : (R₂ (ι (.breg .comp))).length = 1 := hcomp₂
  refine ⟨v₃, _, _, by rw [hu₃, hu₂], ?_, Exec.seq (Exec.seq he₁ he₂) he₃, ?_, ?_, ?_⟩
  · show 1 + m₂ + (2 * (R₂ (ι (.breg .comp))).length + 2) ≤ _
    rw [hcomp₂']
    unfold cxRepairCost
    rw [hsum11] at hm₂
    rw [hLeq]
    have : d.nn * d.G = d.nG := rfl
    rw [this] at hm₂
    omega
  · show Function.update R₂ (ι (.breg .comp)) [] src = _
    rw [Function.update_of_ne (henv.hsrc _).symm, hsrc₂]
  · intro k hk
    show Function.update R₂ (ι (.breg .comp)) [] k = _
    by_cases hkb : k = ι (.breg .comp)
    · subst hkb
      rw [Function.update_self, ← cxFill_update henv.hι _ _ _ henv.hsrc,
        Function.update_of_ne (henv.hsrc _), cxFill_ι henv.hι, if_pos (cxStage_le _)]
      rfl
    rw [Function.update_of_ne hkb]
    by_cases hks : k = src
    · subst hks
      rw [hsrc₂, cxFill_out _ _ _ henv.hsrc, Function.update_self]
    · rw [hoth₂ k hks hkb]
      show S₁ k = _
      rw [hS₁f k hkb, hS k hk, ← cxFill_update henv.hι _ _ _ henv.hsrc,
        Function.update_of_ne hks]
  · show Function.update R₂ (ι (.breg .comp)) [] (ι .comp) = _
    rw [Function.update_of_ne (henv.ne (by simp)), hoth₂ _ (henv.hsrc _) (henv.ne (by simp))]
    exact hS₁f _ (henv.ne (by simp))


/-! ### The instructions -/

lemma CxD.fY_ne_fB (d : CxD) : d.fY ≠ CxD.fB := by unfold CxD.fY CxD.fB; split_ifs <;> decide
lemma CxD.fX_ne_fB (d : CxD) : d.fX ≠ CxD.fB := by unfold CxD.fX CxD.fB; split_ifs <;> decide
lemma CxD.fX_ne_fT (d : CxD) : d.fX ≠ CxD.fT := by unfold CxD.fX CxD.fT; split_ifs <;> decide
lemma CxD.fY_ne_fT (d : CxD) : d.fY ≠ CxD.fT := by unfold CxD.fY CxD.fT; split_ifs <;> decide
lemma CxD.fU_ne_fT : CxD.fU ≠ CxD.fT := by decide
lemma CxD.len11_fB (d : CxD) : d.len11 CxD.fB = d.nG := rfl
lemma CxD.len11_fT (d : CxD) : d.len11 CxD.fT = d.nn * d.G := rfl
lemma CxD.len11_fU (d : CxD) : d.len11 CxD.fU = d.nG := rfl

lemma CxD.nG_le_L (hv : d.Valid) : d.nG ≤ d.L := by
  rw [d.L_eq hv, Nat.add_mul, one_mul]
  have := Nat.mul_le_mul_left d.nn (show d.G ≤ d.K by have := hv.hGK; omega)
  unfold CxD.nG
  omega

lemma CxD.ρK_le_L (hv : d.Valid) : d.ρ + d.nn * d.K ≤ d.L := by
  rw [d.L_eq hv, Nat.add_mul, one_mul]
  have := hv.hρ
  omega

/-- The control fields lie above the slots, the borrow field below them, and the source slot
above the target slot when `y < x`. -/
lemma CxD.above (hv : d.Valid) :
    foff d.len11 d.fY + d.len11 d.fY ≤ foff d.len11 CxD.fT ∧
      foff d.len11 d.fY + d.len11 d.fY ≤ foff d.len11 CxD.fU ∧
      foff d.len11 CxD.fB + d.len11 CxD.fB ≤ foff d.len11 d.fX ∧
      foff d.len11 CxD.fB + d.len11 CxD.fB ≤ foff d.len11 d.fY ∧
      foff d.len11 CxD.fB + d.len11 CxD.fB ≤ foff d.len11 CxD.fU ∧
      (d.y < d.x → foff d.len11 d.fY + d.len11 d.fY ≤ foff d.len11 d.fX) := by
  obtain ⟨hhiL, hhi1, hpU, hbT, hbU, hBlo, hhiT, hUn, hpT⟩ := d.arith hv
  obtain ⟨o1, o3, o5, o7, o9⟩ := d.foff11 hv
  obtain ⟨l1, l3, l5, l7, l9⟩ := d.len11_lit
  have h1 := Nat.mul_le_mul_right d.nG hv.hpT
  unfold CxD.fX CxD.fY CxD.fB CxD.fT CxD.fU
  split_ifs with h
  · simp only [o1, o3, o5, o7, o9, l1, l3, l5]
    omega
  · simp only [o1, o3, o5, o7, o9, l1, l3, l5]
    omega

namespace CxInstr

/-- The control field of the core: `U` or the source slot. -/
def ctrl (d : CxD) (ctrlU : Bool) : Fin 11 := if ctrlU then CxD.fU else d.fX
/-- The offset of the control bits. -/
def oA (d : CxD) (ctrlU : Bool) : ℕ := if ctrlU then 0 else d.ρ
/-- The stride of the control bits. -/
def sA (d : CxD) (ctrlU : Bool) : ℕ := if ctrlU then d.G else d.K

/-- The instructions whose control field lies above the rotated slot. -/
def ok (d : CxD) : CxInstr → Prop
  | swapTB => True
  | swapUB => True
  | rotYW ctrlU _ => ctrlU = false → d.y < d.x
  | rotBbY => True
  | rotYb ctrlU => ctrlU = false → d.y < d.x
  | rotBx ctrlU => ctrlU = false → d.y < d.x
  | rotBbX _ => True

lemma prog_ok (d : CxD) (hv : d.Valid) : ∀ i ∈ prog d, i.ok d := by
  have hxy := hv.hxy
  unfold prog
  split_ifs with h
  · simp [core, loadU, ok]
  · simp [core, ok] <;> omega

/-- The preparation cost of an instruction (`0` for an interchange). -/
def prepC (d : CxD) : CxInstr → ℕ
  | swapTB => 0
  | swapUB => 0
  | rotYW ctrlU _ => prepCost true (pdataP d.len11 (ctrl d ctrlU) d.fY CxD.fT (d.len11 d.fY) d.ρ
      (oA d ctrlU) d.ρ (sA d ctrlU) d.K d.G d.nn (d.K - 1 - d.G) 0) (d.len11 d.fY)
  | rotBbY => prepCost false (pdataP d.len11 d.fY d.fX CxD.fT (d.len11 CxD.fB) 0 d.ρ d.ρ d.K d.K
      d.G d.nn (d.G - 1) 0) (d.len11 CxD.fB)
  | rotYb ctrlU => prepCost false (pdataP d.len11 (ctrl d ctrlU) d.fY CxD.fT (d.len11 d.fY) d.ρ
      (oA d ctrlU) d.ρ (sA d ctrlU) d.K d.G d.nn (d.K - 1) 0) (d.len11 d.fY)
  | rotBx ctrlU => prepCost false (pdataP d.len11 (ctrl d ctrlU) d.fY CxD.fT (d.len11 CxD.fB) 0
      (oA d ctrlU) d.ρ (sA d ctrlU) d.K d.G d.nn (d.G - 1) 0) (d.len11 CxD.fB)
  | rotBbX _ => prepCost false (pdataP d.len11 d.fX d.fY CxD.fT (d.len11 CxD.fB) 0 d.ρ d.ρ d.K d.K
      d.G d.nn (d.G - 1) 0) (d.len11 CxD.fB)

/-- The step bound of an instruction. -/
noncomputable def cost (d : CxD) (T : ℕ) : CxInstr → ℝ
  | swapTB => sxSwapCost d.swapD T
  | swapUB => sxSwapCost d.swapD T
  | rotYW ctrlU neg => cxRotCost d (prepC d (rotYW ctrlU neg))
  | rotBbY => cxRotCost d (prepC d rotBbY)
  | rotYb ctrlU => cxRotCost d (prepC d (rotYb ctrlU))
  | rotBx ctrlU => cxRotCost d (prepC d (rotBx ctrlU))
  | rotBbX neg => cxRotCost d (prepC d (rotBbX neg))

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- The pass of one instruction. -/
noncomputable def pass {Ka : ℕ} (henv : CxEnv ι par src) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (st : Fin T) (d : CxD) : CxInstr → Pr P T Q (prime + Ka) U
  | swapTB => cxSwapPass henv hQ st 1 2
  | swapUB => cxSwapPass henv hQ st 0 2
  | rotYW ctrlU neg => cxRotPass ι par src st d.fY neg (if ctrlU then 1 else 0) false true
      (ctrl d ctrlU) d.fY CxD.fT
  | rotBbY => cxRotPass ι par src st CxD.fB false 2 false false d.fY d.fX CxD.fT
  | rotYb ctrlU => cxRotPass ι par src st d.fY false (if ctrlU then 4 else 3) false false
      (ctrl d ctrlU) d.fY CxD.fT
  | rotBx ctrlU => cxRotPass ι par src st CxD.fB true (if ctrlU then 6 else 5) true false
      (ctrl d ctrlU) d.fY CxD.fT
  | rotBbX neg => cxRotPass ι par src st CxD.fB neg 2 false false d.fX d.fY CxD.fT

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- The passes of a list of instructions. -/
noncomputable def passes {Ka : ℕ} (henv : CxEnv ι par src)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (st : Fin T) (d : CxD) :
    List CxInstr → Pr P T Q (prime + Ka) U
  | [] => .act .done
  | i :: is => .seq (pass henv hQ st d i) (passes henv hQ st d is)

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
lemma pass_ofXY {Ka : ℕ} (henv : CxEnv ι par src) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (st : Fin T) (d : CxD) (i : CxInstr) :
    pass (Ka := Ka) (P := P) (U := U) henv hQ st (CxD.ofXY d.x d.y) i = pass henv hQ st d i := by
  cases i <;> rfl

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
lemma passes_ofXY {Ka : ℕ} (henv : CxEnv ι par src) (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (st : Fin T) (d : CxD) : ∀ l : List CxInstr,
    passes (Ka := Ka) (P := P) (U := U) henv hQ st (CxD.ofXY d.x d.y) l = passes henv hQ st d l
  | [] => rfl
  | i :: l => by rw [passes, passes, pass_ofXY, passes_ofXY henv hQ st d l]

end CxInstr

/-- A rotation pass as an instruction of the program over `n` address bits. -/
theorem cxRot_instr (henv : CxEnv ι par src) (hst : ∀ x, ι x ≠ st) (hv : d.Valid)
    (tf : Fin 11) (htf : d.len11 tf ≤ d.L)
    (hlenReg : d.len11 tf = if tf = CxD.fB then d.nG else d.L) (neg : Bool) (t : Fin 7)
    (useY useT : Bool) (fA fY fT : Fin 11) {off : ℕ → ℕ} (hoff : HighOff d.len11 tf off)
    (hob : ∀ i, off i < 2 ^ d.len11 tf) {cP : ℕ} {P₀ : Fin 9 → List (Fin (A + 4))}
    (hprep : PrepSpec body (prepOff useY useT (rotι ι src t ∘ embedP fA fY fT))
      (fun g => rotι ι src t (.fld g)) d.len11 (d.len11 tf)
      (fun r => rotι ι src t (RotGReg.rsRegG tf r)) (fun r => rotι ι src t (.spare r))
      (rsrcR tf off) (fun s => rotι ι src t (.scr s)) (fun q => rotι ι src t (.prm q)) P₀ cP)
    (hP₀ : ∀ q, cxBc A d (.val (bankVal t q)) = P₀ q)
    (hWF : (CInstr.rot tf neg off).WF d.len11 d.n)
    {X : List (List (Fin (A + 4)))} (hX : X.length = d.M) (hXB : ∀ r ∈ X, r.length = d.Bk)
    {R₁ : Fin T → List (Fin (A + 4))} (hpar : (R₁ (par .L)).length = d.L) (v : HS T Q A U)
    (S : Stacks T A) (hS : CxState ι d R₁ S.R) (hR₁ : R₁ src = X.flatten)
    (hcl : (S.R (ι .comp)).length ≤ d.L) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ cxRotCost d cP ∧
      Exec body (cxRotPass ι par src st tf neg t useY useT fA fY fT) (mk v S) m
        (mk v' { S with R := R' }) ∧
      R' src = (moveRecs (Layer.CompactXor.instrPerm d.len11 (R := d.R) (S := d.n) hWF) X).flatten ∧
      CxState ι d (Function.update R₁ src
        (moveRecs (Layer.CompactXor.instrPerm d.len11 (R := d.R) (S := d.n) hWF) X).flatten) R' ∧
      (R' (ι .comp)).length ≤ d.L := by
  have key : moveRecs (rotPerm d.len11 tf neg d.R hoff) X =
      moveRecs (Layer.CompactXor.instrPerm d.len11 (R := d.R) (S := d.n) hWF) X :=
    moveRecs_congr _ _ (by rw [d.sum_len11 hv]) (fun x hx hx' => by
      rw [rotPerm, Layer.CompactXor.instrPerm_apply, Layer.CompactXor.instrPerm_apply]) X
  rw [← key]
  exact cxRot_exec body henv hst hv (d.sum_len11 hv) tf htf hlenReg neg t useY useT fA fY fT hoff
    hob hprep hP₀ hX hXB hpar v S hS hR₁ hcl

set_option maxHeartbeats 1000000 in
open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- **One instruction** on the built registers. -/
theorem cxInstr_exec {Ka : ℕ} (body : P → Pr P T Q (prime + Ka) U) (henv : CxEnv ι par src)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (hst : ∀ x, ι x ≠ st) (hv : d.Valid)
    (i : CxInstr) (hok : i.ok d) (hWF : (i.toC d).WF d.len11 d.n)
    {X : List (List (Fin (prime + Ka + 4)))} (hX : X.length = d.M)
    (hXB : ∀ r ∈ X, r.length = d.Bk) (hX8 : ∀ r ∈ X, ∀ s ∈ r, s.val < 8)
    {R₁ : Fin T → List (Fin (prime + Ka + 4))} (hpar : (R₁ (par .L)).length = d.L)
    (v : HS T Q (prime + Ka) U) (S : Stacks T (prime + Ka)) (hL : ∀ y, S.L y = [])
    (hS : CxState ι d R₁ S.R) (hR₁ : R₁ src = X.flatten) (hcl : (S.R (ι .comp)).length ≤ d.L) :
    ∃ (v' : HS T Q (prime + Ka) U) (R' : Fin T → List (Fin (prime + Ka + 4))) (m : ℕ),
      v'.user = v.user ∧ (m : ℝ) ≤ i.cost d T ∧
      Exec body (i.pass henv hQ st d) (mk v S) m (mk v' { S with R := R' }) ∧
      R' src = (moveRecs (Layer.CompactXor.instrPerm d.len11 (R := d.R) (S := d.n) hWF) X).flatten ∧
      CxState ι d (Function.update R₁ src
        (moveRecs (Layer.CompactXor.instrPerm d.len11 (R := d.R) (S := d.n) hWF) X).flatten) R' ∧
      (R' (ι .comp)).length ≤ d.L := by
  obtain ⟨o1, o3, o5, o7, o9⟩ := d.foff11 hv
  obtain ⟨hYT, hYU, hBX, hBY, hBU, hYX⟩ := d.above hv
  have hρ := hv.hρ
  have hGK : d.G + 1 ≤ d.K := by have := hv.hGK; omega
  have hG := hv.hG
  have hK : 1 ≤ d.K := by omega
  have hLeq := d.L_eq hv
  have hρK := d.ρK_le_L hv
  have hUG : 0 + d.nn * d.G ≤ d.len11 CxD.fU := by rw [d.len11_fU]; unfold CxD.nG; omega
  have hρKX : d.ρ + d.nn * d.K ≤ d.len11 d.fX := by rw [d.len11_fX]; exact hρK
  have hρKY : d.ρ + d.nn * d.K ≤ d.len11 d.fY := by rw [d.len11_fY]; exact hρK
  have hYlen : d.len11 d.fY = (d.nn + 1) * d.K := by rw [d.len11_fY, hLeq]
  have hTlen : d.len11 CxD.fT = d.nn * d.G := rfl
  have hYreg : d.len11 d.fY = if d.fY = CxD.fB then d.nG else d.L := by
    rw [if_neg d.fY_ne_fB, d.len11_fY]
  have hBreg : d.len11 CxD.fB = if CxD.fB = CxD.fB then d.nG else d.L := by
    rw [if_pos rfl]; rfl
  have hYle : d.len11 d.fY ≤ d.L := by rw [d.len11_fY]
  have hBle : d.len11 CxD.fB ≤ d.L := by rw [d.len11_fB]; exact d.nG_le_L hv
  have hrι := rotι_injective henv
  cases i with
  | swapTB =>
      obtain ⟨v', m, hu, hm, he⟩ := cxSwap_exec body henv hQ hv o1 o7 o9 (a := 1) (b := 2) hWF
        hX hXB hX8 v S hL hS hR₁
      refine ⟨v', _, m, hu, by simpa [CxInstr.cost] using hm, he, ?_, hS.update_src henv _, ?_⟩
      · rw [Function.update_self]; rfl
      · rw [Function.update_of_ne (henv.hsrc _)]; exact hcl
  | swapUB =>
      obtain ⟨v', m, hu, hm, he⟩ := cxSwap_exec body henv hQ hv o1 o7 o9 (a := 0) (b := 2) hWF
        hX hXB hX8 v S hL hS hR₁
      refine ⟨v', _, m, hu, by simpa [CxInstr.cost] using hm, he, ?_, hS.update_src henv _, ?_⟩
      · rw [Function.update_self]; rfl
      · rw [Function.update_of_ne (henv.hsrc _)]; exact hcl
  | rotYW ctrlU neg =>
      cases ctrlU with
      | false =>
          have hYX' := hYX (hok rfl)
          have hlt := offYW_lt (len := d.len11) (T := CxD.fT) (A := d.fX) (K := d.K) (ρ := d.ρ)
            (G := d.G) (n := d.nn) (oA := d.ρ) (sA := d.K) hρ hGK
          obtain ⟨v', R', m, hu, hm, he, hsrc, hS', hcl'⟩ := cxRot_instr body henv hst hv d.fY
            hYle hYreg neg 0 false true d.fX d.fY CxD.fT
            (highOff_offYW d.len11 CxD.fT d.fY d.fX d.K d.ρ d.G d.nn d.ρ d.K hYX' hYT)
            (fun i => by rw [hYlen]; exact hlt i)
            (prepSpec_offYW body d.len11 (hrι 0) d.fX d.fY CxD.fT d.fX_ne_fY d.fX_ne_fT d.fY_ne_fT
              d.ρ d.K d.K d.ρ d.G d.nn hρKX hYlen hTlen hρ hGK)
            (fun q => by fin_cases q <;> simp [cxBc, CxD.valOf, bankVal, prmP, d.len11_fY])
            hWF hX hXB hpar v S hS hR₁ hcl
          refine ⟨v', R', m, hu, ?_, he, hsrc, hS', hcl'⟩
          simp only [CxInstr.cost, CxInstr.prepC, CxInstr.ctrl, CxInstr.oA, CxInstr.sA,
            Bool.false_eq_true, ↓reduceIte]
          exact_mod_cast hm
      | true =>
          have hlt := offYW_lt (len := d.len11) (T := CxD.fT) (A := CxD.fU) (K := d.K) (ρ := d.ρ)
            (G := d.G) (n := d.nn) (oA := 0) (sA := d.G) hρ hGK
          obtain ⟨v', R', m, hu, hm, he, hsrc, hS', hcl'⟩ := cxRot_instr body henv hst hv d.fY
            hYle hYreg neg 1 false true CxD.fU d.fY CxD.fT
            (highOff_offYW d.len11 CxD.fT d.fY CxD.fU d.K d.ρ d.G d.nn 0 d.G hYU hYT)
            (fun i => by rw [hYlen]; exact hlt i)
            (prepSpec_offYW body d.len11 (hrι 1) CxD.fU d.fY CxD.fT d.fU_ne_fY CxD.fU_ne_fT
              d.fY_ne_fT 0 d.G d.K d.ρ d.G d.nn hUG hYlen hTlen hρ hGK)
            (fun q => by fin_cases q <;> simp [cxBc, CxD.valOf, bankVal, prmP, d.len11_fY])
            hWF hX hXB hpar v S hS hR₁ hcl
          refine ⟨v', R', m, hu, ?_, he, hsrc, hS', hcl'⟩
          simp only [CxInstr.cost, CxInstr.prepC, CxInstr.ctrl, CxInstr.oA, CxInstr.sA,
            ↓reduceIte]
          exact_mod_cast hm
  | rotBbY =>
      have hlt := offBb_lt (len := d.len11) (A := d.fY) (G := d.G) (n := d.nn) (oA := d.ρ)
        (sA := d.K) hG
      obtain ⟨v', R', m, hu, hm, he, hsrc, hS', hcl'⟩ := cxRot_instr body henv hst hv CxD.fB
        hBle hBreg false 2 false false d.fY d.fX CxD.fT
        (highOff_offBb d.len11 CxD.fB d.fY d.G d.nn d.ρ d.K hBY)
        (fun i => by rw [d.len11_fB]; exact hlt i)
        (prepSpec_offBb body d.len11 (hrι 2) CxD.fB d.fY d.fX CxD.fT d.fX_ne_fY.symm d.fY_ne_fT
          d.fX_ne_fT d.ρ d.K d.ρ d.K d.G d.nn hρKY hρKX hG)
        (fun q => by fin_cases q <;> simp [cxBc, CxD.valOf, bankVal, prmP, d.len11_fB])
        hWF hX hXB hpar v S hS hR₁ hcl
      refine ⟨v', R', m, hu, ?_, he, hsrc, hS', hcl'⟩
      simp only [CxInstr.cost, CxInstr.prepC]
      exact_mod_cast hm
  | rotYb ctrlU =>
      cases ctrlU with
      | false =>
          have hYX' := hYX (hok rfl)
          have hlt := offYb_lt (len := d.len11) (A := d.fX) (K := d.K) (ρ := d.ρ) (n := d.nn)
            (oA := d.ρ) (sA := d.K) hρ hK
          obtain ⟨v', R', m, hu, hm, he, hsrc, hS', hcl'⟩ := cxRot_instr body henv hst hv d.fY
            hYle hYreg false 3 false false d.fX d.fY CxD.fT
            (highOff_offYb d.len11 d.fY d.fX d.K d.ρ d.nn d.ρ d.K hYX')
            (fun i => by rw [hYlen]; exact hlt i)
            (prepSpec_offYb body d.len11 (hrι 3) d.fX d.fY CxD.fT d.fX_ne_fY d.fX_ne_fT d.fY_ne_fT
              d.ρ d.K d.K d.ρ d.G d.nn hρKX hYlen hρ hK)
            (fun q => by fin_cases q <;> simp [cxBc, CxD.valOf, bankVal, prmP, d.len11_fY])
            hWF hX hXB hpar v S hS hR₁ hcl
          refine ⟨v', R', m, hu, ?_, he, hsrc, hS', hcl'⟩
          simp only [CxInstr.cost, CxInstr.prepC, CxInstr.ctrl, CxInstr.oA, CxInstr.sA,
            Bool.false_eq_true, ↓reduceIte]
          exact_mod_cast hm
      | true =>
          have hlt := offYb_lt (len := d.len11) (A := CxD.fU) (K := d.K) (ρ := d.ρ) (n := d.nn)
            (oA := 0) (sA := d.G) hρ hK
          obtain ⟨v', R', m, hu, hm, he, hsrc, hS', hcl'⟩ := cxRot_instr body henv hst hv d.fY
            hYle hYreg false 4 false false CxD.fU d.fY CxD.fT
            (highOff_offYb d.len11 d.fY CxD.fU d.K d.ρ d.nn 0 d.G hYU)
            (fun i => by rw [hYlen]; exact hlt i)
            (prepSpec_offYb body d.len11 (hrι 4) CxD.fU d.fY CxD.fT d.fU_ne_fY CxD.fU_ne_fT
              d.fY_ne_fT 0 d.G d.K d.ρ d.G d.nn hUG hYlen hρ hK)
            (fun q => by fin_cases q <;> simp [cxBc, CxD.valOf, bankVal, prmP, d.len11_fY])
            hWF hX hXB hpar v S hS hR₁ hcl
          refine ⟨v', R', m, hu, ?_, he, hsrc, hS', hcl'⟩
          simp only [CxInstr.cost, CxInstr.prepC, CxInstr.ctrl, CxInstr.oA, CxInstr.sA,
            ↓reduceIte]
          exact_mod_cast hm
  | rotBx ctrlU =>
      cases ctrlU with
      | false =>
          have hlt := offBx_lt (len := d.len11) (Y := d.fY) (A := d.fX) (K := d.K) (ρ := d.ρ)
            (G := d.G) (n := d.nn) (oA := d.ρ) (sA := d.K) hG
          obtain ⟨v', R', m, hu, hm, he, hsrc, hS', hcl'⟩ := cxRot_instr body henv hst hv CxD.fB
            hBle hBreg true 5 true false d.fX d.fY CxD.fT
            (highOff_offBx d.len11 d.fY CxD.fB d.fX d.K d.ρ d.G d.nn d.ρ d.K hBX hBY)
            (fun i => by rw [d.len11_fB]; exact hlt i)
            (prepSpec_offBx body d.len11 (hrι 5) CxD.fB d.fX d.fY CxD.fT d.fX_ne_fY d.fX_ne_fT
              d.fY_ne_fT d.ρ d.K d.K d.ρ d.G d.nn hρKX hYlen hρ hG)
            (fun q => by fin_cases q <;> simp [cxBc, CxD.valOf, bankVal, prmP, d.len11_fB])
            hWF hX hXB hpar v S hS hR₁ hcl
          refine ⟨v', R', m, hu, ?_, he, hsrc, hS', hcl'⟩
          simp only [CxInstr.cost, CxInstr.prepC, CxInstr.ctrl, CxInstr.oA, CxInstr.sA,
            Bool.false_eq_true, ↓reduceIte]
          exact_mod_cast hm
      | true =>
          have hlt := offBx_lt (len := d.len11) (Y := d.fY) (A := CxD.fU) (K := d.K) (ρ := d.ρ)
            (G := d.G) (n := d.nn) (oA := 0) (sA := d.G) hG
          obtain ⟨v', R', m, hu, hm, he, hsrc, hS', hcl'⟩ := cxRot_instr body henv hst hv CxD.fB
            hBle hBreg true 6 true false CxD.fU d.fY CxD.fT
            (highOff_offBx d.len11 d.fY CxD.fB CxD.fU d.K d.ρ d.G d.nn 0 d.G hBU hBY)
            (fun i => by rw [d.len11_fB]; exact hlt i)
            (prepSpec_offBx body d.len11 (hrι 6) CxD.fB CxD.fU d.fY CxD.fT d.fU_ne_fY
              CxD.fU_ne_fT d.fY_ne_fT 0 d.G d.K d.ρ d.G d.nn hUG hYlen hρ hG)
            (fun q => by fin_cases q <;> simp [cxBc, CxD.valOf, bankVal, prmP, d.len11_fB])
            hWF hX hXB hpar v S hS hR₁ hcl
          refine ⟨v', R', m, hu, ?_, he, hsrc, hS', hcl'⟩
          simp only [CxInstr.cost, CxInstr.prepC, CxInstr.ctrl, CxInstr.oA, CxInstr.sA,
            ↓reduceIte]
          exact_mod_cast hm
  | rotBbX neg =>
      have hlt := offBb_lt (len := d.len11) (A := d.fX) (G := d.G) (n := d.nn) (oA := d.ρ)
        (sA := d.K) hG
      obtain ⟨v', R', m, hu, hm, he, hsrc, hS', hcl'⟩ := cxRot_instr body henv hst hv CxD.fB
        hBle hBreg neg 2 false false d.fX d.fY CxD.fT
        (highOff_offBb d.len11 CxD.fB d.fX d.G d.nn d.ρ d.K hBX)
        (fun i => by rw [d.len11_fB]; exact hlt i)
        (prepSpec_offBb body d.len11 (hrι 2) CxD.fB d.fX d.fY CxD.fT d.fX_ne_fY d.fX_ne_fT
          d.fY_ne_fT d.ρ d.K d.ρ d.K d.G d.nn hρKX hρKY hG)
        (fun q => by fin_cases q <;> simp [cxBc, CxD.valOf, bankVal, prmP, d.len11_fB])
        hWF hX hXB hpar v S hS hR₁ hcl
      refine ⟨v', R', m, hu, ?_, he, hsrc, hS', hcl'⟩
      simp only [CxInstr.cost, CxInstr.prepC]
      exact_mod_cast hm

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- **The instruction list** on the built registers. -/
theorem cxInstrs_exec {Ka : ℕ} (body : P → Pr P T Q (prime + Ka) U) (henv : CxEnv ι par src)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (hst : ∀ x, ι x ≠ st) (hv : d.Valid) :
    ∀ (is : List CxInstr), (∀ i ∈ is, i.ok d) →
    ∀ (hWF : ∀ ins ∈ is.map (CxInstr.toC d), ins.WF d.len11 d.n),
    ∀ (X : List (List (Fin (prime + Ka + 4)))), X.length = d.M → (∀ r ∈ X, r.length = d.Bk) →
      (∀ r ∈ X, ∀ s ∈ r, s.val < 8) →
    ∀ (R₁ : Fin T → List (Fin (prime + Ka + 4))), (R₁ (par .L)).length = d.L →
    ∀ (v : HS T Q (prime + Ka) U) (S : Stacks T (prime + Ka)), (∀ y, S.L y = []) →
      CxState ι d R₁ S.R → R₁ src = X.flatten → (S.R (ι .comp)).length ≤ d.L →
    ∃ (v' : HS T Q (prime + Ka) U) (R' : Fin T → List (Fin (prime + Ka + 4))) (m : ℕ),
      v'.user = v.user ∧ (m : ℝ) ≤ (is.map (CxInstr.cost d T)).sum + 1 ∧
      Exec body (CxInstr.passes henv hQ st d is) (mk v S) m (mk v' { S with R := R' }) ∧
      R' src = (moveRecs (Layer.CompactXor.progPerm d.len11 (R := d.R) (S := d.n)
        (is.map (CxInstr.toC d)) hWF) X).flatten ∧
      CxState ι d (Function.update R₁ src (moveRecs (Layer.CompactXor.progPerm d.len11 (R := d.R)
        (S := d.n) (is.map (CxInstr.toC d)) hWF) X).flatten) R' ∧
      (R' (ι .comp)).length ≤ d.L := by
  intro is
  induction is with
  | nil =>
      intro _ hWF X hX _ _ R₁ _ v S _ hS hR₁ hcl
      refine ⟨v, S.R, 1, rfl, by simp, Exec.cast (Exec.act (body := body) .done (mk v S)) rfl ?_,
        ?_, ?_, hcl⟩
      · rw [run_done]
      · rw [hS.srcVal henv, hR₁]
        show _ = (moveRecs (Equiv.refl (Fin (d.R * 2 ^ d.n))) X).flatten
        rw [sx_moveRecs_refl (M := d.R * 2 ^ d.n) X hX]
      · show CxState ι d (Function.update R₁ src
          (moveRecs (Equiv.refl (Fin (d.R * 2 ^ d.n))) X).flatten) S.R
        rw [sx_moveRecs_refl (M := d.R * 2 ^ d.n) X hX, ← hR₁, Function.update_eq_self]
        exact hS
  | cons i is ih =>
      intro hok hWF X hX hXB hX8 R₁ hpar v S hL hS hR₁ hcl
      obtain ⟨v₁, R₂, m₁, hu₁, hm₁, he₁, hsrc₁, hS₁, hcl₁⟩ := cxInstr_exec body henv hQ hst hv i
        (hok i List.mem_cons_self) (hWF _ List.mem_cons_self) hX hXB hX8 hpar v S hL hS hR₁ hcl
      set X' := moveRecs (Layer.CompactXor.instrPerm d.len11 (R := d.R) (S := d.n) (hWF _ List.mem_cons_self)) X
        with hX'
      have hX'l : X'.length = d.M := length_moveRecs _ _
      have hmem : ∀ r ∈ X', r ∈ X := fun r hr => mem_moveRecs _ hX hr
      obtain ⟨v', R', m', hu', hm', he', hsrc', hS', hcl'⟩ := ih
        (fun j hj => hok j (List.mem_cons_of_mem _ hj))
        (fun ins hins => hWF ins (List.mem_cons_of_mem _ hins)) X' hX'l
        (fun r hr => hXB r (hmem r hr)) (fun r hr => hX8 r (hmem r hr))
        (Function.update R₁ src X'.flatten) (by rw [Function.update_of_ne (henv.hsrcp _)]; exact hpar)
        v₁ { S with R := R₂ } hL hS₁ (by rw [Function.update_self]) hcl₁
      have hR : moveRecs (Layer.CompactXor.progPerm d.len11 (R := d.R) (S := d.n)
          ((i :: is).map (CxInstr.toC d)) hWF) X =
          moveRecs (Layer.CompactXor.progPerm d.len11 (R := d.R) (S := d.n)
            (is.map (CxInstr.toC d)) fun ins hins => hWF ins (List.mem_cons_of_mem _ hins)) X' := by
        rw [hX']
        exact moveRecs_progPerm_cons d.len11 (CxInstr.toC d i) (is.map (CxInstr.toC d)) hWF X hX
      refine ⟨v', R', m₁ + m', hu'.trans hu₁, ?_, Exec.seq he₁ he', ?_, ?_, hcl'⟩
      · push_cast
        simp only [List.map_cons, List.sum_cons]
        linarith
      · rw [hR]; exact hsrc'
      · rw [hR, ← Function.update_idem]; exact hS'


/-! ### The machine -/

open IntegerMultBounds.MathlibTM2.Layer (ZArr encZ recList pullM m)

lemma CxD.foff_fX (hv : d.Valid) : foff d.len11 d.fX = d.a₀ + d.x * d.L := by
  obtain ⟨-, o3, o5, -, -⟩ := d.foff11 hv
  unfold CxD.fX
  split_ifs with h
  · rw [o3]; unfold CxD.lo; rw [min_eq_left h.le]
  · rw [o5]; unfold CxD.hi; rw [max_eq_left (by omega)]

lemma CxD.foff_fY (hv : d.Valid) : foff d.len11 d.fY = d.a₀ + d.y * d.L := by
  obtain ⟨-, o3, o5, -, -⟩ := d.foff11 hv
  have hxy := hv.hxy
  unfold CxD.fY
  split_ifs with h
  · rw [o5]; unfold CxD.hi; rw [max_eq_right h.le]
  · rw [o3]; unfold CxD.lo; rw [min_eq_right (by omega)]

lemma progPerm_congr {nf : ℕ} (len : Fin nf → ℕ) {R S : ℕ} {P P' : List (CInstr nf)}
    (hPP : P = P') (h : ∀ ins ∈ P, ins.WF len S) (h' : ∀ ins ∈ P', ins.WF len S) :
    Layer.CompactXor.progPerm len (R := R) P h = Layer.CompactXor.progPerm len (R := R) P' h' := by
  subst hPP; rfl

/-- The exceptional addresses of the compact program. -/
noncomputable def cxBad (d : CxD) : ℕ :=
  Fintype.card {j : Fin d.M // CBad d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn j}

/-- The step bound of the machine: the setup, the key pass, the instructions, the clearing of
the computed register, the repair, the fix pass and the cleanup. -/
noncomputable def cxCost (A : ℕ) (d : CxD) (T : ℕ) : ℝ :=
  ((∑ i ∈ Finset.range 37, cxStageCost d (i + 1) + 1 + cxKeyCost d + (2 * d.L + 2) +
    cxRepairCost d (cxBad d) + cxFixCost d + cxCleanupCost (A := A) d : ℕ) : ℝ) +
    (((CxInstr.prog d).map (CxInstr.cost d T)).sum + 1)

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- **The compact slot XOR machine**: the setup, the key pass, the compact program, the
clearing of the computed register, the repair, the fix pass and the cleanup. -/
noncomputable def compactXorProg {Ka : ℕ} (henv : CxEnv ι par src)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (st : Fin T) (d : CxD) :
    Pr P T Q (prime + Ka) U :=
  .seq (.seq (.seq (.seq (.seq (.seq (cxSetup ι par d) (cxKeyPass ι d src st))
    (CxInstr.passes henv hQ st d (CxInstr.prog d))) (uclear (ι .comp)))
    (cxRepairPass ι d src st)) (cxFixPass ι d src st)) (cxCleanup ι)

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- The program depends on the data only through the static slots. -/
lemma compactXorProg_ofXY {Ka : ℕ} (henv : CxEnv ι par src)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (st : Fin T) (d : CxD) :
    compactXorProg (Ka := Ka) (P := P) (U := U) henv hQ st (CxD.ofXY d.x d.y) =
      compactXorProg henv hQ st d := by
  unfold compactXorProg
  rw [cxSetup_ofXY, CxInstr.passes_ofXY]
  rfl

set_option maxHeartbeats 1000000 in
open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- **The main theorem of the compact slot XOR**: on the encoded rectangle `Z` in `src`, the
machine performs the slot XOR `y ← y ⊕ x` at the selected positions: column `c` of slot `y`
gains column `c` of slot `x`. Every other register ends as it started and `user` is kept. -/
theorem compactXor_exec {Ka : ℕ} (body : P → Pr P T Q (prime + Ka) U) (henv : CxEnv ι par src)
    (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (hst : ∀ x, ι x ≠ st) (hsrcst : src ≠ st)
    (hA : 12 ≤ prime + Ka) (hv : d.Valid) {r w : ℕ} (hrw : d.rw = r * w) {x y : Fin m}
    (hx : d.x = x) (hy : d.y = y) {e : Fin (m * d.k) → Fin d.n}
    (he : ∀ i, (e i : ℕ) = d.a₀ + d.ρ + d.K * i) (Z : ZArr (Fin d.R × Fin r) d.n)
    (v : HS T Q (prime + Ka) U) (S : Stacks T (prime + Ka)) (hL : ∀ y, S.L y = [])
    (hSsrc : S.R src = encZ (prime + Ka) w Z) (hpar : ∀ p, (S.R (par p)).length = d.par p)
    (hrest : ∀ x, S.R (ι x) = []) :
    ∃ (v' : HS T Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      (c : ℝ) ≤ cxCost (prime + Ka) d T ∧
      Exec body (compactXorProg henv hQ st d) (mk v S) c
        (mk v' { S with
          R := Function.update S.R src (encZ (prime + Ka) w (pullM e (sxXorCol x y) Z)) }) := by
  have hLeq := d.L_eq hv
  have hsum11 := d.sum_len11 hv
  have hsum8 : ∑ j, d.len8 j = d.kl := d.sum_len8 hv
  have hSY := d.hSY11 hv
  obtain ⟨hl, hlB', hl8⟩ := sx_recSyms_facts (by omega : 4 ≤ prime + Ka) (w := w) Z
  set l := (recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms (prime + Ka) w)
    with hldef
  have hlM : l.length = d.M := hl
  have hlB : ∀ q ∈ l, q.length = d.rw := by rw [hrw]; exact hlB'
  -- the setup
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := cxSetup_exec body henv hpar hv hrest v S rfl
  -- the key pass
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := cxKey_exec body henv hst hsrcst hv hsum8 hlM hlB v₁
    { S with R := cxFill ι (cxBc (prime + Ka) d) 37 S.R } rfl
    (by rw [hSsrc, sx_encZ_eq_flatten])
  set πI := idealPerm d.len11 d.K d.ρ d.nn (R := d.R) d.fX_ne_fY d.len11_fX_fY hSY with hπI
  have hkey : keyedFrom (keyBitsAt d.kY d.kX d.len8 (selMask d.K d.ρ d.nn)) 0 l =
      keyRecs d.kl πI l := by
    rw [keyedFrom_eq_keyRecs_ideal d.len8 d.kX d.kY d.kX_ne_kY d.len8_kX_kY d.K d.ρ d.nn d.R d.n
      (d.hSY8 hv) l hlM, hsum8, d.idealPerm_eq8 hv]
  rw [hkey] at he₂
  set K₁ := keyRecs d.kl πI l with hK₁
  have hK₁l : K₁.length = d.M := length_keyRecs _ _ _
  have hK₁B : ∀ q ∈ K₁, q.length = d.Bk := fun q hq => by
    rw [keyRecs_length_mem _ _ _ _ hlM hlB q hq]; unfold CxD.Bk; ring
  have hK₁8 : ∀ q ∈ K₁, ∀ s ∈ q, s.val < 8 := by
    intro q hq s hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hq
    rcases List.mem_append.1 hs with hs | hs
    · simp only [binSyms, List.mem_ofFn] at hs
      obtain ⟨t, rfl⟩ := hs
      cases (Nat.testBit _ _) <;> simp [bitSymbol]
    · have hj : (j : ℕ) < l.length := by rw [hlM]; exact j.isLt
      rw [List.getD_eq_getElem _ _ hj] at hs
      exact hl8 _ (List.getElem_mem hj) s hs
  set R₂ := Function.update S.R src K₁.flatten with hR₂
  -- the program
  have hWF : ∀ ins ∈ (CxInstr.prog d).map (CxInstr.toC d), ins.WF d.len11 d.n := by
    rw [CxInstr.prog_toC]; exact d.prog_WF hv
  obtain ⟨v₃, R₃, m₃, hu₃, hm₃, he₃, hsrc₃, hS₃, hcl₃⟩ := cxInstrs_exec body henv hQ hst hv
    (CxInstr.prog d) (CxInstr.prog_ok d hv) hWF K₁ hK₁l hK₁B hK₁8 R₂
    (by rw [hR₂, Function.update_of_ne (henv.hsrcp _), hpar]; rfl) v₂
    { S with R := cxFill ι (cxBc (prime + Ka) d) 37 R₂ } hL (fun k _ => rfl)
    (by rw [hR₂, Function.update_self])
    (by
      show (cxFill ι (cxBc (prime + Ka) d) 37 R₂ (ι .comp)).length ≤ d.L
      rw [cxFill_ι henv.hι, if_pos (cxStage_le _)]
      simp [cxBc])
  have hπS : Layer.CompactXor.progPerm d.len11 (R := d.R) (S := d.n)
      ((CxInstr.prog d).map (CxInstr.toC d)) hWF =
      Layer.CompactXor.progPerm d.len11 (R := d.R) (S := d.n) d.prog (d.prog_WF hv) :=
    progPerm_congr d.len11 (CxInstr.prog_toC d) _ _
  rw [hπS] at hsrc₃ hS₃
  set πS := Layer.CompactXor.progPerm d.len11 (R := d.R) (S := d.n) d.prog (d.prog_WF hv)
    with hπSdef
  set R₃' := Function.update R₂ src (moveRecs πS K₁).flatten with hR₃'
  -- clearing the computed register
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body (ι .comp) v₃ { S with R := R₃ }
  set R₄ := Function.update R₃ (ι .comp) [] with hR₄
  -- the repair
  have hT : ∀ a : Fin d.M, CBad d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn
      (πI a) ↔ CBad d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn a := by
    intro a
    by_cases hxy : d.x < d.y
    · rw [decide_eq_true hxy, hπI, ← d.idealPerm_eq12 hv]
      exact (d.cbad_iff_badL _).trans ((idealPerm_badL d.len12 (d.layL hv hxy) a).trans
        (d.cbad_iff_badL a).symm)
    · rw [decide_eq_false hxy, hπI, ← d.idealPerm_eq12 hv]
      exact (d.cbad_iff_badE _).trans ((idealPerm_badE d.len12 (d.layE hv hxy) a).trans
        (d.cbad_iff_badE a).symm)
  have agree : ∀ a : Fin d.M,
      ¬ CBad d.len11 (decide (d.x < d.y)) CxD.fU CxD.fT d.fY d.K d.ρ d.G d.nn a → πS a = πI a := by
    intro a ha
    by_cases hxy : d.x < d.y
    · rw [decide_eq_true hxy] at ha
      rw [hπSdef, d.progPerm_eq_progLPerm hv hxy, hπI, ← d.idealPerm_eq12 hv]
      exact progLPerm_agrees d.len12 (d.layL hv hxy) a fun h => ha ((d.cbad_iff_badL a).mpr h)
    · rw [decide_eq_false hxy] at ha
      rw [hπSdef, d.progPerm_eq_progEPerm hv hxy, hπI, ← d.idealPerm_eq12 hv]
      exact progEPerm_agrees d.len12 (d.layE hv hxy) a fun h => ha ((d.cbad_iff_badE a).mpr h)
  obtain ⟨v₅, R₅, m₅, hu₅, hm₅, he₅, hsrc₅, hS₅, hcomp₅⟩ := cxRepair_exec body hA henv hst hsrcst
    hv hsum11 hT agree l hlM hlB v₄ { S with R := R₄ } (hS₃.update_comp _)
    (by rw [hR₃', Function.update_self, hK₁]; rfl)
  -- the fix pass
  set l' := moveRecs πI l with hl'
  have hl'M : l'.length = d.M := length_moveRecs _ _
  have hl'B : ∀ q ∈ l', q.length = d.rw := moveRecs_length_mem _ _ hlM hlB
  set R₆ := Function.update R₃' src l'.flatten with hR₆
  have hR₅ : R₅ = cxFill ι (cxBc (prime + Ka) d) 37 R₆ := by
    funext k
    by_cases hk : k = ι .comp
    · subst hk
      rw [hcomp₅, cxFill_ι henv.hι, if_pos (cxStage_le _)]
      show Function.update R₃ (ι .comp) [] (ι .comp) = _
      rw [Function.update_self]
      rfl
    · exact hS₅ k hk
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := cxFix_exec body henv hst hv hsum11 hSY hl'M hl'B v₅
    { S with R := R₅ } hR₅ (by rw [hR₆, Function.update_self])
  set πF := topFixPermC d.len11 d.fX d.fY d.K d.ρ d.nn (R := d.R) d.fX_ne_fY
    (by rw [d.len11_fX, d.len11_fY]) hSY with hπF
  set R₇ := Function.update R₆ src (moveRecs πF l').flatten with hR₇
  -- the cleanup
  obtain ⟨v₇, m₇, hu₇, hm₇, he₇⟩ := cxCleanup_exec body henv (R₁ := R₇)
    (fun x => by simp [hR₇, hR₆, hR₃', hR₂, Function.update_of_ne (henv.hsrc x), hrest]) v₆
    { S with R := cxFill ι (cxBc (prime + Ka) d) 37 R₇ } rfl
  -- the result
  have hres : (moveRecs πF l').flatten = encZ (prime + Ka) w (pullM e (sxXorCol x y) Z) := by
    rw [hl', ← moveRecs_trans (M := d.R * 2 ^ d.n) _ _ _ hlM, hπI, hπF, d.fullXorPermC_eq hv, hldef]
    exact moveRecs_fullXorPermC d.len11 d.fX_ne_fY hv.hρ hv.hLK (by have := hv.hk; omega)
      (by rw [d.foff_fX hv, hx]) d.len11_fX (by rw [d.foff_fY hv, hy]) d.len11_fY
      d.len11_fX_fY hSY he Z
  have hfinal : R₇ = Function.update S.R src (encZ (prime + Ka) w (pullM e (sxXorCol x y) Z)) := by
    simp only [hR₇, hR₆, hR₃', hR₂, Function.update_idem]
    rw [hres]
  rw [← hfinal]
  refine ⟨v₇, m₁ + m₂ + m₃ +
    (2 * (({ S with R := R₃ } : Stacks T (prime + Ka)).R (ι .comp)).length + 2) + m₅ + m₆ + m₇, hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))),
    ?_, Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq he₁ he₂) he₃) he₄) he₅) he₆)
      he₇⟩
  -- the step bound
  have h4 : 2 * (({ S with R := R₃ } : Stacks T (prime + Ka)).R (ι .comp)).length + 2 ≤
      2 * d.L + 2 := by
    show 2 * (R₃ (ι .comp)).length + 2 ≤ _
    omega
  have hm₅' : m₅ ≤ cxRepairCost d (cxBad d) := hm₅
  unfold cxCost
  have h1 := (Nat.cast_le (α := ℝ)).mpr hm₁
  have h2 := (Nat.cast_le (α := ℝ)).mpr hm₂
  have h4' := (Nat.cast_le (α := ℝ)).mpr h4
  have h5 := (Nat.cast_le (α := ℝ)).mpr hm₅'
  have h6 := (Nat.cast_le (α := ℝ)).mpr hm₆
  have h7 := (Nat.cast_le (α := ℝ)).mpr hm₇
  push_cast at h1 h2 h4' h5 h6 h7 ⊢
  linarith

end Passes



end IntegerMultBounds.MathlibTM2.Node
