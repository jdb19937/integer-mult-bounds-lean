module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBLine
public import IntegerMultBounds.MathlibTM2.Mult.BandList

/-!
# The banded line solve: one forward step

The new `B̃₀` line machine solves the rounded Gaussian system by stored banded
factors. One forward step pops the final head `y` of the pending stack `vk`,
records it on `dout`, multiplies it by the next `B` stored column entries (moved
from `ef` to `xs`, with `B` copies of `y` on `ya`), and subtracts the products
from the next `B` pending records, rebuilding them through `nv`. This file gives
the program and its contract; the list semantics is `Mult.BandList.fwdZC`.

Registers are those of `RsbR`; `m2n` holds `B` symbols and `mwn` holds `B w`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node


variable {T Q A : ℕ} {U : Type} {P : Type}

section Programs

variable (rg : RsbR → Fin T)

/-- Pop the head record of `vk` onto `hv`. -/
def bandPopP : Pr P T Q A U :=
  .seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg .vk) (rg .ac2)) (moveR (rg .ac2) (rg .hv) id)

/-- Move the next `B` records (`mwn` holds `B w` symbols) of `ef` onto `xs`. -/
def bandColP : Pr P T Q A U :=
  .seq (rsbMv (rg .mwn) (rg .tC) (rg .ef) (rg .ac2)) (moveR (rg .ac2) (rg .xs) id)

/-- One pending update: pop a record of `vk`, subtract the top product, push onto `nv`. -/
def bandSubP : Pr P T Q A U :=
  .seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg .vk) (rg .ac2))
    (.seq (moveR (rg .ac2) (rg .ac) id) (.seq (rsbSubBody rg) (moveR (rg .ac) (rg .nv) id)))

end Programs

section Step

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

/-- One forward column step of the banded solve. -/
noncomputable def bandFwdStepP : Pr P T Q A U :=
  .seq (bandPopP rg) (.seq (rsbCopyTo rg .hv .dout)
    (.seq (rsbRep (rg .m2n) (rg .tJ) (rsbCopyTo rg .hv .ya)) (.seq (bandColP rg)
    (.seq (cmulStream (rsbCr rg .ya .xs .pr) (rmulOne ι hι hT hQ (rsbCr rg .ya .xs .pr)))
    (.seq (emptyR (rg .ya)) (.seq (emptyR (rg .xs)) (.seq (emptyR (rg .hv))
    (.seq (rsbRep (rg .m2n) (rg .tJ) (bandSubP rg)) (moveR (rg .nv) (rg .vk) id)))))))))

/-- Replace the head of `vk` by its truncated product with the next stored
reciprocal of `tb`. -/
noncomputable def bandRecipP : Pr P T Q A U :=
  .seq (bandPopP rg) (.seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg .tb) (rg .ac2))
    (.seq (moveR (rg .ac2) (rg .xa) id)
    (.seq (cmulStream (rsbCr rg .hv .xa .hc) (rmulOne ι hι hT hQ (rsbCr rg .hv .xa .hc)))
    (.seq (emptyR (rg .hv)) (.seq (emptyR (rg .xa))
    (.seq (moveR (rg .hc) (rg .ac2) id) (moveR (rg .ac2) (rg .vk) id)))))))

/-- One backward column step: reciprocal, then the forward step. -/
noncomputable def bandBwdStepP : Pr P T Q A U :=
  .seq (bandRecipP rg hι hT hQ) (bandFwdStepP rg hι hT hQ)

/-- The forward pass: one column step per symbol of `sn`. -/
noncomputable def bandFwdLoopP : Pr P T Q A U :=
  rsbRep (rg .sn) (rg .tL) (bandFwdStepP rg hι hT hQ)

/-- The backward pass: one backward column step per symbol of `sn`. -/
noncomputable def bandBwdLoopP : Pr P T Q A U :=
  rsbRep (rg .sn) (rg .tL) (bandBwdStepP rg hι hT hQ)

/-- The step bound of one forward column step. -/
def bandFwdStepCost (T w B : ℕ) : ℕ := B * (rmulCost T w + 40 * w + 60) + 30 * w + 60

end Step

lemma sum_zipWith_const {α β : Type*} (c : ℕ) : ∀ (l₁ : List α) (l₂ : List β),
    (List.zipWith (fun _ _ => c) l₁ l₂).sum=min l₁.length l₂.length*c
  | [], _ => by simp
  | _::_, [] => by simp
  | _::l₁, _::l₂ => by
      simp only [List.zipWith_cons_cons, List.sum_cons, sum_zipWith_const c l₁ l₂,
        List.length_cons]
      rw [Nat.min_def, Nat.min_def]; split <;> split <;> first | omega | ring_nf

lemma bandFree_hv : RsbFree .hv .xa .hc := ⟨by decide, by decide, by decide, fun _ => ⟨by simp,
  by simp, by simp⟩⟩

lemma bandFree_ya : RsbFree .ya .xs .pr := ⟨by decide, by decide, by decide, fun _ => ⟨by simp,
  by simp, by simp⟩⟩

/-- Complex records of a real column. -/
def colC (c : List ℤ) : List GaussianInt := c.map fun x => ⟨x, 0⟩

lemma machine_sub_eq (P B : ℕ) (y : GaussianInt) (c : List ℤ) (rs : List GaussianInt) :
    List.zipWith (· - ·) rs (List.zipWith (fun a b => tdivN P (a * b)) (List.replicate B y) (colC c))=
      List.zipWith (fun r x => r - tdivN P (⟨x, 0⟩ * y)) rs (c.take B) := by
  induction c generalizing rs B with
  | nil => simp [colC]
  | cons x c ih =>
    cases B with
    | zero => simp [colC]
    | succ B =>
      cases rs with
      | nil => simp [colC]
      | cons r rs =>
        simp only [colC, List.map_cons, List.replicate_succ, List.zipWith_cons_cons,
          List.take_succ_cons]
        rw [mul_comm y]
        congr 1
        exact ih B rs

lemma subColC_split (P : ℕ) (y : GaussianInt) : ∀ (c : List ℤ) (rest : List GaussianInt),
    c.length≤rest.length → Mult.BandList.subColC P c y rest=
      List.zipWith (fun r x => r - tdivN P (⟨x, 0⟩ * y)) (rest.take c.length) c ++
        rest.drop c.length
  | [], rest, _ => by cases rest <;> simp [Mult.BandList.subColC]
  | x::c, r::rest, h => by
      simp only [Mult.BandList.subColC, List.length_cons, List.take_succ_cons, List.drop_succ_cons,
        List.zipWith_cons_cons, List.cons_append]
      rw [subColC_split P y c rest (by simp at h; omega)]
  | _::_, [], h => by simp at h

section Contracts

variable {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_pop_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (y : GaussianInt) (VK : List (Fin (A + 4)))
    (hvk : σ .vk = csyms A w y ++ VK) (hhv : σ .hv = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (hwn : (σ (.cm .wn)).length = w) :
    RsbRuns body rg ι (bandPopP rg) σ
      (Function.update (Function.update σ .vk VK) .hv (csyms A w y)) (6 * w + 6) := by
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .vk)
    (y := .ac2) (by decide) σ htC (by rw [hwn, hvk]; simp)
  rw [hwn, hvk, take_csyms_append, drop_csyms_append, hac2, List.append_nil] at h₁
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .hv) (by decide)
    (Function.update (Function.update σ .vk VK) .ac2 (csyms A w y).reverse)
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono ?_
  · funext r; cases r <;> simp [hhv, hac2]
  · simp; omega

theorem band_col_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w B : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (col rest : List GaussianInt) (hcol : col.length = B)
    (hef : σ .ef = cstream A w (col ++ rest)) (hxs : σ .xs = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (hmwn : (σ .mwn).length = B * w) :
    RsbRuns body rg ι (bandColP rg) σ
      (Function.update (Function.update σ .ef (cstream A w rest)) .xs (cstream A w col))
      (6 * (B * w) + 6) := by
  have hlen : (σ .mwn).length ≤ (σ .ef).length := by
    rw [hmwn, hef, cstream_append, List.length_append]
    simp [cstream, hcol]
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .ef)
    (y := .ac2) (by decide) σ htC hlen
  have htake : (σ .ef).take (σ .mwn).length = cstream A w col := by
    rw [hmwn, hef, cstream_append, ← hcol, take_cstream col col.length le_rfl, List.take_length]
  have hdrop : (σ .ef).drop (σ .mwn).length = cstream A w rest := by
    rw [hmwn, hef, cstream_append, ← hcol]
    rw [drop_cstream (A := A) (w := w) col col.length (cstream A w rest)]
    simp
  rw [htake, hdrop, hac2, List.append_nil] at h₁
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .xs) (by decide)
    (Function.update (Function.update σ .ef (cstream A w rest)) .ac2 (cstream A w col).reverse)
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono ?_
  · funext r; cases r <;> simp [hxs, hac2]
  · simp [hmwn, cstream, hcol]; omega

/-- `B` copies of the record on `hv` onto `ya`. -/
theorem band_rep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w B : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (y : GaussianInt) (hhv : σ .hv = csyms A w y)
    (hya : σ .ya = []) (hb1 : σ .b1 = []) (htC : σ .tC = []) (htJ : σ .tJ = [])
    (hm2n : (σ .m2n).length = B) :
    RsbRuns body rg ι (rsbRep (rg .m2n) (rg .tJ) (rsbCopyTo rg .hv .ya)) σ
      (Function.update σ .ya (cstream A w (List.replicate B y))) (B * (6 * w + 12) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)),
      Ψ = fun j => Function.update σ .ya (cstream A w (List.replicate j y)) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .m2n).length, ∀ X Y, RsbRuns body rg ι (rsbCopyTo rg .hv .ya)
      (rsbUpd2 (Ψ j) .m2n X .tJ Y) (rsbUpd2 (Ψ (j + 1)) .m2n X .tJ Y) (6 * w + 6) := by
    intro j _ X Y
    have h := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .hv) (b := .ya)
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (rsbUpd2 (Ψ j) .m2n X .tJ Y)
      (by simp [hΨ, hb1]) (by simp [hΨ, htC])
    refine (h.congr ?_).mono ?_
    · funext r; cases r <;> simp [hΨ, hhv, List.replicate_succ]
    · simp [hΨ, hhv]
  have h := rsb_rep_runs hrg hdisj (ra := .m2n) (rt := .tJ) (by decide) (rsbCopyTo rg .hv .ya)
    (σ .m2n) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext r; cases r <;> simp [hΨ, hya, htJ]
  · rw [hm2n]; funext r; cases r <;> simp [hΨ, htJ]
  · rw [hm2n]

/-- One pending update. -/
theorem band_sub_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ A)
    {w : ℕ} (σ : RsbR → List (Fin (A + 4))) (x z : GaussianInt) (VK PR NV : List (Fin (A + 4)))
    (hvk : σ .vk = csyms A w x ++ VK) (hpr : σ .pr = csyms A w z ++ PR) (hnv : σ .nv = NV)
    (hac : σ .ac = []) (hac2 : σ .ac2 = []) (htC : σ .tC = []) (htA : σ .tA = [])
    (hwn : (σ (.cm .wn)).length = w) :
    RsbRuns body rg ι (bandSubP rg) σ
      (Function.update (Function.update (Function.update σ .vk VK) .pr PR) .nv
        ((csyms A w (x - z)).reverse ++ NV)) (15 * w + 16) := by
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .vk)
    (y := .ac2) (by decide) σ htC (by rw [hwn, hvk]; simp)
  rw [hwn, hvk, take_csyms_append, drop_csyms_append, hac2, List.append_nil] at h₁
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .ac) (by decide)
    (Function.update (Function.update σ .vk VK) .ac2 (csyms A w x).reverse)
  set σ₂ := Function.update (Function.update (Function.update (Function.update σ .vk VK) .ac2
    (csyms A w x).reverse) .ac2 []) .ac
    ((Function.update (Function.update σ .vk VK) .ac2 (csyms A w x).reverse .ac2).reverse ++
      Function.update (Function.update σ .vk VK) .ac2 (csyms A w x).reverse .ac) with hσ₂
  have h₃ := rsb_subBody_runs (body := body) (ι := ι) hrg hdisj hA (w := w) σ₂ x z PR
    (by simp [hσ₂, hac]) (by simp [hσ₂, hpr]) (by simp [hσ₂]) (by simp [hσ₂, htA])
    (by simp [hσ₂, hwn])
  have h₄ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac) (b := .nv) (by decide)
    (Function.update (Function.update σ₂ .ac (csyms A w (x - z))) .pr PR)
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃ h₄))).congr ?_).mono ?_
  · funext r; cases r <;> simp [hσ₂, hnv, hac, hac2]
  · simp [hσ₂, hac]; omega

/-- `B` pending updates against `B` products, rebuilding the records on `nv`. -/
theorem band_subLoop_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ A)
    {w B : ℕ} (σ : RsbR → List (Fin (A + 4))) (rs zs : List GaussianInt)
    (hrs : rs.length = B) (hzs : zs.length = B) (VK PR : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w rs ++ VK) (hpr : σ .pr = cstream A w zs ++ PR) (hnv : σ .nv = [])
    (hac : σ .ac = []) (hac2 : σ .ac2 = []) (htC : σ .tC = []) (htA : σ .tA = [])
    (htJ : σ .tJ = []) (hwn : (σ (.cm .wn)).length = w) (hm2n : (σ .m2n).length = B) :
    RsbRuns body rg ι (rsbRep (rg .m2n) (rg .tJ) (bandSubP rg)) σ
      (Function.update (Function.update (Function.update σ .vk VK) .pr PR) .nv
        (cstream A w (List.zipWith (· - ·) rs zs)).reverse) (B * (15 * w + 22) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update σ .vk (cstream A w (rs.drop j) ++ VK))
        .pr (cstream A w (zs.drop j) ++ PR)) .nv
        (cstream A w ((List.zipWith (· - ·) rs zs).take j)).reverse := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .m2n).length, ∀ X Y, RsbRuns body rg ι (bandSubP rg)
      (rsbUpd2 (Ψ j) .m2n X .tJ Y) (rsbUpd2 (Ψ (j + 1)) .m2n X .tJ Y) (15 * w + 16) := by
    intro j hj X Y
    rw [hm2n] at hj
    have hjr : j < rs.length := by omega
    have hjz : j < zs.length := by omega
    have h := band_sub_runs (body := body) (ι := ι) hrg hdisj hA (w := w)
      (rsbUpd2 (Ψ j) .m2n X .tJ Y) rs[j] zs[j] (cstream A w (rs.drop (j + 1)) ++ VK)
      (cstream A w (zs.drop (j + 1)) ++ PR)
      (cstream A w ((List.zipWith (· - ·) rs zs).take j)).reverse
      (by simp [hΨ, cstream_drop_eq_cons rs j hjr])
      (by simp [hΨ, cstream_drop_eq_cons zs j hjz]) (by simp [hΨ]) (by simp [hΨ, hac])
      (by simp [hΨ, hac2]) (by simp [hΨ, htC]) (by simp [hΨ, htA]) (by simp [hΨ, hwn])
    refine h.congr ?_
    have htake : (List.zipWith (· - ·) rs zs).take (j + 1) =
        (List.zipWith (· - ·) rs zs).take j ++ [rs[j] - zs[j]] := by
      rw [List.take_add_one, List.getElem?_zipWith]
      simp [List.getElem?_eq_getElem hjr, List.getElem?_eq_getElem hjz]
    funext r; cases r <;> simp [hΨ, htake]
  have h := rsb_rep_runs hrg hdisj (ra := .m2n) (rt := .tJ) (by decide) (bandSubP rg)
    (σ .m2n) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext r; cases r <;> simp [hΨ, hvk, hpr, hnv, htJ]
  · rw [hm2n]
    have hz : (List.zipWith (· - ·) rs zs).take B = List.zipWith (· - ·) rs zs := by
      rw [List.take_of_length_le]; simp [hrs, hzs]
    have hdr : rs.drop B = [] := List.drop_of_length_le (le_of_eq hrs)
    have hdz : zs.drop B = [] := List.drop_of_length_le (le_of_eq hzs)
    funext r; cases r <;> simp [hΨ, htJ, hz, hdr, hdz]
  · rw [hm2n]

/-- One forward column step: the head `y` is recorded on `dout`, and the next `B`
pending records lose the truncated products of `y` with the column. -/
theorem band_fwdStep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w p) (hw : 1 ≤ w)
    (hp : p ≤ w) (y : GaussianInt) (rs more col cols : List GaussianInt) (hrs : rs.length = B)
    (hcol : col.length = B) (hfy : Fits w y) (hfc : ∀ a ∈ col, Fits w a ∧ a.im = 0)
    (D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (y :: (rs ++ more))) (hef : σ .ef = cstream A w (col ++ cols))
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hm2n : (σ .m2n).length = B) (hmwn : (σ .mwn).length = B * w) :
    RsbRuns body rg ι (bandFwdStepP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update σ .vk
        (cstream A w (List.zipWith (· - ·) rs
          (List.zipWith (fun a b => tdivN p (a * b)) (List.replicate B y) col) ++ more)))
        .ef (cstream A w cols)) .dout (csyms A w y ++ D))
      (bandFwdStepCost T w B) := by
  have hwn := hready.wn
  set prods := List.zipWith (fun a b => tdivN p (a * b)) (List.replicate B y) col with hprods
  have hprl : prods.length = B := by simp [hprods, hcol]
  -- pop
  have h₁ := band_pop_runs (body := body) (ι := ι) hrg hdisj σ y (cstream A w (rs ++ more))
    (by rw [hvk, cstream_cons]) hhv hac2 htC hwn
  set σ₁ := Function.update (Function.update σ .vk (cstream A w (rs ++ more))) .hv (csyms A w y)
  -- record the head
  have h₂ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .hv) (b := .dout)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₁ (by simp [σ₁, hb1])
    (by simp [σ₁, htC])
  set σ₂ := Function.update σ₁ .dout (σ₁ .hv ++ σ₁ .dout)
  -- replicate
  have h₃ := band_rep_runs (body := body) (ι := ι) hrg hdisj (w := w) (B := B) σ₂ y
    (by simp [σ₂, σ₁]) (by simp [σ₂, σ₁, hya]) (by simp [σ₂, σ₁, hb1]) (by simp [σ₂, σ₁, htC])
    (by simp [σ₂, σ₁, htJ]) (by simp [σ₂, σ₁, hm2n])
  set σ₃ := Function.update σ₂ .ya (cstream A w (List.replicate B y))
  -- the column
  have h₄ := band_col_runs (body := body) (ι := ι) hrg hdisj (w := w) (B := B) σ₃ col cols hcol
    (by simp [σ₃, σ₂, σ₁, hef]) (by simp [σ₃, σ₂, σ₁, hxs]) (by simp [σ₃, σ₂, σ₁, hac2])
    (by simp [σ₃, σ₂, σ₁, htC]) (by simp [σ₃, σ₂, σ₁, hmwn])
  set σ₄ := Function.update (Function.update σ₃ .ef (cstream A w cols)) .xs (cstream A w col)
  -- the products
  have hready₄ : RsbReady σ₄ w p := by
    simp only [σ₄, σ₃, σ₂, σ₁]
    exact (((((hready.update .vk (fun c => by simp) _).update .hv (fun c => by simp) _).update
      .dout (fun c => by simp) _).update .ya (fun c => by simp) _).update .ef (fun c => by simp)
      _).update .xs (fun c => by simp) _
  have h₅ := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA bandFree_ya (ρ := σ₄)
    hready₄ hw hp (List.replicate B y) col (by simp [hcol])
    (by intro a ha; rw [(List.mem_replicate.mp ha).2]; exact hfy) hfc
    (by simp [σ₄, σ₃]) (by simp [σ₄])
  set σ₅ := Function.update σ₄ .pr (cstream A w prods ++ σ₄ .pr)
  have h₆ := rsb_emptyR_runs (body := body) (ι := ι) hrg .ya σ₅
  have h₇ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xs (Function.update σ₅ .ya [])
  have h₈ := rsb_emptyR_runs (body := body) (ι := ι) hrg .hv
    (Function.update (Function.update σ₅ .ya []) .xs [])
  set σ₈ := Function.update (Function.update (Function.update σ₅ .ya []) .xs []) .hv []
  -- the updates
  have h₉ := band_subLoop_runs (body := body) (ι := ι) hrg hdisj hA (w := w) (B := B) σ₈ rs prods
    hrs hprl (cstream A w more) []
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, cstream_append])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hpr]) (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hnv])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hac]) (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hac2])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, htJ]) (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hwn])
    (by simp [σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hm2n])
  set σ₉ := Function.update (Function.update (Function.update σ₈ .vk (cstream A w more)) .pr [])
    .nv (cstream A w (List.zipWith (· - ·) rs prods)).reverse
  have h₁₀ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .nv) (b := .vk) (by decide) σ₉
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj h₆ (RsbRuns.seq hdisj h₇
    (RsbRuns.seq hdisj h₈ (RsbRuns.seq hdisj h₉ h₁₀))))))))).congr ?_).mono ?_
  · funext r; cases r <;> simp [σ₉, σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, hhv, hya, hxs, hpr, hnv, hdout,
      cstream_append]
  · simp [σ₉, σ₈, σ₅, σ₄, σ₃, σ₂, σ₁, bandFwdStepCost, hpr, hdout, 
      hcol, hprl, cstream, sum_zipWith_const, hrs]
    nlinarith

/-- The forward pass over `s` columns. -/
theorem band_fwdLoop_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (cs : List (List ℤ)) (hcs : cs.length = s) (hcl : ∀ c ∈ cs, c.length = B)
    (pend : List GaussianInt) (hpl : pend.length = s + B)
    (hfit : ∀ j < s, Fits w ((Mult.BandList.bandPend P cs pend j).headD 0))
    (hfc : ∀ c ∈ cs, ∀ x ∈ c, Fits w (⟨x, 0⟩ : GaussianInt)) (D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w pend) (hef : σ .ef = cstream A w (cs.map colC).flatten)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (htL : σ .tL = []) (hsn : (σ .sn).length = s)
    (hm2n : (σ .m2n).length = B) (hmwn : (σ .mwn).length = B * w) :
    RsbRuns body rg ι (bandFwdLoopP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update σ .vk
        (cstream A w (Mult.BandList.bandPend P cs pend s))) .ef []) .dout
        (cstream A w (Mult.BandList.bandOut P cs pend s) ++ D))
      (s * (bandFwdStepCost T w B + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update σ .vk
        (cstream A w (Mult.BandList.bandPend P cs pend j))) .ef
        (cstream A w ((cs.map colC).drop j).flatten)) .dout
        (cstream A w (Mult.BandList.bandOut P cs pend j) ++ D) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y, RsbRuns body rg ι (bandFwdStepP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .sn X .tL Y) (rsbUpd2 (Ψ (j + 1)) .sn X .tL Y) (bandFwdStepCost T w B) := by
    intro j hj X Y
    rw [hsn] at hj
    have hlenj := Mult.BandList.length_bandPend P cs pend j (by omega)
    obtain ⟨y, rest, hyr⟩ : ∃ y rest, Mult.BandList.bandPend P cs pend j = y :: rest := by
      cases h : Mult.BandList.bandPend P cs pend j with
      | nil => rw [h] at hlenj; simp at hlenj; omega
      | cons y rest => exact ⟨y, rest, rfl⟩
    have hrl : rest.length = s + B - j - 1 := by rw [hyr] at hlenj; simp at hlenj; omega
    have hjc : j < cs.length := by omega
    have hcj := hcl (cs[j]'hjc) (List.getElem_mem hjc)
    have hready' : RsbReady (rsbUpd2 (Ψ j) .sn X .tL Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((((hready.update .vk (fun c => by simp) _).update .ef (fun c => by simp) _).update
        .dout (fun c => by simp) _).update .sn (fun c => by simp) _).update .tL
        (fun c => by simp) _
    have hstep := band_fwdStep_runs (body := body) (ι := ι) (w := w) (p := P) (B := B) hrg hdisj
      hι hT hQ hA
      (rsbUpd2 (Ψ j) .sn X .tL Y) hready' hw hp y (rest.take B) (rest.drop B) (colC (cs[j]'hjc))
      ((cs.map colC).drop (j + 1)).flatten (by simp only [List.length_take]; omega) (by simp [colC, hcj])
      (by have := hfit j hj; rwa [hyr] at this)
      (by intro a ha; simp only [colC, List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
          exact ⟨hfc _ (List.getElem_mem hjc) x hx, rfl⟩)
      (cstream A w (Mult.BandList.bandOut P cs pend j) ++ D)
      (by simp [hΨ, hyr]) (by
        have hjm : j < (cs.map colC).length := by simpa using hjc
        simp [hΨ]; rw [List.drop_eq_getElem_cons hjm]; simp)
      (by simp [hΨ]) (by simp [hΨ, hhv]) (by simp [hΨ, hya]) (by simp [hΨ, hxs])
      (by simp [hΨ, hpr]) (by simp [hΨ, hnv]) (by simp [hΨ, hac]) (by simp [hΨ, hac2])
      (by simp [hΨ, htC]) (by simp [hΨ, htA]) (by simp [hΨ, htJ]) (by simp [hΨ, hb1])
      (by simp [hΨ, hm2n]) (by simp [hΨ, hmwn])
    refine hstep.congr ?_
    have hnext : Mult.BandList.bandPend P cs pend (j + 1) =
        List.zipWith (· - ·) (rest.take B)
          (List.zipWith (fun a b => tdivN P (a * b)) (List.replicate B y) (colC (cs[j]'hjc))) ++
          rest.drop B := by
      have e1 : (cs[j]'hjc).take B = cs[j]'hjc := List.take_of_length_le (le_of_eq hcj)
      rw [machine_sub_eq, e1]
      simp only [Mult.BandList.bandPend, hyr, List.getD_eq_getElem _ _ hjc]
      rw [subColC_split P y (cs[j]'hjc) rest (by omega), hcj]
    have hout : Mult.BandList.bandOut P cs pend (j + 1) = y :: Mult.BandList.bandOut P cs pend j := by
      simp [Mult.BandList.bandOut, hyr]
    funext r; cases r <;> simp [hΨ, hnext, hout]
  have h := rsb_rep_runs hrg hdisj (ra := .sn) (rt := .tL) (by decide) (bandFwdStepP rg hι hT hQ)
    (σ .sn) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext r; cases r <;> simp [hΨ, hvk, hef, hdout, htL, Mult.BandList.bandPend,
      Mult.BandList.bandOut]
  · rw [hsn]
    have hd : (cs.map colC).drop s = [] := List.drop_of_length_le (by simp [hcs])
    funext r; cases r <;> simp [hΨ, htL, hd]
  · rw [hsn]

/-- The reciprocal preamble of a backward step. -/
theorem band_recip_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (q : GaussianInt) (r : ℤ) (VK TB : List (Fin (A + 4))) (hfq : Fits w q)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt))
    (hvk : σ .vk = csyms A w q ++ VK) (htb : σ .tb = csyms A w ⟨r, 0⟩ ++ TB)
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) :
    RsbRuns body rg ι (bandRecipP rg hι hT hQ) σ
      (Function.update (Function.update σ .vk (csyms A w (tdivN P (q * ⟨r, 0⟩)) ++ VK)) .tb TB)
      (rmulCost T w + 30 * w + 40) := by
  have hwn := hready.wn
  have h₁ := band_pop_runs (body := body) (ι := ι) hrg hdisj σ q VK hvk hhv hac2 htC hwn
  set σ₁ := Function.update (Function.update σ .vk VK) .hv (csyms A w q)
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .tb)
    (y := .ac2) (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hwn, htb])
  rw [show (σ₁ (.cm .wn)).length = w by simp [σ₁, hwn]] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.tb ≠ RsbR.hv),
    Function.update_of_ne (by decide : RsbR.tb ≠ RsbR.vk),
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.hv),
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.vk), htb, take_csyms_append,
    drop_csyms_append, hac2, List.append_nil] at h₂
  set σ₂ := Function.update (Function.update σ₁ .tb TB) .ac2 (csyms A w ⟨r, 0⟩).reverse
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .xa) (by decide) σ₂
  set σ₃ := Function.update (Function.update σ₂ .ac2 []) .xa ((σ₂ .ac2).reverse ++ σ₂ .xa)
  have hready₃ : RsbReady σ₃ w P := by
    simp only [σ₃, σ₂, σ₁]
    exact (((((hready.update .vk (fun c => by simp) _).update .hv (fun c => by simp) _).update
      .tb (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2 (fun c => by simp)
      _).update .xa (fun c => by simp) _
  have h₄ := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA bandFree_hv (ρ := σ₃)
    hready₃ hw hp [q] [⟨r, 0⟩] rfl (by simpa using hfq) (by simpa using hfr)
    (by simp [σ₃, σ₂, σ₁]) (by simp [σ₃, σ₂, σ₁, hxa])
  set σ₄ := Function.update σ₃ .hc
    (cstream A w (List.zipWith (fun a b => tdivN P (a * b)) [q] [⟨r, 0⟩]) ++ σ₃ .hc)
  have h₅ := rsb_emptyR_runs (body := body) (ι := ι) hrg .hv σ₄
  have h₆ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xa (Function.update σ₄ .hv [])
  set σ₆ := Function.update (Function.update σ₄ .hv []) .xa []
  have h₇ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .hc) (b := .ac2) (by decide) σ₆
  set σ₇ := Function.update (Function.update σ₆ .hc []) .ac2 ((σ₆ .hc).reverse ++ σ₆ .ac2)
  have h₈ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .vk) (by decide) σ₇
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj h₆
    (RsbRuns.seq hdisj h₇ h₈))))))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₇, σ₆, σ₄, σ₃, σ₂, σ₁, hhv, hxa, hhc, hac2]
  · simp [σ₇, σ₆, σ₄, σ₃, σ₂, σ₁, hxa, hhc, cstream]
    omega

/-- One backward column step. -/
theorem band_bwdStep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (q : GaussianInt) (r : ℤ) (rs more col cols : List GaussianInt)
    (hrs : rs.length = B) (hcol : col.length = B) (hfq : Fits w q)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt)) (hfx : Fits w (tdivN P (q * ⟨r, 0⟩)))
    (hfc : ∀ a ∈ col, Fits w a ∧ a.im = 0) (D TB : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (q :: (rs ++ more))) (htb : σ .tb = csyms A w ⟨r, 0⟩ ++ TB)
    (hef : σ .ef = cstream A w (col ++ cols))
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hxa : σ .xa = []) (hhc : σ .hc = [])
    (hm2n : (σ .m2n).length = B) (hmwn : (σ .mwn).length = B * w) :
    RsbRuns body rg ι (bandBwdStepP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w (List.zipWith (· - ·) rs
          (List.zipWith (fun a b => tdivN P (a * b)) (List.replicate B (tdivN P (q * ⟨r, 0⟩)))
            col) ++ more))) .tb TB) .ef (cstream A w cols)) .dout
        (csyms A w (tdivN P (q * ⟨r, 0⟩)) ++ D))
      (rmulCost T w + 30 * w + 40 + bandFwdStepCost T w B) := by
  obtain ⟨x, hx⟩ : ∃ x, x = tdivN P (q * ⟨r, 0⟩) := ⟨_, rfl⟩
  rw [← hx] at hfx ⊢
  have h₁ := band_recip_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA σ hready hw hp q r
    (cstream A w (rs ++ more)) TB hfq hfr (by rw [hvk, cstream_cons]) htb hhv hxa hhc hac2 htC
  rw [← hx] at h₁
  set σ₁ := Function.update (Function.update σ .vk
    (csyms A w x ++ cstream A w (rs ++ more))) .tb TB
  have hready₁ : RsbReady σ₁ w P :=
    (hready.update .vk (fun c => by simp) _).update .tb (fun c => by simp) _
  have h₂ := band_fwdStep_runs (body := body) (ι := ι) (w := w) (p := P) (B := B) hrg hdisj hι hT
    hQ hA σ₁ hready₁ hw hp x rs more col cols hrs hcol hfx hfc D
    (by simp [σ₁, cstream_cons]) (by simp [σ₁, hef]) (by simp [σ₁, hdout]) (by simp [σ₁, hhv])
    (by simp [σ₁, hya]) (by simp [σ₁, hxs]) (by simp [σ₁, hpr]) (by simp [σ₁, hnv])
    (by simp [σ₁, hac]) (by simp [σ₁, hac2]) (by simp [σ₁, htC]) (by simp [σ₁, htA])
    (by simp [σ₁, htJ]) (by simp [σ₁, hb1]) (by simp [σ₁, hm2n]) (by simp [σ₁, hmwn])
  refine (RsbRuns.seq hdisj h₁ h₂).congr ?_
  funext z; cases z <;> simp [σ₁]

/-- The backward pass over `s` columns, with stored reciprocals on `tb`. -/
theorem band_bwdLoop_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (cs : List (List ℤ)) (hcs : cs.length = s) (hcl : ∀ c ∈ cs, c.length = B)
    (rcs : List ℤ) (hrcs : rcs.length = s) (hfr : ∀ x ∈ rcs, Fits w (⟨x, 0⟩ : GaussianInt))
    (pend : List GaussianInt) (hpl : pend.length = s + B)
    (hfit : ∀ j < s, Fits w ((Mult.BandList.bandPendB P cs rcs pend j).headD 0))
    (hfx : ∀ j < s, Fits w (tdivN P ((Mult.BandList.bandPendB P cs rcs pend j).headD 0 *
      ⟨rcs.getD j 0, 0⟩)))
    (hfc : ∀ c ∈ cs, ∀ x ∈ c, Fits w (⟨x, 0⟩ : GaussianInt)) (D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w pend) (hef : σ .ef = cstream A w (cs.map colC).flatten)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (htL : σ .tL = []) (hsn : (σ .sn).length = s) (hxa : σ .xa = []) (hhc : σ .hc = [])
    (htb : σ .tb = cstream A w (rcs.map fun x => (⟨x, 0⟩ : GaussianInt)))
    (hm2n : (σ .m2n).length = B) (hmwn : (σ .mwn).length = B * w) :
    RsbRuns body rg ι (bandBwdLoopP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w (Mult.BandList.bandPendB P cs rcs pend s))) .tb []) .ef []) .dout
        (cstream A w (Mult.BandList.bandOutB P cs rcs pend s) ++ D))
      (s * (rmulCost T w + 30 * w + 40 + bandFwdStepCost T w B + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w (Mult.BandList.bandPendB P cs rcs pend j))) .tb
        (cstream A w ((rcs.map fun x => (⟨x, 0⟩ : GaussianInt)).drop j))) .ef
        (cstream A w ((cs.map colC).drop j).flatten)) .dout
        (cstream A w (Mult.BandList.bandOutB P cs rcs pend j) ++ D) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y, RsbRuns body rg ι (bandBwdStepP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .sn X .tL Y) (rsbUpd2 (Ψ (j + 1)) .sn X .tL Y)
      (rmulCost T w + 30 * w + 40 + bandFwdStepCost T w B) := by
    intro j hj X Y
    rw [hsn] at hj
    have hlenj := Mult.BandList.length_bandPendB P cs rcs pend j (by omega)
    obtain ⟨y, rest, hyr⟩ : ∃ y rest, Mult.BandList.bandPendB P cs rcs pend j = y :: rest := by
      cases h : Mult.BandList.bandPendB P cs rcs pend j with
      | nil => rw [h] at hlenj; simp at hlenj; omega
      | cons y rest => exact ⟨y, rest, rfl⟩
    have hrl : rest.length = s + B - j - 1 := by rw [hyr] at hlenj; simp at hlenj; omega
    have hjc : j < cs.length := by omega
    have hcj := hcl (cs[j]'hjc) (List.getElem_mem hjc)
    have hready' : RsbReady (rsbUpd2 (Ψ j) .sn X .tL Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact (((((hready.update .vk (fun c => by simp) _).update .tb (fun c => by simp) _).update
        .ef (fun c => by simp) _).update
        .dout (fun c => by simp) _).update .sn (fun c => by simp) _).update .tL
        (fun c => by simp) _
    have hjr : j < rcs.length := by omega
    have hstep := band_bwdStep_runs (body := body) (ι := ι) (w := w) (B := B) hrg hdisj
      hι hT hQ hA
      (rsbUpd2 (Ψ j) .sn X .tL Y) hready' hw hp y (rcs[j]'hjr) (rest.take B) (rest.drop B)
      (colC (cs[j]'hjc))
      ((cs.map colC).drop (j + 1)).flatten (by simp only [List.length_take]; omega) (by simp [colC, hcj])
      (by have := hfit j hj; rwa [hyr] at this) (hfr _ (List.getElem_mem hjr))
      (by have := hfx j hj; rwa [hyr, List.getD_eq_getElem _ _ hjr] at this)
      (by intro a ha; simp only [colC, List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
          exact ⟨hfc _ (List.getElem_mem hjc) x hx, rfl⟩)
      (cstream A w (Mult.BandList.bandOutB P cs rcs pend j) ++ D)
      (cstream A w ((rcs.map fun x => (⟨x, 0⟩ : GaussianInt)).drop (j + 1)))
      (by simp [hΨ, hyr]) (by
        have hjm : j < (rcs.map fun x => (⟨x, 0⟩ : GaussianInt)).length := by simpa using hjr
        simp [hΨ]; rw [List.drop_eq_getElem_cons hjm]; simp) (by
        have hjm : j < (cs.map colC).length := by simpa using hjc
        simp [hΨ]; rw [List.drop_eq_getElem_cons hjm]; simp)
      (by simp [hΨ]) (by simp [hΨ, hhv]) (by simp [hΨ, hya]) (by simp [hΨ, hxs])
      (by simp [hΨ, hpr]) (by simp [hΨ, hnv]) (by simp [hΨ, hac]) (by simp [hΨ, hac2])
      (by simp [hΨ, htC]) (by simp [hΨ, htA]) (by simp [hΨ, htJ]) (by simp [hΨ, hb1])
      (by simp [hΨ, hxa]) (by simp [hΨ, hhc]) (by simp [hΨ, hm2n]) (by simp [hΨ, hmwn])
    refine hstep.congr ?_
    have hnext : Mult.BandList.bandPendB P cs rcs pend (j + 1) =
        List.zipWith (· - ·) (rest.take B)
          (List.zipWith (fun a b => tdivN P (a * b))
            (List.replicate B (tdivN P (y * ⟨rcs[j]'hjr, 0⟩))) (colC (cs[j]'hjc))) ++
          rest.drop B := by
      have e1 : (cs[j]'hjc).take B = cs[j]'hjc := List.take_of_length_le (le_of_eq hcj)
      rw [machine_sub_eq, e1]
      simp only [Mult.BandList.bandPendB, hyr, List.getD_eq_getElem _ _ hjc,
        List.getD_eq_getElem _ _ hjr]
      rw [subColC_split P _ (cs[j]'hjc) rest (by omega), hcj]
    have hout : Mult.BandList.bandOutB P cs rcs pend (j + 1) =
        tdivN P (y * ⟨rcs[j]'hjr, 0⟩) :: Mult.BandList.bandOutB P cs rcs pend j := by
      simp [Mult.BandList.bandOutB, hyr, List.getElem?_eq_getElem hjr]
    funext r; cases r <;> simp [hΨ, hnext, hout]
  have h := rsb_rep_runs hrg hdisj (ra := .sn) (rt := .tL) (by decide) (bandBwdStepP rg hι hT hQ)
    (σ .sn) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext r; cases r <;> simp [hΨ, hvk, hef, hdout, htL, htb, Mult.BandList.bandPendB,
      Mult.BandList.bandOutB]
  · rw [hsn]
    have hd : (cs.map colC).drop s = [] := List.drop_of_length_le (by simp [hcs])
    have hdr : (rcs.map fun x => (⟨x, 0⟩ : GaussianInt)).drop s = [] :=
      List.drop_of_length_le (by simp [hrcs])
    funext r; cases r <;> simp [hΨ, htL, hd, hdr]
  · rw [hsn]


end Contracts

end IntegerMultBounds.MathlibTM2.Fast
