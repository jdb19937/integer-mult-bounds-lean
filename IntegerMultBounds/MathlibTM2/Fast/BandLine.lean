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

set_option linter.unusedSimpArgs false

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
  · simp [hwn]; omega

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
  · simp [hσ₂, hwn, hac]; omega

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
    funext r; cases r <;> simp [hΨ, htake, reverse_cstream_snoc]
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

end Contracts

end IntegerMultBounds.MathlibTM2.Fast
