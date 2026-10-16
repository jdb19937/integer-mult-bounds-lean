module

public import IntegerMultBounds.MathlibTM2.Fast.BandLine
public import IntegerMultBounds.MathlibTM2.Mult.BandFactor

/-!
# The banded factorization: Newton reciprocals of the pivots

The window factorization of `Mult.BandFactor` needs, for each pivot `c`, the
Newton reciprocal `newtonZ P c K`. One Newton step keeps `c` on `hv` and the
current reciprocal `r` on `xa`; it forms `t = c r` and `q = r t` by truncated
record products and replaces `r` by `r - (q - r) = 2r - q` with two record
subtractions, so no constant record is needed.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U : Type} {P : Type}

section Programs

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

/-- One Newton step on the reciprocal `xa` of the pivot `hv`. -/
noncomputable def bandNewtonStepP : Pr P T Q A U :=
  .seq (cmulStream (rsbCr rg .hv .xa .hc) (rmulOne ι hι hT hQ (rsbCr rg .hv .xa .hc)))
  (.seq (rsbCopyTo rg .xa .ya)
  (.seq (moveR (rg .hc) (rg .ac2) id)
  (.seq (moveR (rg .ac2) (rg .xs) id)
  (.seq (cmulStream (rsbCr rg .ya .xs .pr) (rmulOne ι hι hT hQ (rsbCr rg .ya .xs .pr)))
  (.seq (emptyR (rg .ya)) (.seq (emptyR (rg .xs))
  (.seq (rsbCopyTo rg .xa .ac)
  (.seq (rsbSubWord (rg .pr) (rg .ac) (rg .ac2) (rg (.cm .wn)) (rg .tA))
  (.seq (moveR (rg .ac2) (rg .nv) id)
  (.seq (rsbSubWord (rg .xa) (rg .nv) (rg .ac2) (rg (.cm .wn)) (rg .tA))
  (moveR (rg .ac2) (rg .xa) id)))))))))))

/-- The Newton reciprocal of the pivot `hv` onto `xa`: start from the constant
record on `bx`, then one step per symbol of `kn`. -/
noncomputable def bandNewtonP : Pr P T Q A U :=
  .seq (rsbCopyTo rg .bx .xa) (rsbRep (rg .kn) (rg .tK) (bandNewtonStepP rg hι hT hQ))

end Programs

/-- A Newton step on real records. -/
def newtonStepZ (P : ℕ) (c r : ℤ) : ℤ := 2*r-(r*(c*r).tdiv (2^P)).tdiv (2^P)

lemma tdivN_real (P : ℕ) (a b : ℤ) :
    tdivN P ((⟨a, 0⟩ : GaussianInt)*⟨b, 0⟩)=⟨(a*b).tdiv (2^P), 0⟩ := by
  ext <;> simp [tdivN]

lemma newtonZ_succ (P : ℕ) (c : ℤ) (n : ℕ) :
    Mult.BandFactor.newtonZ P c (n+1)=newtonStepZ P c (Mult.BandFactor.newtonZ P c n) := rfl

section Contracts

variable {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

lemma bandFree_hv' : RsbFree .hv .xa .hc := bandFree_hv

/-- The cost of one Newton step. -/
def bandNewtonStepCost (T w : ℕ) : ℕ := 2 * rmulCost T w + 80 * w + 120

/-- One Newton step: `xa` goes from `r` to `2r - r(cr)`, truncated, everything else kept. -/
theorem band_newtonStep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (c r : ℤ)
    (hfc : Fits w (⟨c, 0⟩ : GaussianInt)) (hfr : Fits w (⟨r, 0⟩ : GaussianInt))
    (hft : Fits w (⟨(c*r).tdiv (2^P), 0⟩ : GaussianInt))
    (hhv : σ .hv = csyms A w ⟨c, 0⟩) (hxa : σ .xa = csyms A w ⟨r, 0⟩)
    (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = []) (hpr : σ .pr = []) (hac : σ .ac = [])
    (hac2 : σ .ac2 = []) (hnv : σ .nv = []) (hb1 : σ .b1 = []) (htC : σ .tC = [])
    (htA : σ .tA = []) :
    RsbRuns body rg ι (bandNewtonStepP rg hι hT hQ) σ
      (Function.update σ .xa (csyms A w ⟨newtonStepZ P c r, 0⟩))
      (bandNewtonStepCost T w) := by
  have hwn := hready.wn
  set t : ℤ := (c*r).tdiv (2^P) with ht
  set q : ℤ := (r*t).tdiv (2^P) with hq
  -- t = c r
  have h₁ := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA bandFree_hv (ρ := σ)
    hready hw hp [⟨c, 0⟩] [⟨r, 0⟩] rfl (by simpa using hfc) (by simpa using hfr)
    (by simp [hhv, cstream]) (by simp [hxa, cstream])
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, tdivN_real, hhc, List.append_nil,
    cstream, List.flatMap_cons, List.flatMap_nil] at h₁
  set σ₁ := Function.update σ .hc (csyms A w ⟨t, 0⟩)
  -- ya = r
  have h₂ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .ya)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₁ (by simp [σ₁, hb1])
    (by simp [σ₁, htC])
  set σ₂ := Function.update σ₁ .ya (σ₁ .xa ++ σ₁ .ya)
  -- xs = t
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .hc) (b := .ac2) (by decide) σ₂
  set σ₃ := Function.update (Function.update σ₂ .hc []) .ac2 ((σ₂ .hc).reverse ++ σ₂ .ac2)
  have h₄ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .xs) (by decide) σ₃
  set σ₄ := Function.update (Function.update σ₃ .ac2 []) .xs ((σ₃ .ac2).reverse ++ σ₃ .xs)
  have hready₄ : RsbReady σ₄ w P := by
    simp only [σ₄, σ₃, σ₂, σ₁]
    exact (((((hready.update .hc (fun c => by simp) _).update .ya (fun c => by simp) _).update
      .hc (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2 (fun c => by simp)
      _).update .xs (fun c => by simp) _
  -- q = r t
  have h₅ := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA bandFree_ya (ρ := σ₄)
    hready₄ hw hp [⟨r, 0⟩] [⟨t, 0⟩] rfl (by simpa using hfr) (by simpa using hft)
    (by simp [σ₄, σ₃, σ₂, σ₁, hya, hxa, cstream]) (by simp [σ₄, σ₃, σ₂, σ₁, hac2, hxs, cstream])
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, tdivN_real, cstream,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at h₅
  set σ₅ := Function.update σ₄ .pr (csyms A w ⟨q, 0⟩ ++ σ₄ .pr)
  have h₆ := rsb_emptyR_runs (body := body) (ι := ι) hrg .ya σ₅
  have h₇ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xs (Function.update σ₅ .ya [])
  set σ₇ := Function.update (Function.update σ₅ .ya []) .xs []
  -- ac = r
  have h₈ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .ac)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₇
    (by simp [σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₈ := Function.update σ₇ .ac (σ₇ .xa ++ σ₇ .ac)
  -- ac2 = rev (q - r)
  have h₉ := rsb_subWord_runs (body := body) (ι := ι) hrg hA (a := .pr) (b := .ac) (o := .ac2)
    (ctr := .cm .wn) (tmp := .tA) (w := w) (by decide) σ₈ ⟨q, 0⟩ ⟨r, 0⟩ [] []
    (by simp [σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hpr])
    (by simp [σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hxa, hac])
    (by simp [σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hwn]) (by simp [σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
  set σ₉ := Function.update (Function.update (Function.update σ₈ .pr []) .ac []) .ac2
    ((csyms A w (⟨q, 0⟩-⟨r, 0⟩)).reverse ++ σ₈ .ac2)
  have h₁₀ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .nv) (by decide) σ₉
  set σ₁₀ := Function.update (Function.update σ₉ .ac2 []) .nv ((σ₉ .ac2).reverse ++ σ₉ .nv)
  -- ac2 = rev (r - (q - r))
  have h₁₁ := rsb_subWord_runs (body := body) (ι := ι) hrg hA (a := .xa) (b := .nv) (o := .ac2)
    (ctr := .cm .wn) (tmp := .tA) (w := w) (by decide) σ₁₀ ⟨r, 0⟩ (⟨q, 0⟩-⟨r, 0⟩) [] []
    (by simp [σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hxa])
    (by simp [σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hac2, hnv])
    (by simp [σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hwn])
    (by simp [σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
  set σ₁₁ := Function.update (Function.update (Function.update σ₁₀ .xa []) .nv []) .ac2
    ((csyms A w (⟨r, 0⟩-(⟨q, 0⟩-⟨r, 0⟩))).reverse ++ σ₁₀ .ac2)
  have h₁₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .xa) (by decide) σ₁₁
  have hval : (⟨r, 0⟩ : GaussianInt)-(⟨q, 0⟩-⟨r, 0⟩)=⟨newtonStepZ P c r, 0⟩ := by
    ext <;> simp [newtonStepZ, hq, ht] <;> ring
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj h₆ (RsbRuns.seq hdisj h₇
    (RsbRuns.seq hdisj h₈ (RsbRuns.seq hdisj h₉ (RsbRuns.seq hdisj h₁₀
    (RsbRuns.seq hdisj h₁₁ h₁₂))))))))))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₁₁, σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hhc, hya, hxs, hpr,
      hac, hac2, hnv, hval]
  · simp [σ₁₁, σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hhc, hya, hxs, hpr, hac, hac2, hnv, hxa,
      hwn, bandNewtonStepCost, cstream]
    omega

/-- The Newton loop: `xa` ends with `newtonZ P c K`. -/
theorem band_newton_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P K : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (c : ℤ) (hfc : Fits w (⟨c, 0⟩ : GaussianInt))
    (hfit : ∀ n < K, Fits w (⟨Mult.BandFactor.newtonZ P c n, 0⟩ : GaussianInt) ∧
      Fits w (⟨(c*Mult.BandFactor.newtonZ P c n).tdiv (2^P), 0⟩ : GaussianInt))
    (hbx : σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩)
    (hhv : σ .hv = csyms A w ⟨c, 0⟩) (hxa : σ .xa = [])
    (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = []) (hpr : σ .pr = []) (hac : σ .ac = [])
    (hac2 : σ .ac2 = []) (hnv : σ .nv = []) (hb1 : σ .b1 = []) (htC : σ .tC = [])
    (htA : σ .tA = []) (htK : σ .tK = []) (hkn : (σ .kn).length = K) :
    RsbRuns body rg ι (bandNewtonP rg hι hT hQ) σ
      (Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c K, 0⟩))
      (6 * w + 6 + (K * (bandNewtonStepCost T w + 6) + 4)) := by
  have hcsl : (csyms A w (⟨Mult.BandFactor.newtonZ P c 0, 0⟩ : GaussianInt)).length = w := by
    simp [csyms]
  have h₁ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .bx) (b := .xa)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ hb1 htC
  rw [hbx, hxa, List.append_nil, hcsl] at h₁
  set σ₁ := Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c j, 0⟩) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ₁ .kn).length, ∀ X Y, RsbRuns body rg ι (bandNewtonStepP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .kn X .tK Y) (rsbUpd2 (Ψ (j + 1)) .kn X .tK Y) (bandNewtonStepCost T w) := by
    intro j hj X Y
    have hj' : j < K := by simpa [σ₁, hkn] using hj
    have hready' : RsbReady (rsbUpd2 (Ψ j) .kn X .tK Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((hready.update .xa (fun c => by simp) _).update .kn (fun c => by simp) _).update .tK
        (fun c => by simp) _
    have hstep := band_newtonStep_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA
      (rsbUpd2 (Ψ j) .kn X .tK Y) hready' hw hp c (Mult.BandFactor.newtonZ P c j) hfc
      (hfit j hj').1 (hfit j hj').2 (by simp [rsbUpd2, hΨ, hhv]) (by simp [rsbUpd2, hΨ])
      (by simp [rsbUpd2, hΨ, hhc]) (by simp [rsbUpd2, hΨ, hya]) (by simp [rsbUpd2, hΨ, hxs])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hac]) (by simp [rsbUpd2, hΨ, hac2])
      (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, hb1]) (by simp [rsbUpd2, hΨ, htC])
      (by simp [rsbUpd2, hΨ, htA])
    refine hstep.congr ?_
    funext r; cases r <;> simp [rsbUpd2, hΨ, newtonZ_succ]
  have h₂ := rsb_rep_runs hrg hdisj (ra := .kn) (rt := .tK) (by decide)
    (bandNewtonStepP rg hι hT hQ) (σ₁ .kn) Ψ _ hbody
  refine ((RsbRuns.seq hdisj h₁ ((h₂.congr_pre ?_).congr ?_)).mono ?_)
  · funext r; cases r <;> simp [rsbUpd2, hΨ, σ₁, htK]
  · funext r; cases r <;> simp [rsbUpd2, hΨ, σ₁, htK, hkn]
  · simp [σ₁, hkn]

end Contracts

end IntegerMultBounds.MathlibTM2.Fast
