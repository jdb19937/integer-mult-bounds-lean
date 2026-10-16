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

/-- One non-pivot row of a window step: multiplier by the stored reciprocal,
row update against the pivot-row copy on `ef`, then the updated row moves to
the new window `sr` (reversed) followed by the zero record of `msk`. -/
noncomputable def bandFacRowP : Pr P T Q A U :=
  .seq (bandBwdStepP rg hι hT hQ) (.seq (rsbMv (rg .mwn) (rg .tC) (rg .vk) (rg .sr))
    (copyR (rg .msk) (rg .sr) (rg .tC) id))

/-- The `B` non-pivot rows of a window step, one per symbol of `ms`. -/
noncomputable def bandFacRowsP : Pr P T Q A U := rsbRep (rg .ms) (rg .tL) (bandFacRowP rg hι hT hQ)

/-- One window step: pivot row out to `hf`, its Newton reciprocal out to `df`,
the `B` non-pivot rows updated into the new window, the next input row of `src`
appended. -/
noncomputable def bandFacStepP : Pr P T Q A U :=
  .seq (bandPopP rg)
  (.seq (rsbMv (rg .mwn) (rg .tC) (rg .vk) (rg .ac2))
  (.seq (moveR (rg .ac2) (rg .bo) id)
  (.seq (bandNewtonP rg hι hT hQ)
  (.seq (rsbCopyTo rg .bo .hf) (.seq (rsbCopyTo rg .hv .hf)
  (.seq (rsbCopyTo rg .xa .df)
  (.seq (rsbRep (rg .ms) (rg .tL) (rsbCopyTo rg .bo .ef))
  (.seq (rsbRep (rg .ms) (rg .tL) (rsbCopyTo rg .xa .tb))
  (.seq (emptyR (rg .hv)) (.seq (emptyR (rg .xa)) (.seq (emptyR (rg .bo))
  (.seq (bandFacRowsP rg hι hT hQ)
  (.seq (rsbMv (rg .smwn) (rg .tC) (rg .src) (rg .sr))
  (moveR (rg .sr) (rg .vk) id))))))))))))))

end Programs

/-- A Newton step on real records. -/
def newtonStepZ (P : ℕ) (c r : ℤ) : ℤ := 2*r-(r*(c*r).tdiv (2^P)).tdiv (2^P)

lemma tdivN_real (P : ℕ) (a b : ℤ) :
    tdivN P ((⟨a, 0⟩ : GaussianInt)*⟨b, 0⟩)=⟨(a*b).tdiv (2^P), 0⟩ := by
  ext <;> simp [tdivN]

lemma newtonZ_succ (P : ℕ) (c : ℤ) (n : ℕ) :
    Mult.BandFactor.newtonZ P c (n+1)=newtonStepZ P c (Mult.BandFactor.newtonZ P c n) := rfl

lemma machine_row (P : ℕ) (x : ℤ) : ∀ (n : ℕ) (u v : List ℤ), u.length=n → v.length=n →
    List.zipWith (· - ·) (colC v) (List.zipWith (fun a b => tdivN P (a * b))
      (List.replicate n (⟨x, 0⟩ : GaussianInt)) (colC u))=colC (Mult.BandFactor.subRowZ P x u v)
  | 0, [], [], _, _ => rfl
  | n+1, a::u, b::v, hu, hv => by
    have ih := machine_row P x n u v (by simpa using hu) (by simpa using hv)
    simp only [colC, List.map_cons, List.replicate_succ, List.zipWith_cons_cons,
      Mult.BandFactor.subRowZ] at ih ⊢
    rw [ih, tdivN_real]
    congr 1
  | 0, _::_, _, hu, _ => by simp at hu
  | 0, [], _::_, _, hv => by simp at hv
  | _+1, [], _, hu, _ => by simp at hu
  | _+1, _::_, [], _, hv => by simp at hv

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

/-- The cost of one non-pivot row (rows of `2B` tail records). -/
def bandFacRowCost (T w B : ℕ) : ℕ :=
  rmulCost T w + 30 * w + 40 + bandFwdStepCost T w (2 * B) + 4 * (2 * B * w) + 4 * w + 8

/-- One non-pivot row: `vk` loses the row, `dout` gains its multiplier `x`, and `sr`
gains the updated tail followed by a zero record, reversed. -/
theorem band_facRow_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (q : GaussianInt) (r : ℤ) (rs more col cols : List GaussianInt)
    (hrs : rs.length = 2 * B) (hcol : col.length = 2 * B) (hfq : Fits w q)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt)) (hfx : Fits w (tdivN P (q * ⟨r, 0⟩)))
    (hfc : ∀ a ∈ col, Fits w a ∧ a.im = 0) (D TB SR : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (q :: (rs ++ more))) (htb : σ .tb = csyms A w ⟨r, 0⟩ ++ TB)
    (hef : σ .ef = cstream A w (col ++ cols)) (hsr : σ .sr = SR)
    (hmsk : σ .msk = csyms A w 0)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hxa : σ .xa = []) (hhc : σ .hc = [])
    (hm2n : (σ .m2n).length = 2 * B) (hmwn : (σ .mwn).length = 2 * B * w) :
    RsbRuns body rg ι (bandFacRowP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w more)) .tb TB) .ef (cstream A w cols)) .dout
        (csyms A w (tdivN P (q * ⟨r, 0⟩)) ++ D)) .sr
        ((cstream A w (List.zipWith (· - ·) rs
          (List.zipWith (fun a b => tdivN P (a * b))
            (List.replicate (2 * B) (tdivN P (q * ⟨r, 0⟩))) col) ++ [0])).reverse ++ SR))
      (bandFacRowCost T w B) := by
  set rs' := List.zipWith (· - ·) rs (List.zipWith (fun a b => tdivN P (a * b))
    (List.replicate (2 * B) (tdivN P (q * ⟨r, 0⟩))) col) with hrs'
  have hrs'l : rs'.length = 2 * B := by simp [hrs', hrs, hcol]
  have h₁ := band_bwdStep_runs (body := body) (ι := ι) (w := w) (B := 2 * B) hrg hdisj hι
    hT hQ hA σ hready hw hp q r rs more col cols hrs hcol hfq hfr hfx hfc D TB hvk htb hef hdout
    hhv hya hxs hpr hnv hac hac2 htC htA htJ hb1 hxa hhc hm2n hmwn
  rw [← hrs'] at h₁
  set σ₁ := Function.update (Function.update (Function.update (Function.update σ .vk
    (cstream A w (rs' ++ more))) .tb TB) .ef (cstream A w cols)) .dout
    (csyms A w (tdivN P (q * ⟨r, 0⟩)) ++ D)
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .vk) (y := .sr)
    (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hmwn, hrs'l])
  have hmw : (σ₁ .mwn).length = rs'.length * w := by simp [σ₁, hmwn, hrs'l]
  rw [hmw] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.dout),
    Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ef),
    Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.tb), Function.update_self,
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.dout),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.ef),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.tb),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.vk), hsr, cstream_append,
    take_cstream rs' rs'.length le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₂
  set σ₂ := Function.update (Function.update σ₁ .vk (cstream A w more)) .sr
    ((cstream A w rs').reverse ++ SR)
  have h₃ := rsb_copyR_runs (body := body) (ι := ι) hrg (a := .msk) (b := .sr) (t := .tC)
    (by decide) (by decide) (by decide) σ₂ (by simp [σ₂, σ₁, htC])
  have h₂' := h₂.congr_pre (ρ₀ := σ₁) (by simp only [σ₁, cstream_append])
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj (h₂'.congr ?_) h₃)).congr ?_).mono ?_
  · simp only [σ₂, σ₁, cstream_append]
  · funext x; cases x <;> simp [σ₂, σ₁, hmsk, cstream_append, List.reverse_append]
  · simp [σ₂, σ₁, hmsk, bandFacRowCost, hmwn, hrs'l, csyms]
    nlinarith

/-- The multiplier of a row with head `h` and pivot reciprocal `r`. -/
def facMul (P : ℕ) (r : ℤ) (row : List ℤ) : ℤ := (row.headD 0*r).tdiv (2^P)

/-- The updated, shifted row. -/
def facRow (P : ℕ) (r : ℤ) (tail0 row : List ℤ) : List ℤ :=
  Mult.BandFactor.subRowZ P (facMul P r row) tail0 row.tail++[0]

/-- The `B` non-pivot rows of a window step. -/
theorem band_facRows_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (r : ℤ) (tail0 : List ℤ) (rest : List (List ℤ)) (htl : tail0.length = 2 * B)
    (hrest : rest.length = B) (hrow : ∀ row ∈ rest, row.length = 2 * B + 1)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt)) (hft : ∀ a ∈ tail0, Fits w (⟨a, 0⟩ : GaussianInt))
    (hfh : ∀ row ∈ rest, Fits w (⟨row.headD 0, 0⟩ : GaussianInt) ∧
      Fits w (⟨facMul P r row, 0⟩ : GaussianInt))
    (D TB SR : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (rest.map colC).flatten)
    (htb : σ .tb = cstream A w (List.replicate B ⟨r, 0⟩) ++ TB)
    (hef : σ .ef = cstream A w (List.replicate B (colC tail0)).flatten) (hsr : σ .sr = SR)
    (hmsk : σ .msk = csyms A w 0)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hxa : σ .xa = []) (hhc : σ .hc = []) (htL : σ .tL = []) (hms : (σ .ms).length = B)
    (hm2n : (σ .m2n).length = 2 * B) (hmwn : (σ .mwn).length = 2 * B * w) :
    RsbRuns body rg ι (bandFacRowsP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        []) .tb TB) .ef []) .dout
        (cstream A w ((rest.map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)) .sr
        ((cstream A w (rest.map fun row => colC (facRow P r tail0 row)).flatten).reverse ++ SR))
      (B * (bandFacRowCost T w B + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((rest.drop j).map colC).flatten)) .tb
        (cstream A w (List.replicate (B-j) ⟨r, 0⟩) ++ TB)) .ef
        (cstream A w (List.replicate (B-j) (colC tail0)).flatten)) .dout
        (cstream A w (((rest.take j).map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D))
        .sr ((cstream A w ((rest.take j).map fun row => colC (facRow P r tail0 row)).flatten).reverse ++
          SR) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .ms).length, ∀ X Y, RsbRuns body rg ι (bandFacRowP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .ms X .tL Y) (rsbUpd2 (Ψ (j + 1)) .ms X .tL Y) (bandFacRowCost T w B) := by
    intro j hj X Y
    rw [hms] at hj
    have hjr : j < rest.length := by omega
    set row := rest[j]'hjr with hrowdef
    have hrl := hrow row (List.getElem_mem hjr)
    obtain ⟨h, tl, hht⟩ : ∃ h tl, row = h :: tl := by
      cases hr : row with
      | nil => rw [hr] at hrl; simp at hrl
      | cons h tl => exact ⟨h, tl, rfl⟩
    have htll : tl.length = 2 * B := by rw [hht] at hrl; simp at hrl; omega
    have hfhj := hfh row (List.getElem_mem hjr)
    rw [hht] at hfhj
    have hready' : RsbReady (rsbUpd2 (Ψ j) .ms X .tL Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((((((hready.update .vk (fun c => by simp) _).update .tb (fun c => by simp) _).update
        .ef (fun c => by simp) _).update .dout (fun c => by simp) _).update .sr (fun c => by simp)
        _).update .ms (fun c => by simp) _).update .tL (fun c => by simp) _
    have hBj : B-j=(B-(j+1))+1 := by omega
    have hstep := band_facRow_runs (body := body) (ι := ι) (w := w) (B := B) hrg hdisj hι hT hQ hA
      (rsbUpd2 (Ψ j) .ms X .tL Y) hready' hw hp ⟨h, 0⟩ r (colC tl)
      ((rest.drop (j+1)).map colC).flatten (colC tail0)
      (List.replicate (B-(j+1)) (colC tail0)).flatten (by simp [colC, htll])
      (by simp [colC, htl]) hfhj.1 hfr (by rw [tdivN_real]; simpa [facMul, hht] using hfhj.2)
      (by intro a ha; simp only [colC, List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
          exact ⟨hft x hx, rfl⟩)
      (cstream A w (((rest.take j).map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)
      (cstream A w (List.replicate (B-(j+1)) ⟨r, 0⟩) ++ TB)
      ((cstream A w ((rest.take j).map fun row => colC (facRow P r tail0 row)).flatten).reverse ++ SR)
      (by
        simp only [rsbUpd2, hΨ, Function.update_self, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.tL),
          Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ms)]
        rw [List.drop_eq_getElem_cons hjr, ← hrowdef, hht]
        simp [colC])
      (by simp [rsbUpd2, hΨ, hBj, List.replicate_succ])
      (by simp [rsbUpd2, hΨ, hBj, List.replicate_succ])
      (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ, hmsk]) (by simp [rsbUpd2, hΨ])
      (by simp [rsbUpd2, hΨ, hhv]) (by simp [rsbUpd2, hΨ, hya]) (by simp [rsbUpd2, hΨ, hxs])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, hac])
      (by simp [rsbUpd2, hΨ, hac2]) (by simp [rsbUpd2, hΨ, htC]) (by simp [rsbUpd2, hΨ, htA])
      (by simp [rsbUpd2, hΨ, htJ]) (by simp [rsbUpd2, hΨ, hb1]) (by simp [rsbUpd2, hΨ, hxa])
      (by simp [rsbUpd2, hΨ, hhc]) (by simp [rsbUpd2, hΨ, hm2n]) (by simp [rsbUpd2, hΨ, hmwn])
    refine hstep.congr ?_
    have htake : ∀ {β : Type} (F : List ℤ → β), (rest.map F).take (j+1)=(rest.map F).take j++[F row] := by
      intro β F
      rw [List.take_succ_eq_append_getElem (by simpa using hjr), List.getElem_map]
    have hmr := machine_row P (facMul P r row) (2 * B) tail0 tl htl htll
    rw [tdivN_real]
    have hfm : facMul P r row=(h*r).tdiv (2^P) := by simp [facMul, hht]
    rw [← hfm, hmr]
    have h0 : (0 : GaussianInt)=⟨0, 0⟩ := rfl
    funext x; cases x <;> simp [rsbUpd2, hΨ, htake, facRow, hht, colC, List.reverse_append, h0]
  have h := rsb_rep_runs hrg hdisj (ra := .ms) (rt := .tL) (by decide) (bandFacRowP rg hι hT hQ)
    (σ .ms) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext x; cases x <;> simp [rsbUpd2, hΨ, hvk, htb, hef, hdout, hsr, htL]
  · rw [hms]
    have hd : (rest.map colC).drop B=[] := List.drop_of_length_le (by simp [hrest])
    funext x; cases x <;> simp [rsbUpd2, hΨ, htL, hrest, List.take_of_length_le, hd]
  · rw [hms]

/-- `B` copies of register `a` onto `b`, one per symbol of `ms`. -/
theorem band_copyRep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {a b : RsbR}
    (ha : a ≠ .b1 ∧ a ≠ .tC ∧ a ≠ .ms ∧ a ≠ .tL) (hb : b ≠ .b1 ∧ b ≠ .tC ∧ b ≠ .ms ∧ b ≠ .tL)
    (hab : a ≠ b) {B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hb1 : σ .b1 = []) (htC : σ .tC = [])
    (htL : σ .tL = []) (hms : (σ .ms).length = B) :
    RsbRuns body rg ι (rsbRep (rg .ms) (rg .tL) (rsbCopyTo rg a b)) σ
      (Function.update σ b ((List.replicate B (σ a)).flatten ++ σ b))
      (B * (6 * (σ a).length + 6 + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update σ b ((List.replicate j (σ a)).flatten ++ σ b) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .ms).length, ∀ X Y, RsbRuns body rg ι (rsbCopyTo rg a b)
      (rsbUpd2 (Ψ j) .ms X .tL Y) (rsbUpd2 (Ψ (j + 1)) .ms X .tL Y) (6 * (σ a).length + 6) := by
    intro j _ X Y
    have h := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj ⟨ha.1, ha.2.1⟩ ⟨hb.1, hb.2.1⟩ hab
      (rsbUpd2 (Ψ j) .ms X .tL Y)
      (by simp [rsbUpd2, hΨ, Function.update_of_ne hb.1.symm, hb1])
      (by simp [rsbUpd2, hΨ, Function.update_of_ne hb.2.1.symm, htC])
    have hA : rsbUpd2 (Ψ j) .ms X .tL Y a=σ a := by
      simp [rsbUpd2, hΨ, Function.update_of_ne hab, Function.update_of_ne ha.2.2.1,
        Function.update_of_ne ha.2.2.2]
    rw [hA] at h
    refine h.congr ?_
    funext x
    simp only [rsbUpd2, hΨ, Function.update_apply, List.replicate_succ, List.flatten_cons,
      List.append_assoc]
    split_ifs <;> simp_all
  have h := rsb_rep_runs hrg hdisj (ra := .ms) (rt := .tL) (by decide) (rsbCopyTo rg a b)
    (σ .ms) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext x
    simp only [rsbUpd2, hΨ, Function.update_apply, List.replicate_zero, List.flatten_nil,
      List.nil_append]
    split_ifs <;> simp_all
  · funext x
    simp only [rsbUpd2, hΨ, Function.update_apply, hms]
    split_ifs <;> simp_all
  · rw [hms]

lemma flatten_replicate_cstream {w : ℕ} (B : ℕ) (X : List GaussianInt) :
    (List.replicate B (cstream A w X)).flatten=cstream A w (List.replicate B X).flatten := by
  induction B with
  | zero => simp
  | succ B ih => simp [List.replicate_succ, ih]

lemma flatten_replicate_csyms {w : ℕ} (B : ℕ) (x : GaussianInt) :
    (List.replicate B (csyms A w x)).flatten=cstream A w (List.replicate B x) := by
  induction B with
  | zero => simp
  | succ B ih => simp [List.replicate_succ, ih]

/-- The cost of one window step. -/
def bandFacStepCost (T w B K : ℕ) : ℕ :=
  100 * (B + 1) * (B + 1) * w + 200 + (K * (bandNewtonStepCost T w + 6) + 4) +
    (B * (bandFacRowCost T w B + 6) + 4)

/-- **One window step.** The pivot row `c :: tail0` goes to `hf`, its reciprocal
`r = newtonZ P c K` to `df`, the multipliers of the `B` rows (last on top) to
`dout`, and `vk` becomes the updated rows followed by the next input row of `src`. -/
theorem band_facStep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B K : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (c : ℤ) (tail0 next : List ℤ) (rest : List (List ℤ))
    (htl : tail0.length = 2 * B) (hnext : next.length = 2 * B + 1)
    (hrest : rest.length = B) (hrow : ∀ row ∈ rest, row.length = 2 * B + 1)
    (hfc : Fits w (⟨c, 0⟩ : GaussianInt))
    (hfit : ∀ n < K, Fits w (⟨Mult.BandFactor.newtonZ P c n, 0⟩ : GaussianInt) ∧
      Fits w (⟨(c*Mult.BandFactor.newtonZ P c n).tdiv (2^P), 0⟩ : GaussianInt))
    (hfr : Fits w (⟨Mult.BandFactor.newtonZ P c K, 0⟩ : GaussianInt))
    (hft : ∀ a ∈ tail0, Fits w (⟨a, 0⟩ : GaussianInt))
    (hfh : ∀ row ∈ rest, Fits w (⟨row.headD 0, 0⟩ : GaussianInt) ∧
      Fits w (⟨facMul P (Mult.BandFactor.newtonZ P c K) row, 0⟩ : GaussianInt))
    (SRC HF DF D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (colC (c :: tail0) ++ (rest.map colC).flatten))
    (hsrc : σ .src = cstream A w (colC next) ++ SRC)
    (hhf : σ .hf = HF) (hdf : σ .df = DF) (hdout : σ .dout = D)
    (hbx : σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩) (hmsk : σ .msk = csyms A w 0)
    (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = [])
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = B) (hm2n : (σ .m2n).length = 2 * B)
    (hmwn : (σ .mwn).length = 2 * B * w) (hsmwn : (σ .smwn).length = (2 * B + 1) * w) :
    RsbRuns body rg ι (bandFacStepP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((rest.map fun row =>
          colC (facRow P (Mult.BandFactor.newtonZ P c K) tail0 row)).flatten ++ colC next)))
        .src SRC) .hf (cstream A w (colC (c :: tail0)) ++ HF))
        .df (csyms A w ⟨Mult.BandFactor.newtonZ P c K, 0⟩ ++ DF))
        .dout (cstream A w ((rest.map fun row =>
          (⟨facMul P (Mult.BandFactor.newtonZ P c K) row, 0⟩ : GaussianInt)).reverse) ++ D))
      (bandFacStepCost T w B K) := by
  have hwn := hready.wn
  set r := Mult.BandFactor.newtonZ P c K with hr
  set RS := cstream A w (rest.map colC).flatten with hRS
  have htl' : (colC tail0).length = 2 * B := by simp [colC, htl]
  -- pop the pivot
  have h₁ := band_pop_runs (body := body) (ι := ι) hrg hdisj σ ⟨c, 0⟩
    (cstream A w (colC tail0) ++ RS) (by rw [hvk]; simp [colC, hRS]) hhv hac2 htC hwn
  set σ₁ := Function.update (Function.update σ .vk (cstream A w (colC tail0) ++ RS)) .hv
    (csyms A w ⟨c, 0⟩)
  -- the pivot tail to `bo`
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .vk) (y := .ac2)
    (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hmwn, htl'])
  have hmw : (σ₁ .mwn).length=(colC tail0).length * w := by simp [σ₁, hmwn, htl']
  rw [hmw] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.hv), Function.update_self,
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.hv),
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.vk), take_cstream _ _ le_rfl,
    drop_cstream, List.take_length, List.drop_length, Nat.sub_self, zero_mul, List.drop_zero,
    cstream_nil, List.nil_append, hac2, List.append_nil] at h₂
  have h₂' := h₂.congr_pre (ρ₀ := σ₁) rfl
  set σ₂ := Function.update (Function.update σ₁ .vk RS) .ac2 (cstream A w (colC tail0)).reverse
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .bo) (by decide) σ₂
  set σ₃ := Function.update (Function.update σ₂ .ac2 []) .bo ((σ₂ .ac2).reverse ++ σ₂ .bo)
  have hready₃ : RsbReady σ₃ w P := by
    simp only [σ₃, σ₂, σ₁]
    exact (((((hready.update .vk (fun c => by simp) _).update .hv (fun c => by simp) _).update
      .vk (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2 (fun c => by simp)
      _).update .bo (fun c => by simp) _
  -- Newton
  have h₄ := band_newton_runs (body := body) (ι := ι) (K := K) hrg hdisj hι hT hQ hA σ₃ hready₃ hw hp
    c hfc hfit (by simp [σ₃, σ₂, σ₁, hbx]) (by simp [σ₃, σ₂, σ₁]) (by simp [σ₃, σ₂, σ₁, hxa])
    (by simp [σ₃, σ₂, σ₁, hhc]) (by simp [σ₃, σ₂, σ₁, hya]) (by simp [σ₃, σ₂, σ₁, hxs])
    (by simp [σ₃, σ₂, σ₁, hpr]) (by simp [σ₃, σ₂, σ₁, hac]) (by simp [σ₃, σ₂, σ₁])
    (by simp [σ₃, σ₂, σ₁, hnv]) (by simp [σ₃, σ₂, σ₁, hb1]) (by simp [σ₃, σ₂, σ₁, htC])
    (by simp [σ₃, σ₂, σ₁, htA]) (by simp [σ₃, σ₂, σ₁, htK]) (by simp [σ₃, σ₂, σ₁, hkn])
  rw [← hr] at h₄
  set σ₄ := Function.update σ₃ .xa (csyms A w ⟨r, 0⟩)
  -- outputs
  have h₅ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .bo) (b := .hf)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₄ (by simp [σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₄, σ₃, σ₂, σ₁, htC])
  set σ₅ := Function.update σ₄ .hf (σ₄ .bo ++ σ₄ .hf)
  have h₆ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .hv) (b := .hf)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₅ (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₆ := Function.update σ₅ .hf (σ₅ .hv ++ σ₅ .hf)
  have h₇ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .df)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₆
    (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₇ := Function.update σ₆ .df (σ₆ .xa ++ σ₆ .df)
  -- copies for the rows
  have h₈ := band_copyRep_runs (body := body) (ι := ι) hrg hdisj (a := .bo) (b := .ef)
    ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩
    (by decide) (B := B) σ₇ (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
  set σ₈ := Function.update σ₇ .ef ((List.replicate B (σ₇ .bo)).flatten ++ σ₇ .ef)
  have h₉ := band_copyRep_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .tb)
    ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩
    (by decide) (B := B) σ₈ (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
  set σ₉ := Function.update σ₈ .tb ((List.replicate B (σ₈ .xa)).flatten ++ σ₈ .tb)
  have h₁₀ := rsb_emptyR_runs (body := body) (ι := ι) hrg .hv σ₉
  have h₁₁ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xa (Function.update σ₉ .hv [])
  have h₁₂ := rsb_emptyR_runs (body := body) (ι := ι) hrg .bo
    (Function.update (Function.update σ₉ .hv []) .xa [])
  set σ₁₂ := Function.update (Function.update (Function.update σ₉ .hv []) .xa []) .bo []
  have hready₁₂ : RsbReady σ₁₂ w P := by
    simp only [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄]
    exact ((((((((hready₃.update .xa (fun c => by simp) _).update .hf (fun c => by simp) _).update
      .hf (fun c => by simp) _).update .df (fun c => by simp) _).update .ef (fun c => by simp)
      _).update .tb (fun c => by simp) _).update .hv (fun c => by simp) _).update .xa
      (fun c => by simp) _).update .bo (fun c => by simp) _
  -- the rows
  have h₁₃ := band_facRows_runs (body := body) (ι := ι) (w := w) (B := B) hrg hdisj hι hT hQ hA
    σ₁₂ hready₁₂ hw hp r tail0 rest htl hrest hrow hfr hft hfh D [] []
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hRS])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htb, flatten_replicate_csyms])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, hbo, flatten_replicate_cstream])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsr])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hmsk])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hdout])
    (by simp [σ₁₂]) (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hya])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hxs])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hpr])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hnv])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hac])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hac2])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htJ])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₁₂])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hhc])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hm2n])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hmwn])
  set NR := cstream A w (rest.map fun row => colC (facRow P r tail0 row)).flatten
  set σ₁₃ := Function.update (Function.update (Function.update (Function.update (Function.update
    σ₁₂ .vk []) .tb []) .ef []) .dout (cstream A w ((rest.map fun row =>
      (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)) .sr (NR.reverse ++ [])
  -- the next input row
  have hnl : (colC next).length = 2 * B + 1 := by simp [colC, hnext]
  have h₁₄ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .smwn) (t := .tC) (x := .src) (y := .sr)
    (by decide) σ₁₃ (by simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsmwn, hsrc, hnl])
  have hsw : (σ₁₃ .smwn).length=(colC next).length * w := by
    simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsmwn, hnl]
  have hsrc₁₃ : σ₁₃ .src=cstream A w (colC next) ++ SRC := by
    simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsrc]
  rw [hsw, hsrc₁₃, take_cstream _ _ le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₁₄
  set σ₁₄ := Function.update (Function.update σ₁₃ .src SRC) .sr
    ((cstream A w (colC next)).reverse ++ σ₁₃ .sr)
  have h₁₅ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .sr) (b := .vk) (by decide) σ₁₄
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂' (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj h₆ (RsbRuns.seq hdisj h₇
    (RsbRuns.seq hdisj h₈ (RsbRuns.seq hdisj h₉ (RsbRuns.seq hdisj h₁₀ (RsbRuns.seq hdisj h₁₁
    (RsbRuns.seq hdisj h₁₂ (RsbRuns.seq hdisj h₁₃ (RsbRuns.seq hdisj h₁₄
    h₁₅)))))))))))))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₁₄, σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, htb, hsr,
      hbo, hhv, hxa, hac2, hhf, hdf, NR, colC, List.reverse_append]
  · simp [σ₁₄, σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, htb, hsr, hbo, hhv, hxa, hac2,
      hhf, hdf, hwn, bandFacStepCost, htl', hnl, hmwn, csyms, colC, htl, NR, hRS]
    have hsum : (List.map (List.length ∘ fun row => List.map (fun x => (⟨x, 0⟩ : GaussianInt))
        (facRow P r tail0 row)) rest).sum=B*(2*B+1) := by
      rw [List.map_congr_left (g := fun _ => 2*B+1) (fun row hr => by
        simp [facRow, Mult.BandFactor.subRowZ, htl, hrow row hr]), List.map_const',
        List.sum_replicate, hrest, smul_eq_mul]
    rw [hsum, hnext]
    nlinarith

end Contracts

end IntegerMultBounds.MathlibTM2.Fast
