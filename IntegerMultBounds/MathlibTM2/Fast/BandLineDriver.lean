module

public import IntegerMultBounds.MathlibTM2.Fast.BandFold
public import IntegerMultBounds.MathlibTM2.Fast.BandRegs

/-!
# The banded line driver

One line of the banded `B̃₀`: select the rows, fold, scale to the working precision
and append `B` zero records; the two banded passes; unfold, scale back, multiply by
the diagonal table and pad. This file proves the phases.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node

set_option linter.unusedSimpArgs false

open IntegerMultBounds.NLogN (rowIndex)

theorem mem_interleave {α : Type*} (x : α) : ∀ (a b : List α),
    x ∈ Mult.BandFactor.interleave a b → x ∈ a ∨ x ∈ b
  | u :: as, v :: bs, h => by
    simp only [Mult.BandFactor.interleave, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact Or.inl (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_self ..)
    · rcases mem_interleave x as bs h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (List.mem_cons_of_mem _ h)
  | as, [], h => by cases as <;> simp_all [Mult.BandFactor.interleave]
  | [], _ :: _, h => by simp_all [Mult.BandFactor.interleave]

theorem mem_of_mem_foldList {α : Type*} (x : α) (v : List α) (h : x ∈ Mult.BandFactor.foldList v) :
    x ∈ v := by
  rcases mem_interleave x _ _ h with h | h
  · exact List.mem_of_mem_take h
  · exact List.mem_of_mem_drop (List.mem_reverse.mp h)

variable {T Q A : ℕ} {U : Type} {P : Type}

theorem csyms_zero' (w : ℕ) : csyms A w 0 = List.replicate w (pairSym A false false) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [csyms, coeffSyms, red]

section Programs

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

/-- Multiply the records of `x` by the constant on `y` onto `o`, emptying `x`. -/
noncomputable def bandScaleP (x y o : RsbR) : Pr P T Q A U :=
  .seq (cmulTable (rsbCr rg x y o) (rmulOne ι hι hT hQ (rsbCr rg x y o))) (emptyR (rg x))

/-- Select, fold, scale by the constant on `smwn` and append `B` zero records (`mwn` holds
`B w` symbols): the right-hand side of the forward pass on `vk`. -/
noncomputable def bandLineInP : Pr P T Q A U :=
  .seq (rsbSelP rg) (.seq (bandFoldLineP rg) (.seq (bandScaleP rg hι hT hQ .vk .smwn .ya)
  (.seq (umulSym 1 (pairSym A false false) (rg .mwn) (rg .vk) (rg .tC))
  (.seq (moveR (rg .ya) (rg .ac2) id) (moveR (rg .ac2) (rg .vk) id)))))

end Programs

section Contracts

variable {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

/-- **Scale by a constant.** -/
theorem band_scale_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o) {w P : ℕ} (σ : RsbR → List (Fin (A + 4)))
    (hr : RsbReady σ w P) (hw : 1 ≤ w) (hp : P ≤ w) (xs : List GaussianInt) (c : ℤ)
    (hfx : ∀ a ∈ xs, Fits w a) (hfc : Fits w (⟨c, 0⟩ : GaussianInt))
    (hx : σ x = cstream A w xs) (hy : σ y = csyms A w ⟨c, 0⟩) (ho : σ o = []) :
    RsbRuns body rg ι (bandScaleP rg hι hT hQ x y o) σ
      (Function.update (Function.update σ o
        (cstream A w (xs.map fun a => tdivN P (a * ⟨c, 0⟩)))) x [])
      (xs.length * (rmulCost T w + 6 * w + 8) + 6 + (2 * (xs.length * w) + 2)) := by
  have hsing : ∀ l : List GaussianInt, (l.map fun a => [a]).flatten = l := by
    intro l; induction l <;> simp_all
  obtain ⟨hxy, hxo, hyo, -⟩ := id hfree
  have H := rsb_rmulTable_runs (body := body) hrg hdisj hι hT hQ hA hfree hr hw hp
    (xs.map fun a => [a]) [⟨c, 0⟩] (by simp) (by simp) (by rwa [hsing])
    (by intro a ha; simp only [List.mem_singleton] at ha; subst ha; exact ⟨hfc, rfl⟩)
    (by rw [hsing, hx]) (by rw [hy]; simp [cstream])
  rw [tableOut_single, hsing, ho, List.append_nil] at H
  have H2 := rsb_emptyR_runs (body := body) (ι := ι) hrg x (Function.update σ o
    (cstream A w (xs.map fun a => tdivN P (a * ⟨c, 0⟩))))
  refine ((RsbRuns.seq hdisj H H2).congr rfl).mono ?_
  simp [Function.update_of_ne hxo, hx]

/-- **The input phase of a line.** -/
theorem band_lineIn_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P s t B : ℕ} [NeZero s] [NeZero t] (hst : s < t) (σ : RsbR → List (Fin (A + 4)))
    (hr : RsbReady σ w P) (hw : 1 ≤ w) (hp : P ≤ w) (N : ZMod t → GaussianInt)
    (hfN : ∀ j, Fits w (N j)) (cin : ℤ) (hfc : Fits w (⟨cin, 0⟩ : GaussianInt))
    (rest : List (Fin (A + 4))) (hsrc : σ .src = cstream A w (rsbArr N) ++ rest)
    (hmsk : σ .msk = (rsbMask s t).map bitSymbol) (hcin : σ .smwn = csyms A w ⟨cin, 0⟩)
    (htswn : (σ .tswn).length = (s + 1) / 2 * w) (hm2wn : (σ .m2wn).length = s / 2)
    (hkn : (σ .kn).length = (s + 1) / 2 - s / 2) (hsn : (σ .sn).length = s)
    (hmwn : (σ .mwn).length = B * w)
    (hms : σ .ms = []) (hsr : σ .sr = []) (hsel : σ .sel = []) (hvk : σ .vk = [])
    (hya : σ .ya = []) (hxs : σ .xs = []) (hnv : σ .nv = []) (htK : σ .tK = [])
    (htC : σ .tC = []) (hac2 : σ .ac2 = []) :
    ∃ b, RsbRuns body rg ι (bandLineInP rg hι hT hQ) σ
      (Function.update (Function.update σ .src rest) .vk
        (cstream A w ((Mult.BandFactor.foldList (rsbArr fun ℓ : ZMod s => N (rowIndex s t ℓ))).map
          (fun a => tdivN P (a * ⟨cin, 0⟩)) ++ List.replicate B 0))) b := by
  have hwn := hr.wn
  have hlen : (rsbArr N).length = (rsbMask s t).length := by rw [length_rsbArr, length_rsbMask]
  set SL := rsbArr fun ℓ : ZMod s => N (rowIndex s t ℓ) with hSL
  have hSLl : SL.length = s := by rw [hSL, length_rsbArr]
  have h₁ := rsb_sel_runs (body := body) (ι := ι) hrg hdisj σ (rsbMask s t) (rsbArr N) rest hlen
    hmsk hms hsrc hsr hsel htC hwn
  rw [rsbSel_full _ _ hlen, rsb_filter_mask hst N, ← hSL, length_rsbMask] at h₁
  set σ₁ := Function.update (Function.update σ .src rest) .sel (cstream A w SL)
  have h₂ := band_foldLine_runs (body := body) (ι := ι) hrg hdisj (w := w) σ₁ SL (by simp [σ₁])
    (by simp [σ₁, htswn, hSLl]) (by simp [σ₁, hm2wn, hSLl]) (by simp [σ₁, hkn, hSLl])
    (by simp [σ₁, hsn, hSLl]) (by simp [σ₁, hwn]) (by simp [σ₁, hvk]) (by simp [σ₁, hya])
    (by simp [σ₁, hxs]) (by simp [σ₁, hnv]) (by simp [σ₁, htK]) (by simp [σ₁, htC])
    (by simp [σ₁, hac2])
  set σ₂ := Function.update (Function.update σ₁ .sel []) .vk
    (cstream A w (Mult.BandFactor.foldList SL))
  have hready₂ : RsbReady σ₂ w P := by
    simp only [σ₂, σ₁]
    exact (((hr.update .src (fun c => by simp) _).update .sel (fun c => by simp) _).update .sel
      (fun c => by simp) _).update .vk (fun c => by simp) _
  have hfold : ∀ a ∈ Mult.BandFactor.foldList SL, Fits w a := by
    intro a ha
    have hsub : ∀ a ∈ SL, Fits w a := by
      intro a ha; simp only [hSL, rsbArr, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; exact hfN _
    exact hsub a (mem_of_mem_foldList a SL ha)
  have h₃ := band_scale_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA (x := .vk) (y := .smwn)
    (o := .ya) ⟨by decide, by decide, by decide, fun _ => ⟨by simp, by simp, by simp⟩⟩ σ₂ hready₂ hw hp
    (Mult.BandFactor.foldList SL) cin hfold hfc (by simp [σ₂]) (by simp [σ₂, σ₁, hcin])
    (by simp [σ₂, σ₁, hya])
  set sc := (Mult.BandFactor.foldList SL).map fun a => tdivN P (a * ⟨cin, 0⟩)
  set σ₃ := Function.update (Function.update σ₂ .ya (cstream A w sc)) .vk []
  have h₄ := rsb_umulSym_runs (body := body) (ι := ι) hrg (pairSym A false false) (c := .mwn) (a := .vk)
    (t := .tC) (by decide) (by decide) (by decide) σ₃ (by simp [σ₃, σ₂, σ₁, htC])
  set σ₄ := Function.update σ₃ .vk (List.replicate (σ₃ .mwn).length (pairSym A false false) ++ σ₃ .vk)
  have h₅ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ya) (b := .ac2) (by decide) σ₄
  set σ₅ := Function.update (Function.update σ₄ .ya []) .ac2 ((σ₄ .ya).reverse ++ σ₄ .ac2)
  have h₆ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .vk) (by decide) σ₅
  refine ⟨_, (RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃ (RsbRuns.seq hdisj h₄
    (RsbRuns.seq hdisj h₅ h₆))))).congr ?_⟩
  have hz : List.replicate (σ .mwn).length (pairSym A false false) = cstream A w (List.replicate B 0) := by
    rw [cstream_replicate_zero, hmwn]
  funext x; cases x <;> simp [σ₅, σ₄, σ₃, σ₂, σ₁, hya, hac2, hsel, hz, cstream_append]

end Contracts

end IntegerMultBounds.MathlibTM2.Fast
