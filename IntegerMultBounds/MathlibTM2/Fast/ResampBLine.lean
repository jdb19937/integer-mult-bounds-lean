module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBCore

/-!
# The fast `B̃₀` on one line

`rsbLineP rg hι hT hQ` maps one line of `t` grid records to the `s` records of
`Mult.FastB0.resampB₀NumK p K m (E/2^p) (D/2^p)`, followed by `t - s` zero records
(`rsb_line_runs`); `rsbLineNum_eq_numer` identifies the `s` records with the numerators of
`resampB₀NumK` at scale `2^p`.

**Formats.** A grid value `N / 2^p` is stored as `csyms A w N = coeffSyms A w (red w N)`: `w` pair
symbols, least significant first. A stream of records is `cstream A w l`, the first record on top.
Every stored value is a numerator at scale `2^p`; the tables are real (`rsbReal x = x + 0 i`).

**Registers** (`rg : RsbR → Fin T` injective, disjoint from the 64 registers `ι j` of the
Schönhage–Strassen multiplier, which are empty; all left stacks empty):
* `src`: the line `N` (`t` records) on top of any `rest`; ends holding `rest`;
* `dst`: gains `(cstream A w (rsbArr (rsbLineNum p K m E D N) ++ replicate (t - s) 0)).reverse`
  on top, so that a sequence of lines leaves the outputs reversed;
* `msk`: the row-selection mask `(rsbMask s t).map bitSymbol` (bit `j` set when
  `j = rowIndexNat s t ℓ` for some `ℓ < s`); restored;
* `ef`: `cstream A w (rsbETab s m E)`, the entries `E ℓ h` for `ℓ = 0, …, s - 1` and
  `h ∈ rsbHs m = [-m, …, -1, 1, …, m]` in increasing order;
  `df`: `cstream A w (rsbArr (rsbReal ∘ D))`; `hf`: `csyms A w (rsbReal (2^(p-1)))`, the halving
  constant; all restored;
* `kn`: `K` symbols (the number of Horner steps, in unary); `tswn`: `(t - s) w` symbols; restored;
* `RsbEnv`: the product registers `cm c` ready for width `w` and shift `p` (`cm .wn`, `cm .pn`,
  `cm .nn` hold `w`, `p`, `topN w` symbols), the counters `mwn`, `m2wn`, `m2n`, `sn`, `smwn` of
  `m w`, `2 m w`, `2 m`, `s`, `(s - m) w` symbols, and the scratch registers empty; the scratch
  registers `ms`, `sr`, `sel`, `hv`, `vk`, `dout`, `tK` are empty as well.

**Algorithm.**
1. `rsbSelP`: for each mask symbol, move one record of `src` onto `sr` (bit set) or drop it;
   then `sr` onto `sel`: the records `N (rowIndex s t ℓ)`, `ℓ = 0, …, s - 1` (`rsb_filter_mask`).
2. `rsbHalfP`: the products by the one-entry real table `hf`: `tdivN p (N · 2^(p-1)) = tdivN 1 N`
   (`rsb_tdivN_half`), the numerator of `rdV p ((1/2) • ·)`; onto `hv`.
3. `rsbCopyTo hv vk`: the first iterate.
4. `K` times `rsbStepP` (`rsb_step_runs`): three copies of the iterate `V` onto `ya`, `s - m`
   records dropped, so that `ya` holds `V` cyclically from index `-m`; `s` windows (`rsbWinBody`:
   `m` records, the centre skipped, `m` records) onto `xa`, then onto `xs`; the truncated products
   of the windows against the table `ef` (`rmulStream`) onto `pr`; for each `ℓ`, the record
   `H ℓ` minus its `2m` products (`rsbGrpBody`, the subtraction automaton of `Layer/GaussStream`)
   onto `nv`; `nv` onto `vk`. This is `V ← H - Ẽ V` (`rsbStep`, `rsb_products`).
5. The diagonal: the truncated products of the iterate against `df` onto `dout`.
6. `dout` onto `dst`, then `(t - s) w` zero pair symbols onto `dst`.

**Fits.** A product is computed exactly when both factors fit `w` bits (`Fits`): the line
entries, the table entries, and the iterates `rsbIter p m E (rsbHalf N) k`, `k ≤ K`, are
hypotheses of `rsb_line_runs` (`rsbLineOk_of_ball` and `rsb_pipe_lineOk` derive them from
unit-disk bounds). Sums and differences are exact modulo `2^w`.

**Cost** (`rsbLineCost T w s t m K`):
`K (rsbStepCost T w s m + 6) + 2 s (rmulCost T w + 16 w + 16) + 32 t w + 16 t + 64` steps, with
`rsbStepCost T w s m = 2 m s (rmulCost T w + 64 w + 64) + 64 s w + 64 s + 128`; for `m ≥ 1` at most
`(K s 2m + 2s) (rmulCost T w + 96 w + 96) + 32 t w + 16 t + 134 K + 64` (`rsbLineCost_le`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.NLogN (rowIndex)

set_option linter.unusedSimpArgs false

noncomputable section

/-! ### Coefficient streams -/

section Streams

variable {A w : ℕ}

@[simp] lemma length_csyms (x : GaussianInt) : (csyms A w x).length = w := by simp [csyms]

lemma drop_csyms_append (x : GaussianInt) (L : List (Fin (A + 4))) :
    (csyms A w x ++ L).drop w = L := by
  rw [List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp)]; simp

lemma take_csyms_append (x : GaussianInt) (L : List (Fin (A + 4))) :
    (csyms A w x ++ L).take w = csyms A w x := by
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

lemma drop_cstream (l : List GaussianInt) (j : ℕ) (L : List (Fin (A + 4))) :
    (cstream A w l ++ L).drop (j * w) =
      cstream A w (l.drop j) ++ (L.drop ((j - l.length) * w)) := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [cstream_cons, List.append_assoc, Nat.succ_mul, Nat.add_comm (j * w) w,
        ← List.drop_drop, drop_csyms_append, ih]
      simp

lemma take_cstream (l : List GaussianInt) (j : ℕ) (hj : j ≤ l.length) (L : List (Fin (A + 4))) :
    (cstream A w l ++ L).take (j * w) = cstream A w (l.take j) := by
  induction l generalizing j with
  | nil => simp at hj; subst hj; simp
  | cons x l ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [cstream_cons, List.append_assoc, Nat.succ_mul, Nat.add_comm (j * w) w,
        List.take_add, take_csyms_append, drop_csyms_append, ih j (by simpa using hj)]
      simp [cstream_cons]

lemma take_cstream' (l : List GaussianInt) (k : ℕ) :
    (cstream A w l).take (k * w) = cstream A w (l.take k) := by
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [cstream_cons, Nat.succ_mul, Nat.add_comm (k * w) w, List.take_add, take_csyms_append,
        drop_csyms_append, ih]
      simp

lemma drop_cstream' (l : List GaussianInt) (k : ℕ) :
    (cstream A w l).drop (k * w) = cstream A w (l.drop k) := by
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [cstream_cons, Nat.succ_mul, Nat.add_comm (k * w) w, ← List.drop_drop,
        drop_csyms_append, ih]
      simp

lemma take_cstream_one (l : List GaussianInt) :
    (cstream A w l).take w = cstream A w (l.take 1) := by
  simpa using take_cstream' (A := A) (w := w) l 1

lemma drop_cstream_one (l : List GaussianInt) :
    (cstream A w l).drop w = cstream A w (l.drop 1) := by
  simpa using drop_cstream' (A := A) (w := w) l 1

lemma reverse_cstream_append (l l' : List GaussianInt) :
    (cstream A w (l ++ l')).reverse = (cstream A w l').reverse ++ (cstream A w l).reverse := by
  rw [cstream_append, List.reverse_append]

lemma cstream_drop_eq_cons (l : List GaussianInt) (j : ℕ) (hj : j < l.length) :
    cstream A w (l.drop j) = csyms A w l[j] ++ cstream A w (l.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hj, cstream_cons]

lemma reverse_cstream_snoc (l : List GaussianInt) (x : GaussianInt) :
    (cstream A w (l ++ [x])).reverse = (csyms A w x).reverse ++ (cstream A w l).reverse := by
  rw [cstream_append, List.reverse_append]; simp [cstream]

end Streams

/-! ### Row selection -/

section Select

/-- The entries of `ln` selected by the first `j` mask bits, in order. -/
def rsbSel (ln : List GaussianInt) (mask : List Bool) (j : ℕ) : List GaussianInt :=
  (((ln.zip mask).take j).filter (·.2)).map (·.1)

lemma rsbSel_zero (ln : List GaussianInt) (mask : List Bool) : rsbSel ln mask 0 = [] := by
  simp [rsbSel]

lemma rsbSel_succ (ln : List GaussianInt) (mask : List Bool) (j : ℕ) (h1 : j < ln.length)
    (h2 : j < mask.length) :
    rsbSel ln mask (j + 1) =
      rsbSel ln mask j ++ (if mask[j] then [ln[j]] else []) := by
  have hz : j < (ln.zip mask).length := by simp [h1, h2]
  rw [rsbSel, rsbSel, List.take_succ, List.getElem?_eq_getElem hz, Option.toList_some,
    List.filter_append, List.map_append]
  congr 1
  simp only [List.getElem_zip]
  by_cases hm : mask[j] <;> simp [hm]

lemma length_rsbSel_le (ln : List GaussianInt) (mask : List Bool) (j : ℕ) :
    (rsbSel ln mask j).length ≤ j := by
  unfold rsbSel
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- The symbol of a mask bit. -/
lemma rsb_isOne_bitSymbol {A : ℕ} (b : Bool) :
    decide ((bitSymbol b : Fin (A + 4)) = bitSymbol true) = b := by
  cases b <;> simp [bitSymbol, Fin.ext_iff]

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- Row selection on registers: for each mask symbol, move one record from `src` onto `sr` if the
symbol is `bitSymbol true`, else drop one record; then move `sr` onto `sel`. -/
def rsbSelP (rg : RsbR → Fin T) : Pr P T Q A U :=
  .seq (rsbScanIf (rg .msk) (rg .ms) (fun x => decide (x = bitSymbol true))
      (rsbMv (rg (.cm .wn)) (rg .tC) (rg .src) (rg .sr)) (usub (rg (.cm .wn)) (rg .src) (rg .tC)))
    (moveR (rg .sr) (rg .sel) id)

variable {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_sel_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w : ℕ}
    (ρ : RsbR → List (Fin (A + 4))) (mask : List Bool) (ln : List GaussianInt)
    (rest : List (Fin (A + 4))) (hlen : ln.length = mask.length)
    (hmsk : ρ .msk = mask.map bitSymbol) (hms : ρ .ms = []) (hsrc : ρ .src = cstream A w ln ++ rest)
    (hsr : ρ .sr = []) (hsel : ρ .sel = []) (htC : ρ .tC = []) (hwn : (ρ (.cm .wn)).length = w) :
    RsbRuns body rg ι (rsbSelP rg) ρ
      (Function.update (Function.update ρ .src rest) .sel
        (cstream A w (rsbSel ln mask mask.length)))
      (mask.length * (6 * w + 10) + 6) := by
  set Ψ : ℕ → RsbR → List (Fin (A + 4)) := fun j =>
    Function.update (Function.update ρ .src (cstream A w (ln.drop j) ++ rest)) .sr
      (cstream A w (rsbSel ln mask j)).reverse with hΨ
  have hbody : ∀ j (hj : j < (mask.map bitSymbol).length) X Y,
      RsbRuns body rg ι (if (fun x : Fin (A + 4) => decide (x = bitSymbol true))
          (mask.map bitSymbol)[j] then rsbMv (rg (.cm .wn)) (rg .tC) (rg .src) (rg .sr)
          else usub (rg (.cm .wn)) (rg .src) (rg .tC))
        (rsbUpd2 (Ψ j) .msk X .ms Y) (rsbUpd2 (Ψ (j + 1)) .msk X .ms Y) (4 * w + 4) := by
    intro j hj X Y
    have hjm : j < mask.length := by simpa using hj
    have hjl : j < ln.length := by omega
    have hsrcj : rsbUpd2 (Ψ j) .msk X .ms Y .src =
        csyms A w ln[j] ++ (cstream A w (ln.drop (j + 1)) ++ rest) := by
      simp [hΨ, cstream_drop_eq_cons ln j hjl]
    simp only [List.getElem_map, rsb_isOne_bitSymbol]
    by_cases hm : mask[j]
    · rw [if_pos hm]
      refine ((rsb_mv_runs hrg (c := .cm .wn) (t := .tC) (x := .src) (y := .sr) (by decide) _
        (by simp [hΨ, htC]) (by rw [hsrcj]; simp [hΨ, hwn])).congr ?_).mono (by simp [hΨ, hwn])
      rw [hsrcj]
      funext r
      cases r <;> simp [hΨ, hwn, drop_csyms_append, take_csyms_append,
        rsbSel_succ ln mask j hjl hjm,
        hm, reverse_cstream_snoc]
    · rw [if_neg hm]
      refine ((rsb_usub_runs hrg (c := .cm .wn) (a := .src) (t := .tC) (by decide) (by decide)
        (by decide) _ (by simp [hΨ, htC])).congr ?_).mono (by simp [hΨ, hwn])
      rw [hsrcj]
      funext r
      cases r <;> simp [hΨ, hwn, drop_csyms_append, rsbSel_succ ln mask j hjl hjm, hm]
  have h₁ := rsb_scanIf_runs (body := body) hrg hdisj (ra := .msk) (rt := .ms) (by decide)
    (fun x : Fin (A + 4) => decide (x = bitSymbol true))
    (rsbMv (rg (.cm .wn)) (rg .tC) (rg .src) (rg .sr)) (usub (rg (.cm .wn)) (rg .src) (rg .tC))
    (mask.map bitSymbol) Ψ (fun _ => 4 * w + 4) hbody
  have e₀ : rsbUpd2 (Ψ 0) .msk (mask.map bitSymbol) .ms [] = ρ := by
    funext r; cases r <;> simp [hΨ, rsbSel_zero, hmsk, hms, hsrc, hsr]
  rw [e₀, List.length_map] at h₁
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .sr) (b := .sel) (by decide)
    (rsbUpd2 (Ψ mask.length) .msk (mask.map bitSymbol) .ms [])
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono ?_
  · funext r
    cases r <;> simp [hΨ, hmsk, hms, hsel, hsr, List.drop_of_length_le (le_of_eq hlen)]
  · have hsl := length_rsbSel_le ln mask mask.length
    have hsl' := Nat.mul_le_mul_right w hsl
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, rsbUpd2, hΨ,
      Function.update_self, List.length_reverse, length_cstream]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, List.length_reverse, length_cstream]
    nlinarith

end Select

/-! ### Halving and the first iterate -/

section Half

/-- `2^(p-1) / 2^p = 1/2`: the truncated product by the real coefficient `2^(p-1)` halves. -/
lemma rsb_tdivN_half (p : ℕ) (hp : 1 ≤ p) (a : GaussianInt) :
    tdivN p (a * rsbReal (2 ^ (p - 1))) = tdivN 1 a := by
  have e : (2 : ℤ) ^ p = 2 ^ (p - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hpos : (0 : ℤ) < 2 ^ (p - 1) := by positivity
  ext <;> simp [tdivN, rsbReal, e, mul_comm _ ((2 : ℤ) ^ (p - 1)), Int.mul_tdiv_mul_of_pos _ _ hpos]

lemma tableOut_single (g : GaussianInt → GaussianInt → GaussianInt) (l : List GaussianInt)
    (c : GaussianInt) : tableOut g (l.map fun a => [a]) [c] = l.map fun a => g a c := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [tableOut] at ih ⊢; exact ih

lemma flatten_singletons {α : Type*} (l : List α) : (l.map fun a => [a]).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- `Fits` for the halving constant `2^(p-1)`. -/
lemma fits_half {w p : ℕ} (hp : 1 ≤ p) (hpw : p < w) : Fits w (rsbReal (2 ^ (p - 1))) := by
  refine ⟨?_, ?_⟩
  · simp only [rsbReal]
    rw [abs_of_pos (by positivity)]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  · simp [rsbReal]

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- The registers of a product call. -/
abbrev rsbCr (rg : RsbR → Fin T) (x y o : RsbR) : CR → Fin T := fun c => rg (rsbRemap x y o c)

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

/-- Halve the selected records against the one-entry table `hf = 2^(p-1)`, onto `hv`. -/
def rsbHalfP : Pr P T Q A U :=
  .seq (cmulTable (rsbCr rg .sel .hf .hv) (rmulOne ι hι hT hQ (rsbCr rg .sel .hf .hv)))
    (emptyR (rg .sel))

variable {body : P → Pr P T Q A U} {rg}

lemma rsbFree_sel : RsbFree .sel .hf .hv := ⟨by decide, by decide, by decide, fun _ => ⟨by simp,
  by simp, by simp⟩⟩

theorem rsb_half_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ A)
    {w p : ℕ} (hp : 1 ≤ p) (hpw : p < w) (σ : RsbR → List (Fin (A + 4))) (hr : RsbReady σ w p)
    (xs : List GaussianInt) (hfx : ∀ a ∈ xs, Fits w a) (hsel : σ .sel = cstream A w xs)
    (hhf : σ .hf = csyms A w (rsbReal (2 ^ (p - 1)))) (hhv : σ .hv = []) :
    RsbRuns body rg ι (rsbHalfP rg hι hT hQ) σ
      (Function.update (Function.update σ .hv (cstream A w (xs.map (tdivN 1)))) .sel [])
      (xs.length * (rmulCost T w + 8 * w + 8) + 8) := by
  have H := rsb_rmulTable_runs (body := body) hrg hdisj hι hT hQ hA rsbFree_sel hr (by omega)
    (by omega) (xs.map fun a => [a]) [rsbReal (2 ^ (p - 1))] (by simp) (by simp)
    (by rwa [flatten_singletons])
    (by intro a ha; simp only [List.mem_singleton] at ha; subst ha; exact ⟨fits_half hp hpw, rfl⟩)
    (by rw [flatten_singletons, hsel]) (by rw [hhf]; simp [cstream])
  rw [tableOut_single, flatten_singletons] at H
  have H2 := rsb_emptyR_runs (body := body) (ι := ι) hrg .sel (Function.update σ .hv
    (cstream A w (xs.map fun a => tdivN p (a * rsbReal (2 ^ (p - 1)))) ++ σ .hv))
  refine ((RsbRuns.seq hdisj H H2).congr ?_).mono ?_
  · funext r
    cases r <;> simp [hhv, rsb_tdivN_half p hp]
  · simp [hsel]
    nlinarith

end Half

/-! ### Windows -/

section Windows

/-- The window of offsets `-m … -1, 1 … m` around position `m` of `Z`. -/
def rsbWinOf {α : Type*} (m : ℕ) (Z : List α) : List α :=
  Z.take m ++ (Z.drop (m + 1)).take m

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- One window: copy `m` records of `ya` onto `xa` (keeping them on `tb`), keep the centre on
`tb`, copy `m` more, move `2m` records back onto `ya`, drop the first record. -/
def rsbWinBody (rg : RsbR → Fin T) : Pr P T Q A U :=
  .seq (rsbMv2 (rg .mwn) (rg .tC) (rg .ya) (rg .tb) (rg .xa))
    (.seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg .ya) (rg .tb))
      (.seq (rsbMv2 (rg .mwn) (rg .tC) (rg .ya) (rg .tb) (rg .xa))
        (.seq (rsbMv (rg .m2wn) (rg .tC) (rg .tb) (rg .ya)) (emptyR (rg .tb)))))

variable {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_winBody_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w m : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (Z : List GaussianInt) (hZ : 2 * m + 1 ≤ Z.length)
    (Xacc : List (Fin (A + 4))) (hya : σ .ya = cstream A w Z) (htb : σ .tb = [])
    (hxa : σ .xa = Xacc) (htC : σ .tC = []) (hwn : (σ (.cm .wn)).length = w)
    (hmwn : (σ .mwn).length = m * w) (hm2wn : (σ .m2wn).length = 2 * m * w) :
    RsbRuns body rg ι (rsbWinBody rg) σ
      (Function.update (Function.update σ .ya (cstream A w (Z.drop 1))) .xa
        ((cstream A w (rsbWinOf m Z)).reverse ++ Xacc)) (16 * (m * w) + 6 * w + 18) := by
  -- step 1: `m` records onto `tb` and `xa`
  have h₁ := rsb_mv2_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .ya) (y := .tb)
    (z := .xa) (by decide) σ htC (by rw [hmwn, hya]; simp; nlinarith)
  rw [hmwn, hya, take_cstream', drop_cstream', htb, hxa, List.append_nil] at h₁
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : RsbR → List (Fin (A + 4)), σ₁ = Function.update (Function.update
      (Function.update σ .ya (cstream A w (Z.drop m))) .tb (cstream A w (Z.take m)).reverse) .xa
      ((cstream A w (Z.take m)).reverse ++ Xacc) := ⟨_, rfl⟩
  rw [← hσ₁] at h₁
  -- step 2: the centre onto `tb`
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .ya)
    (y := .tb) (by decide) σ₁ (by simp [hσ₁, htC])
    (by simp [hσ₁, hwn]; exact Nat.le_mul_of_pos_left w (by omega))
  have e₂ : σ₁ (.cm .wn) = σ (.cm .wn) := by simp [hσ₁]
  have e₂' : σ₁ .ya = cstream A w (Z.drop m) := by simp [hσ₁]
  have e₂'' : σ₁ .tb = (cstream A w (Z.take m)).reverse := by simp [hσ₁]
  rw [e₂, hwn, e₂', e₂''] at h₂
  rw [take_cstream_one, drop_cstream_one] at h₂
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂ : RsbR → List (Fin (A + 4)), σ₂ = Function.update
      (Function.update σ₁ .ya (cstream A w (Z.drop (m + 1)))) .tb
      (cstream A w (Z.take (m + 1))).reverse := ⟨_, rfl⟩
  have hσ₂' : Function.update (Function.update σ₁ .ya (cstream A w ((Z.drop m).drop 1)))
      .tb ((cstream A w ((Z.drop m).take 1)).reverse ++ (cstream A w (Z.take m)).reverse) = σ₂ := by
    rw [hσ₂, List.drop_drop, ← reverse_cstream_append, ← List.take_add]
  rw [hσ₂'] at h₂
  -- step 3: `m` more records onto `tb` and `xa`
  have h₃ := rsb_mv2_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .ya) (y := .tb)
    (z := .xa) (by decide) σ₂ (by simp [hσ₂, hσ₁, htC])
    (by simp [hσ₂, hσ₁, hmwn]; exact Nat.mul_le_mul_right w (by omega))
  have e₃ : (σ₂ .mwn).length = m * w := by simp [hσ₂, hσ₁, hmwn]
  have e₃' : σ₂ .ya = cstream A w (Z.drop (m + 1)) := by simp [hσ₂]
  have e₃'' : σ₂ .tb = (cstream A w (Z.take (m + 1))).reverse := by simp [hσ₂]
  have e₃x : σ₂ .xa = (cstream A w (Z.take m)).reverse ++ Xacc := by simp [hσ₂, hσ₁]
  rw [e₃, e₃', e₃'', e₃x, take_cstream', drop_cstream'] at h₃
  obtain ⟨σ₃, hσ₃⟩ : ∃ σ₃ : RsbR → List (Fin (A + 4)), σ₃ = Function.update (Function.update
      (Function.update σ₂ .ya (cstream A w (Z.drop (2 * m + 1)))) .tb
      ((cstream A w ((Z.drop 1).take (2 * m))).reverse ++ (cstream A w (Z.take 1)).reverse)) .xa
      ((cstream A w (rsbWinOf m Z)).reverse ++ Xacc) := ⟨_, rfl⟩
  have hσ₃' : Function.update (Function.update (Function.update σ₂ .ya
      (cstream A w ((Z.drop (m + 1)).drop m))) .tb
      ((cstream A w ((Z.drop (m + 1)).take m)).reverse ++ (cstream A w (Z.take (m + 1))).reverse))
      .xa ((cstream A w ((Z.drop (m + 1)).take m)).reverse ++
        ((cstream A w (Z.take m)).reverse ++ Xacc)) = σ₃ := by
    have e1 : (Z.drop (m + 1)).drop m = Z.drop (2 * m + 1) := by
      rw [List.drop_drop]; congr 1; omega
    have e2 : (cstream A w ((Z.drop (m + 1)).take m)).reverse ++
        (cstream A w (Z.take (m + 1))).reverse =
        (cstream A w ((Z.drop 1).take (2 * m))).reverse ++ (cstream A w (Z.take 1)).reverse := by
      rw [← reverse_cstream_append, ← reverse_cstream_append, ← List.take_add, ← List.take_add]
      congr 3; omega
    have e3 : (cstream A w ((Z.drop (m + 1)).take m)).reverse ++
        ((cstream A w (Z.take m)).reverse ++ Xacc) =
        (cstream A w (rsbWinOf m Z)).reverse ++ Xacc := by
      rw [← List.append_assoc, ← reverse_cstream_append, rsbWinOf]
    rw [hσ₃, e1, e2, e3]
  rw [hσ₃'] at h₃
  -- step 4: `2m` records back onto `ya`
  have hlenb : ((Z.drop 1).take (2 * m)).length = 2 * m := by simp; omega
  have e₄' : σ₃ .tb = (cstream A w ((Z.drop 1).take (2 * m))).reverse ++
      (cstream A w (Z.take 1)).reverse := by simp [hσ₃]
  have h₄ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .m2wn) (t := .tC) (x := .tb) (y := .ya)
    (by decide) σ₃ (by simp [hσ₃, hσ₂, hσ₁, htC])
    (by
      rw [e₄']
      simp only [List.length_append, List.length_reverse, length_cstream, hlenb]
      have : (σ₃ .m2wn).length = 2 * m * w := by simp [hσ₃, hσ₂, hσ₁, hm2wn]
      rw [this]; exact Nat.le_add_right _ _)
  have e₄ : (σ₃ .m2wn).length = 2 * m * w := by simp [hσ₃, hσ₂, hσ₁, hm2wn]
  have e₄'' : σ₃ .ya = cstream A w (Z.drop (2 * m + 1)) := by simp [hσ₃]
  have htk : (2 * m * w) = ((cstream A w ((Z.drop 1).take (2 * m))).reverse).length := by
    simp only [List.length_reverse, length_cstream, hlenb]
  rw [e₄, e₄', e₄'', htk, List.take_left, List.drop_left, List.reverse_reverse] at h₄
  -- step 5: drop the first record
  have h₅ := rsb_emptyR_runs (body := body) (ι := ι) hrg .tb
    (Function.update (Function.update σ₃ .tb (cstream A w (Z.take 1)).reverse) .ya
      (cstream A w ((Z.drop 1).take (2 * m)) ++ cstream A w (Z.drop (2 * m + 1))))
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ h₅)))).congr ?_).mono ?_
  · have hy : cstream A w ((Z.drop 1).take (2 * m)) ++ cstream A w (Z.drop (2 * m + 1)) =
        cstream A w (Z.drop 1) := by
      rw [← cstream_append, show 2 * m + 1 = 1 + 2 * m by ring, ← List.drop_drop,
        List.take_append_drop]
    rw [hy]
    funext r
    cases r <;> simp [hσ₃, hσ₂, hσ₁, htb]
  · have hm1 : min (2 * m) (Z.length - 1) = 2 * m := by omega
    have hm2 : min 1 Z.length = 1 := by omega
    simp [hσ₃, hσ₂, hσ₁, hwn, hmwn, hm2wn, hlenb, hm1, hm2]; nlinarith

/-- The window phase on `ya` holding `Y`: `s` windows onto `xa` (reversed), `ya` advanced by
`s` records. -/
theorem rsb_winLoop_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w m s : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (Y : List GaussianInt) (hY : s + 2 * m ≤ Y.length)
    (hya : σ .ya = cstream A w Y) (htb : σ .tb = []) (hxa : σ .xa = []) (htC : σ .tC = [])
    (htL : σ .tL = []) (hsn : (σ .sn).length = s) (hwn : (σ (.cm .wn)).length = w)
    (hmwn : (σ .mwn).length = m * w) (hm2wn : (σ .m2wn).length = 2 * m * w) :
    RsbRuns body rg ι (rsbRep (rg .sn) (rg .tL) (rsbWinBody rg)) σ
      (Function.update (Function.update σ .ya (cstream A w (Y.drop s))) .xa
        (cstream A w ((List.range s).flatMap fun ℓ => rsbWinOf m (Y.drop ℓ))).reverse)
      (s * (16 * (m * w) + 6 * w + 24) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update σ .ya (cstream A w (Y.drop j))) .xa
        (cstream A w ((List.range j).flatMap fun ℓ => rsbWinOf m (Y.drop ℓ))).reverse := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y', RsbRuns body rg ι (rsbWinBody rg)
      (rsbUpd2 (Ψ j) .sn X .tL Y') (rsbUpd2 (Ψ (j + 1)) .sn X .tL Y')
      (16 * (m * w) + 6 * w + 18) := by
    intro j hj X Y'
    rw [hsn] at hj
    refine (rsb_winBody_runs hrg hdisj _ (Y.drop j) (by simp; omega) _ (by simp [hΨ])
      (by simp [hΨ, htb]) rfl (by simp [hΨ, htC]) (by simp [hΨ, hwn]) (by simp [hΨ, hmwn])
      (by simp [hΨ, hm2wn])).congr ?_
    funext r
    cases r <;> simp [hΨ, List.drop_drop, List.range_succ, List.flatMap_append,
      reverse_cstream_append, Nat.add_comm 1 j]
  have H := rsb_rep_runs hrg hdisj (ra := .sn) (rt := .tL) (by decide) (rsbWinBody rg) (σ .sn) Ψ _
    hbody
  have e₀ : rsbUpd2 (Ψ 0) .sn (σ .sn) .tL [] = σ := by
    funext r; cases r <;> simp [hΨ, hya, hxa, htL]
  rw [e₀, hsn] at H
  refine (H.congr ?_).mono (by nlinarith)
  funext r; cases r <;> simp [hΨ, htL]

end Windows

/-! ### Cyclic windows as offsets -/

section Cyclic

variable {s : ℕ}

lemma rsb_cast_sub_self {n : ℕ} (h : s ≤ n) : (((n - s : ℕ) : ZMod s)) = (n : ZMod s) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, sub_zero]

lemma rsbArr_getElem {α : Type*} (V : ZMod s → α) (n : ℕ) (hn : n < (rsbArr V).length) :
    (rsbArr V)[n] = V (n : ZMod s) := by
  simp [rsbArr]

lemma rsb_arr3_getElem {α : Type*} (V : ZMod s → α) (n : ℕ)
    (hn : n < (rsbArr V ++ rsbArr V ++ rsbArr V).length) :
    (rsbArr V ++ rsbArr V ++ rsbArr V)[n] = V (n : ZMod s) := by
  have hl := length_rsbArr V
  simp only [List.length_append, hl] at hn
  by_cases h1 : n < s
  · rw [List.getElem_append_left (by simp [hl]; omega),
      List.getElem_append_left (by simp [hl]; omega),
      rsbArr_getElem]
  by_cases h2 : n < 2 * s
  · rw [List.getElem_append_left (by simp [hl]; omega),
      List.getElem_append_right (by simp [hl]; omega),
      rsbArr_getElem]
    simp only [hl]
    rw [rsb_cast_sub_self (by omega)]
  · rw [List.getElem_append_right (by simp [hl]; omega), rsbArr_getElem]
    simp only [List.length_append, hl]
    rw [show n - (s + s) = (n - s) - s by omega, rsb_cast_sub_self (by omega),
      rsb_cast_sub_self (by omega)]

lemma rsb_cast_window (m ℓ i : ℕ) (hm : m ≤ s) :
    ((s - m + ℓ + i : ℕ) : ZMod s) = (ℓ : ZMod s) + ((((i : ℤ) - m : ℤ)) : ZMod s) := by
  have : ((s - m + ℓ + i : ℕ) : ℤ) = s + (ℓ + ((i : ℤ) - m)) := by push_cast [Nat.cast_sub hm]; ring
  rw [← Int.cast_natCast, this]
  push_cast
  rw [ZMod.natCast_self]; ring

/-- The windows of the tripled array, from position `s - m`, are the cyclic windows. -/
theorem rsb_windows {α : Type*} (V : ZMod s → α) {m : ℕ} (hm : m ≤ s) (ℓ : ℕ) (hℓ : ℓ < s) :
    (((rsbArr V ++ rsbArr V ++ rsbArr V).drop (s - m)).drop ℓ).take m ++
        ((((rsbArr V ++ rsbArr V ++ rsbArr V).drop (s - m)).drop ℓ).drop (m + 1)).take m =
      (rsbHs m).map fun h : ℤ => V ((ℓ : ZMod s) + (h : ZMod s)) := by
  have hlen : (rsbArr V ++ rsbArr V ++ rsbArr V).length = 3 * s := by
    simp [length_rsbArr]; ring
  rw [rsbHs, List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.ext_getElem (by simp [length_rsbArr]; omega)
    intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      Function.comp_apply]
    rw [rsb_arr3_getElem, show s - m + (ℓ + i) = s - m + ℓ + i by ring, rsb_cast_window m ℓ i hm]
  · apply List.ext_getElem (by simp [length_rsbArr]; omega)
    intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      Function.comp_apply]
    rw [rsb_arr3_getElem, show s - m + (ℓ + (m + 1 + i)) = s - m + ℓ + (m + 1 + i) by ring,
      rsb_cast_window m ℓ (m + 1 + i) hm]
    congr 2
    push_cast; ring

end Cyclic

lemma rsb_zipWith_flatMap {α β γ δ : Type*} (f : α → β → γ) (l : List δ) (a : δ → List α)
    (b : δ → List β) (h : ∀ x ∈ l, (a x).length = (b x).length) :
    List.zipWith f (l.flatMap a) (l.flatMap b) = l.flatMap fun x => List.zipWith f (a x) (b x) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [List.zipWith_append (h x (by simp)), ih (fun y hy => h y (by simp [hy]))]

lemma rsb_zipWith_map {α β γ δ : Type*} (f : α → β → γ) (l : List δ) (a : δ → α) (b : δ → β) :
    List.zipWith f (l.map a) (l.map b) = l.map fun x => f (a x) (b x) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- The off-diagonal weight table: for `ℓ = 0, …, s - 1` the real entries `E ℓ h`, `h` over
`rsbHs m`. -/
def rsbETab (s m : ℕ) (E : ZMod s → ℤ → ℤ) : List GaussianInt :=
  (List.range s).flatMap fun ℓ : ℕ => (rsbHs m).map fun h : ℤ => rsbReal (E (ℓ : ZMod s) h)

/-- The truncated products of one window. -/
def rsbBlk {s : ℕ} (p m : ℕ) (E : ZMod s → ℤ → ℤ) (V : ZMod s → GaussianInt) (ℓ : ℕ) :
    List GaussianInt :=
  (rsbHs m).map fun h : ℤ =>
    tdivN p (V ((ℓ : ZMod s) + (h : ZMod s)) * rsbReal (E (ℓ : ZMod s) h))

lemma length_rsbBlk {s : ℕ} (p m : ℕ) (E : ZMod s → ℤ → ℤ) (V : ZMod s → GaussianInt) (ℓ : ℕ) :
    (rsbBlk p m E V ℓ).length = 2 * m := by
  simp [rsbBlk, length_rsbHs]

/-- The product stream of one Horner step. -/
theorem rsb_products {s : ℕ} [NeZero s] (p : ℕ) {m : ℕ} (hm : m ≤ s) (E : ZMod s → ℤ → ℤ)
    (V : ZMod s → GaussianInt) :
    List.zipWith (fun a b => tdivN p (a * b))
        ((List.range s).flatMap fun ℓ => rsbWinOf m
          (((rsbArr V ++ rsbArr V ++ rsbArr V).drop (s - m)).drop ℓ)) (rsbETab s m E) =
      (List.range s).flatMap (rsbBlk p m E V) := by
  have hw : ∀ ℓ ∈ List.range s, rsbWinOf m
      (((rsbArr V ++ rsbArr V ++ rsbArr V).drop (s - m)).drop ℓ) =
      (rsbHs m).map fun h : ℤ => V ((ℓ : ZMod s) + (h : ZMod s)) := fun ℓ hℓ =>
    rsb_windows V hm ℓ (List.mem_range.mp hℓ)
  rw [List.flatMap_congr hw, rsbETab, rsb_zipWith_flatMap _ _ _ _ (fun x _ => by simp)]
  apply List.flatMap_congr
  intro ℓ _
  rw [rsb_zipWith_map]
  rfl

/-- One Horner step from the product blocks. -/
lemma rsbStep_blk {s : ℕ} [NeZero s] (p m : ℕ) (E : ZMod s → ℤ → ℤ) (H V : ZMod s → GaussianInt)
    (ℓ : ℕ) : rsbStep p m E H V (ℓ : ZMod s) = H (ℓ : ZMod s) - (rsbBlk p m E V ℓ).sum := rfl

/-! ### Window sums -/

section Sums

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- Subtract the record on top of `pr` from the record on `ac`. -/
def rsbSubBody (rg : RsbR → Fin T) : Pr P T Q A U :=
  .seq (rsbSubWord (rg .ac) (rg .pr) (rg .ac2) (rg (.cm .wn)) (rg .tA))
    (moveR (rg .ac2) (rg .ac) id)

/-- One output of a Horner step: take the next record of `hc`, subtract `2m` records of `pr`,
push the result onto `nv`. -/
def rsbGrpBody (rg : RsbR → Fin T) : Pr P T Q A U :=
  .seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg .hc) (rg .ac2))
    (.seq (moveR (rg .ac2) (rg .ac) id)
      (.seq (rsbRep (rg .m2n) (rg .tJ) (rsbSubBody rg)) (moveR (rg .ac) (rg .nv) id)))

variable {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_subBody_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ A)
    {w : ℕ} (σ : RsbR → List (Fin (A + 4))) (x y : GaussianInt) (PR : List (Fin (A + 4)))
    (hac : σ .ac = csyms A w x) (hpr : σ .pr = csyms A w y ++ PR) (hac2 : σ .ac2 = [])
    (htA : σ .tA = []) (hwn : (σ (.cm .wn)).length = w) :
    RsbRuns body rg ι (rsbSubBody rg) σ
      (Function.update (Function.update σ .ac (csyms A w (x - y))) .pr PR) (7 * w + 8) := by
  have h₁ := rsb_subWord_runs (body := body) (ι := ι) hrg hA (a := .ac) (b := .pr) (o := .ac2)
    (ctr := .cm .wn) (tmp := .tA) (by decide) σ x y [] PR (by rw [hac, List.append_nil]) hpr hwn
    htA
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .ac) (by decide)
    (Function.update (Function.update (Function.update σ .ac []) .pr PR) .ac2
      ((csyms A w (x - y)).reverse ++ σ .ac2))
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono ?_
  · funext r; cases r <;> simp [hac2]
  · simp [hac2]; omega

theorem rsb_grpBody_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ A)
    {w m : ℕ} (σ : RsbR → List (Fin (A + 4))) (h : GaussianInt) (blk : List GaussianInt)
    (hblk : blk.length = 2 * m) (HC PR NV : List (Fin (A + 4)))
    (hhc : σ .hc = csyms A w h ++ HC) (hpr : σ .pr = cstream A w blk ++ PR) (hnv : σ .nv = NV)
    (hac : σ .ac = []) (hac2 : σ .ac2 = []) (htC : σ .tC = []) (htA : σ .tA = [])
    (htJ : σ .tJ = []) (hwn : (σ (.cm .wn)).length = w) (hm2n : (σ .m2n).length = 2 * m) :
    RsbRuns body rg ι (rsbGrpBody rg) σ
      (Function.update (Function.update (Function.update σ .hc HC) .pr PR) .nv
        ((csyms A w (h - blk.sum)).reverse ++ NV)) (8 * w + 12 + 2 * m * (7 * w + 14)) := by
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .hc)
    (y := .ac2) (by decide) σ htC (by rw [hwn, hhc]; simp)
  rw [hwn, hhc, take_csyms_append, drop_csyms_append, hac2, List.append_nil] at h₁
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .ac) (by decide)
    (Function.update (Function.update σ .hc HC) .ac2 (csyms A w h).reverse)
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂ : RsbR → List (Fin (A + 4)),
      σ₂ = Function.update σ .hc HC := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update σ₂ .ac (csyms A w (h - (blk.take j).sum))) .pr
        (cstream A w (blk.drop j) ++ PR) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .m2n).length, ∀ X Y, RsbRuns body rg ι (rsbSubBody rg)
      (rsbUpd2 (Ψ j) .m2n X .tJ Y) (rsbUpd2 (Ψ (j + 1)) .m2n X .tJ Y) (7 * w + 8) := by
    intro j hj X Y
    rw [hm2n] at hj
    have hjb : j < blk.length := by omega
    refine (rsb_subBody_runs hrg hdisj hA _ (h - (blk.take j).sum) blk[j]
      (cstream A w (blk.drop (j + 1)) ++ PR) (by simp [hΨ])
      (by simp [hΨ, cstream_drop_eq_cons blk j hjb]) (by simp [hΨ, hσ₂, hac2])
      (by simp [hΨ, hσ₂, htA]) (by simp [hΨ, hσ₂, hwn])).congr ?_
    funext r; cases r <;> simp [hΨ, List.sum_take_succ _ _ hjb, sub_add_eq_sub_sub]
  have h₃ := rsb_rep_runs hrg hdisj (ra := .m2n) (rt := .tJ) (by decide) (rsbSubBody rg)
    (σ .m2n) Ψ _ hbody
  have e₁₂ : Function.update (Function.update (Function.update (Function.update σ .hc HC) .ac2
      (csyms A w h).reverse) .ac2 []) .ac
      ((Function.update (Function.update σ .hc HC) .ac2 (csyms A w h).reverse .ac2).reverse ++
        Function.update (Function.update σ .hc HC) .ac2 (csyms A w h).reverse .ac) =
      rsbUpd2 (Ψ 0) .m2n (σ .m2n) .tJ [] := by
    funext r; cases r <;> simp [hΨ, hσ₂, hac, hac2, hpr, htJ]
  have h₂' := h₂.congr e₁₂
  have h₄ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac) (b := .nv) (by decide)
    (rsbUpd2 (Ψ (σ .m2n).length) .m2n (σ .m2n) .tJ [])
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂' (RsbRuns.seq hdisj h₃ h₄))).congr ?_).mono ?_
  · rw [hm2n, ← hblk]
    funext r; cases r <;> simp [hΨ, hσ₂, hnv, htJ, hac]
  · simp [hwn, hm2n, hΨ, hσ₂, hac]
    nlinarith

end Sums

section SumsLoop

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

lemma range_drop_cons {s ℓ : ℕ} (h : ℓ < s) :
    (List.range s).drop ℓ = ℓ :: (List.range s).drop (ℓ + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_range]

/-- All outputs of a Horner step: `s` times `rsbGrpBody`. -/
theorem rsb_grpLoop_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ A)
    {w m s : ℕ} (σ : RsbR → List (Fin (A + 4))) (Hf : ℕ → GaussianInt)
    (blk : ℕ → List GaussianInt) (hblk : ∀ ℓ, (blk ℓ).length = 2 * m)
    (hhc : σ .hc = cstream A w ((List.range s).map Hf))
    (hpr : σ .pr = cstream A w ((List.range s).flatMap blk)) (hnv : σ .nv = [])
    (hac : σ .ac = []) (hac2 : σ .ac2 = []) (htC : σ .tC = []) (htA : σ .tA = [])
    (htJ : σ .tJ = []) (htL : σ .tL = []) (hwn : (σ (.cm .wn)).length = w)
    (hm2n : (σ .m2n).length = 2 * m) (hsn : (σ .sn).length = s) :
    RsbRuns body rg ι (rsbRep (rg .sn) (rg .tL) (rsbGrpBody rg)) σ
      (Function.update (Function.update (Function.update σ .hc []) .pr []) .nv
        (cstream A w ((List.range s).map fun ℓ => Hf ℓ - (blk ℓ).sum)).reverse)
      (s * (8 * w + 18 + 2 * m * (7 * w + 14)) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update σ .hc
        (cstream A w (((List.range s).map Hf).drop j))) .pr
        (cstream A w (((List.range s).drop j).flatMap blk))) .nv
        (cstream A w ((List.range j).map fun ℓ => Hf ℓ - (blk ℓ).sum)).reverse := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y, RsbRuns body rg ι (rsbGrpBody rg)
      (rsbUpd2 (Ψ j) .sn X .tL Y) (rsbUpd2 (Ψ (j + 1)) .sn X .tL Y)
      (8 * w + 12 + 2 * m * (7 * w + 14)) := by
    intro j hj X Y
    rw [hsn] at hj
    have hc1 : ((List.range s).map Hf).drop j = Hf j :: ((List.range s).map Hf).drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hj)]; simp
    refine (rsb_grpBody_runs hrg hdisj hA _ (Hf j) (blk j) (hblk j)
      (cstream A w (((List.range s).map Hf).drop (j + 1)))
      (cstream A w (((List.range s).drop (j + 1)).flatMap blk))
      (cstream A w ((List.range j).map fun ℓ => Hf ℓ - (blk ℓ).sum)).reverse
      (by simp [hΨ, hc1]) (by simp [hΨ, range_drop_cons hj])
      (by simp [hΨ]) (by simp [hΨ, hac]) (by simp [hΨ, hac2]) (by simp [hΨ, htC])
      (by simp [hΨ, htA]) (by simp [hΨ, htJ]) (by simp [hΨ, hwn]) (by simp [hΨ, hm2n])).congr ?_
    funext r
    cases r <;> simp [hΨ, List.range_succ, reverse_cstream_append, cstream]
  have H := rsb_rep_runs hrg hdisj (ra := .sn) (rt := .tL) (by decide) (rsbGrpBody rg)
    (σ .sn) Ψ _ hbody
  have e₀ : rsbUpd2 (Ψ 0) .sn (σ .sn) .tL [] = σ := by
    funext r; cases r <;> simp [hΨ, hhc, hpr, hnv, htL]
  rw [e₀, hsn] at H
  refine (H.congr ?_).mono (by nlinarith)
  have hd1 : (List.range s).drop s = [] := List.drop_eq_nil_of_le (by simp)
  have hd2 : ((List.range s).map Hf).drop s = [] := List.drop_eq_nil_of_le (by simp)
  funext r; cases r <;> simp [hΨ, htL, hd1, hd2]

end SumsLoop

/-! ### One Horner step -/

section Step

/-- Counters and empty scratch registers of the Horner steps. -/
structure RsbEnv {A : ℕ} (σ : RsbR → List (Fin (A + 4))) (w p s m : ℕ) : Prop where
  ready : RsbReady σ w p
  mwn : (σ .mwn).length = m * w
  m2wn : (σ .m2wn).length = 2 * m * w
  m2n : (σ .m2n).length = 2 * m
  sn : (σ .sn).length = s
  smwn : (σ .smwn).length = (s - m) * w
  ya : σ .ya = []
  b1 : σ .b1 = []
  tb : σ .tb = []
  xa : σ .xa = []
  xs : σ .xs = []
  pr : σ .pr = []
  hc : σ .hc = []
  ac : σ .ac = []
  ac2 : σ .ac2 = []
  nv : σ .nv = []
  tC : σ .tC = []
  tA : σ .tA = []
  tJ : σ .tJ = []
  tL : σ .tL = []

/-- The registers that `RsbEnv` does not constrain. -/
def RsbFreeReg (r : RsbR) : Prop :=
  r = .src ∨ r = .dst ∨ r = .msk ∨ r = .ms ∨ r = .kn ∨ r = .tK ∨ r = .ef ∨ r = .df ∨ r = .hf ∨
    r = .tswn ∨ r = .sr ∨ r = .sel ∨ r = .hv ∨ r = .vk ∨ r = .dout ∨ r = .bx ∨ r = .bo

lemma RsbEnv.update {A : ℕ} {σ : RsbR → List (Fin (A + 4))} {w p s m : ℕ} (h : RsbEnv σ w p s m)
    {r : RsbR} (hr : RsbFreeReg r) (l : List (Fin (A + 4))) :
    RsbEnv (Function.update σ r l) w p s m := by
  have hc : ∀ c, r ≠ .cm c := by
    intro c e; subst e; simp [RsbFreeReg] at hr
  unfold RsbFreeReg at hr
  refine ⟨h.ready.update r hc l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;>
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
  simp [h.mwn, h.m2wn, h.m2n, h.sn, h.smwn, h.ya, h.b1, h.tb, h.xa, h.xs, h.pr, h.hc, h.ac,
    h.ac2, h.nv, h.tC, h.tA, h.tJ, h.tL]

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- Push the contents of `a` onto `b` (in order), `a` restored. -/
def rsbCopyTo (rg : RsbR → Fin T) (a b : RsbR) : Pr P T Q A U :=
  .seq (copyR (rg a) (rg .b1) (rg .tC) id) (moveR (rg .b1) (rg b) id)

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

/-- One rounded Horner step `vk ← H - Ẽ vk`. -/
def rsbStepP : Pr P T Q A U :=
  .seq (rsbCopyTo rg .vk .ya) (.seq (rsbCopyTo rg .vk .ya) (.seq (rsbCopyTo rg .vk .ya)
    (.seq (usub (rg .smwn) (rg .ya) (rg .tC))
    (.seq (rsbRep (rg .sn) (rg .tL) (rsbWinBody rg))
    (.seq (moveR (rg .xa) (rg .xs) id) (.seq (emptyR (rg .ya))
    (.seq (cmulStream (rsbCr rg .xs .ef .pr) (rmulOne ι hι hT hQ (rsbCr rg .xs .ef .pr)))
    (.seq (emptyR (rg .xs)) (.seq (rsbCopyTo rg .hv .hc)
    (.seq (rsbRep (rg .sn) (rg .tL) (rsbGrpBody rg))
    (.seq (emptyR (rg .vk)) (moveR (rg .nv) (rg .vk) id))))))))))))

/-- The step bound of `rsbStepP`. -/
def rsbStepCost (T w s m : ℕ) : ℕ :=
  2 * m * s * (rmulCost T w + 64 * w + 64) + 64 * s * w + 64 * s + 128

variable {body : P → Pr P T Q A U} {rg}

theorem rsb_copyTo_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {a b : RsbR}
    (ha : a ≠ .b1 ∧ a ≠ .tC) (hb : b ≠ .b1 ∧ b ≠ .tC) (hab : a ≠ b)
    (σ : RsbR → List (Fin (A + 4))) (hb1 : σ .b1 = []) (htC : σ .tC = []) :
    RsbRuns body rg ι (rsbCopyTo rg a b) σ (Function.update σ b (σ a ++ σ b))
      (6 * (σ a).length + 6) := by
  have h₁ := rsb_copyR_runs (body := body) (ι := ι) hrg (a := a) (b := .b1) (t := .tC)
    ha.1 ha.2 (by decide) σ htC
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .b1) (b := b) hb.1.symm
    (Function.update σ .b1 ((σ a).reverse ++ σ .b1))
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono ?_
  · funext r
    by_cases hr : r = b
    · subst hr; simp [hb1, Function.update_of_ne hb.1, Function.update_of_ne hab.symm]
    by_cases hr' : r = .b1
    · subst hr'; simp [hr, hb1]
    simp [hr, hr']
  · simp [hb1, Function.update_of_ne ha.1]; omega

lemma rsbFree_xs : RsbFree .xs .ef .pr := ⟨by decide, by decide, by decide, fun _ => ⟨by simp,
  by simp, by simp⟩⟩

end Step

section StepProof

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

lemma rsb_length_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ x, (f x).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, h, ih, Nat.succ_mul, Nat.add_comm]

/-- The windows of the tripled array as cyclic offsets. -/
lemma rsb_windows_flat {s : ℕ} {α : Type*} (V : ZMod s → α) {m : ℕ} (hm : m ≤ s) :
    ((List.range s).flatMap fun ℓ =>
        rsbWinOf m (((rsbArr V ++ rsbArr V ++ rsbArr V).drop (s - m)).drop ℓ)) =
      (List.range s).flatMap fun ℓ : ℕ =>
        (rsbHs m).map fun h : ℤ => V ((ℓ : ZMod s) + (h : ZMod s)) :=
  List.flatMap_congr fun ℓ hℓ => rsb_windows V hm ℓ (List.mem_range.mp hℓ)

theorem rsb_copyTo_runs' (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {a b : RsbR}
    (ha : a ≠ .b1 ∧ a ≠ .tC) (hb : b ≠ .b1 ∧ b ≠ .tC) (hab : a ≠ b)
    (σ : RsbR → List (Fin (A + 4))) (X Y : List (Fin (A + 4))) (hX : σ a = X) (hY : σ b = Y)
    (hb1 : σ .b1 = []) (htC : σ .tC = []) :
    RsbRuns body rg ι (rsbCopyTo rg a b) σ (Function.update σ b (X ++ Y)) (6 * X.length + 6) := by
  have h := rsb_copyTo_runs (body := body) hrg hdisj ha hb hab σ hb1 htC
  rwa [hX, hY] at h

set_option maxHeartbeats 2000000 in
/-- **One Horner step.** From `vk` holding `V` and `hv` holding `H`, `rsbStepP` leaves
`rsbStep p m E H V` on `vk` and every other register as it was. -/
theorem rsb_step_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p s m : ℕ} [NeZero s] (hm : m ≤ s) (hw : 1 ≤ w) (hp : p ≤ w)
    (E : ZMod s → ℤ → ℤ) (H V : ZMod s → GaussianInt) (hfV : ∀ ℓ, Fits w (V ℓ))
    (hfE : ∀ ℓ, ∀ h ∈ rsbHs m, Fits w (rsbReal (E ℓ h)))
    (σ : RsbR → List (Fin (A + 4))) (henv : RsbEnv σ w p s m)
    (hvk : σ .vk = cstream A w (rsbArr V)) (hhv : σ .hv = cstream A w (rsbArr H))
    (hef : σ .ef = cstream A w (rsbETab s m E)) :
    RsbRuns body rg ι (rsbStepP rg hι hT hQ) σ
      (Function.update σ .vk (cstream A w (rsbArr (rsbStep p m E H V))))
      (rsbStepCost T w s m) := by
  have hs : 1 ≤ s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hwn := henv.ready.wn
  have harrl : (rsbArr V).length = s := length_rsbArr V
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (rsbArr V ++ rsbArr V ++ rsbArr V).drop (s - m) := ⟨_, rfl⟩
  have hYl : Y.length = 2 * s + m := by simp [hY, harrl]; omega
  obtain ⟨X, hX⟩ : ∃ X, X = (List.range s).flatMap fun ℓ => rsbWinOf m (Y.drop ℓ) := ⟨_, rfl⟩
  have hX' : X = (List.range s).flatMap fun ℓ : ℕ =>
      (rsbHs m).map fun h : ℤ => V ((ℓ : ZMod s) + (h : ZMod s)) := by
    rw [hX, hY, rsb_windows_flat V hm]
  have hXl : X.length = s * (2 * m) := by
    rw [hX', rsb_length_flatMap_const _ _ (2 * m) (fun _ => by simp [length_rsbHs])]; simp
  have hEl : (rsbETab s m E).length = s * (2 * m) := by
    rw [rsbETab, rsb_length_flatMap_const _ _ (2 * m) (fun _ => by simp [length_rsbHs])]; simp
  obtain ⟨Pl, hPl⟩ : ∃ Pl, Pl = (List.range s).flatMap (rsbBlk p m E V) := ⟨_, rfl⟩
  have hPX : List.zipWith (fun a b => tdivN p (a * b)) X (rsbETab s m E) = Pl := by
    rw [hPl, hX, hY]; exact rsb_products p hm E V
  -- three copies of `vk` onto `ya`
  have hτ : ∀ (L₁ L₂ : List (Fin (A + 4))),
      Function.update (Function.update σ .ya L₁) .ya L₂ = Function.update σ .ya L₂ :=
    fun _ _ => Function.update_idem _ _ _
  have h₁ := (rsb_copyTo_runs' (body := body) hrg hdisj (a := .vk) (b := .ya)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ _ _ hvk henv.ya henv.b1
    henv.tC).congr (by rw [List.append_nil])
  have h₂ := (rsb_copyTo_runs' (body := body) hrg hdisj (a := .vk) (b := .ya)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
    (Function.update σ .ya (cstream A w (rsbArr V))) (cstream A w (rsbArr V))
    (cstream A w (rsbArr V)) (by simp [hvk]) (by simp)
    (by simp [henv.b1]) (by simp [henv.tC])).congr (hτ _ _)
  have h₃ := (rsb_copyTo_runs' (body := body) hrg hdisj (a := .vk) (b := .ya)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
    (Function.update σ .ya (cstream A w (rsbArr V) ++ cstream A w (rsbArr V)))
    (cstream A w (rsbArr V)) (cstream A w (rsbArr V) ++ cstream A w (rsbArr V)) (by simp [hvk])
    (by simp) (by simp [henv.b1]) (by simp [henv.tC])).congr (hτ _ _)
  -- drop `s - m` records
  have h₄ := (rsb_usub_runs (body := body) (ι := ι) hrg (c := .smwn) (a := .ya) (t := .tC)
    (by decide) (by decide) (by decide)
    (Function.update σ .ya (cstream A w (rsbArr V) ++
      (cstream A w (rsbArr V) ++ cstream A w (rsbArr V)))) (by simp [henv.tC])).congr
    (show _ = Function.update σ .ya (cstream A w Y) by
      rw [hτ]
      congr 1
      rw [Function.update_self, Function.update_of_ne (by decide), henv.smwn, hY,
        ← drop_cstream', cstream_append, cstream_append, List.append_assoc])
  -- the windows
  have h₅ := rsb_winLoop_runs (body := body) (ι := ι) hrg hdisj (w := w) (m := m) (s := s)
    (Function.update σ .ya (cstream A w Y)) Y (by omega) (by simp) (by simp [henv.tb])
    (by simp [henv.xa]) (by simp [henv.tC]) (by simp [henv.tL]) (by simp [henv.sn])
    (by simp [hwn]) (by simp [henv.mwn]) (by simp [henv.m2wn])
  rw [← hX] at h₅
  have h₆ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .xa) (b := .xs) (by decide)
    (Function.update (Function.update (Function.update σ .ya (cstream A w Y)) .ya
      (cstream A w (Y.drop s))) .xa (cstream A w X).reverse)
  have h₇ := rsb_emptyR_runs (body := body) (ι := ι) hrg .ya
    (Function.update (Function.update σ .ya (cstream A w (Y.drop s))) .xs (cstream A w X))
  -- the products
  have h₈ := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA rsbFree_xs
    (ρ := Function.update σ .xs (cstream A w X))
    ((henv.ready.update .xs (fun c => by simp) _)) hw hp X (rsbETab s m E) (by rw [hXl, hEl])
    (by rw [hX']; intro a ha; simp only [List.mem_flatMap, List.mem_map] at ha
        obtain ⟨_, _, _, _, rfl⟩ := ha; exact hfV _)
    (by intro a ha; simp only [rsbETab, List.mem_flatMap, List.mem_map] at ha
        obtain ⟨_, _, h, hh, rfl⟩ := ha; exact ⟨hfE _ h hh, rfl⟩)
    (by simp) (by simp [hef])
  rw [hPX] at h₈
  have h₉ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xs
    (Function.update (Function.update σ .xs (cstream A w X)) .pr
      (cstream A w Pl ++ Function.update σ .xs (cstream A w X) .pr))
  -- `H` onto `hc`
  have h₁₀ := rsb_copyTo_runs' (body := body) hrg hdisj (a := .hv) (b := .hc)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
    (Function.update σ .pr (cstream A w Pl)) (cstream A w (rsbArr H)) [] (by simp [hhv])
    (by simp [henv.hc])
    (by simp [henv.b1]) (by simp [henv.tC])
  -- the window sums
  have h₁₁ := rsb_grpLoop_runs (body := body) (ι := ι) hrg hdisj hA (w := w) (m := m) (s := s)
    (Function.update (Function.update σ .pr (cstream A w Pl)) .hc
      (cstream A w (rsbArr H) ++ []))
    (fun ℓ : ℕ => H (ℓ : ZMod s)) (rsbBlk p m E V) (length_rsbBlk p m E V)
    (by simp [rsbArr]) (by simp [hPl]) (by simp [henv.nv]) (by simp [henv.ac])
    (by simp [henv.ac2]) (by simp [henv.tC]) (by simp [henv.tA]) (by simp [henv.tJ])
    (by simp [henv.tL]) (by simp [hwn]) (by simp [henv.m2n]) (by simp [henv.sn])
  have hnew : ((List.range s).map fun ℓ : ℕ => H (ℓ : ZMod s) - (rsbBlk p m E V ℓ).sum) =
      rsbArr (rsbStep p m E H V) := by
    simp only [rsbArr, rsbStep_blk]
  rw [hnew] at h₁₁
  have h₁₂ := rsb_emptyR_runs (body := body) (ι := ι) hrg .vk
    (Function.update σ .nv (cstream A w (rsbArr (rsbStep p m E H V))).reverse)
  have h₁₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .nv) (b := .vk) (by decide)
    (Function.update (Function.update σ .nv (cstream A w (rsbArr (rsbStep p m E H V))).reverse)
      .vk [])
  have hYd : (Y.drop s).length = s + m := by simp [hYl]; omega
  have e₆ := h₆.congr (show _ = Function.update (Function.update σ .ya (cstream A w (Y.drop s)))
      .xs (cstream A w X) by funext r; cases r <;> simp [henv.xa, henv.xs])
  have e₇ := h₇.congr (show _ = Function.update σ .xs (cstream A w X) by
      funext r; cases r <;> simp [henv.ya])
  have e₉ := h₉.congr (show _ = Function.update σ .pr (cstream A w Pl) by
      funext r; cases r <;> simp [henv.xs, henv.pr])
  have e₁₁ := h₁₁.congr (show _ = Function.update σ .nv
      (cstream A w (rsbArr (rsbStep p m E H V))).reverse by
      funext r; cases r <;> simp [henv.hc, henv.pr])
  have e₁₃ := h₁₃.congr (show _ = Function.update σ .vk
      (cstream A w (rsbArr (rsbStep p m E H V))) by
      funext r; cases r <;> simp [henv.nv])
  refine (RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj e₆ (RsbRuns.seq hdisj e₇
    (RsbRuns.seq hdisj h₈ (RsbRuns.seq hdisj e₉ (RsbRuns.seq hdisj h₁₀
    (RsbRuns.seq hdisj e₁₁ (RsbRuns.seq hdisj h₁₂ e₁₃)))))))))))).mono ?_
  have hsm : (s - m) * w ≤ s * w := Nat.mul_le_mul_right w (Nat.sub_le s m)
  have hmw : m * w ≤ m * s * w := Nat.mul_le_mul_right w (Nat.le_mul_of_pos_right m hs)
  simp [hXl, hYd, harrl, length_rsbArr, henv.smwn, henv.xs, henv.ya, henv.pr, hvk]
  unfold rsbStepCost
  generalize rmulCost T w = R
  nlinarith [hsm, hmw]

end StepProof

/-! ### The Neumann loop and the line -/

section Line

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

lemma rsbEnv_upd2 {σ : RsbR → List (Fin (A + 4))} {w p s m : ℕ} (h : RsbEnv σ w p s m)
    {a b : RsbR} (ha : RsbFreeReg a) (hb : RsbFreeReg b) (X Y : List (Fin (A + 4))) :
    RsbEnv (rsbUpd2 σ a X b Y) w p s m := (h.update ha X).update hb Y

/-- **The Neumann loop.** `K` Horner steps (`K = |kn|`) from `vk = hv = H`. -/
theorem rsb_iter_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p s m K : ℕ} [NeZero s] (hm : m ≤ s) (hw : 1 ≤ w) (hp : p ≤ w)
    (E : ZMod s → ℤ → ℤ) (H : ZMod s → GaussianInt)
    (hfit : ∀ k < K, ∀ ℓ, Fits w (rsbIter p m E H k ℓ))
    (hfE : ∀ ℓ, ∀ h ∈ rsbHs m, Fits w (rsbReal (E ℓ h)))
    (σ : RsbR → List (Fin (A + 4))) (henv : RsbEnv σ w p s m)
    (hvk : σ .vk = cstream A w (rsbArr H)) (hhv : σ .hv = cstream A w (rsbArr H))
    (hef : σ .ef = cstream A w (rsbETab s m E)) (htK : σ .tK = []) (hkn : (σ .kn).length = K) :
    RsbRuns body rg ι (rsbRep (rg .kn) (rg .tK) (rsbStepP rg hι hT hQ)) σ
      (Function.update σ .vk (cstream A w (rsbArr (rsbIter p m E H K))))
      (K * (rsbStepCost T w s m + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun k =>
      Function.update σ .vk (cstream A w (rsbArr (rsbIter p m E H k))) := ⟨_, rfl⟩
  have hbody : ∀ k < (σ .kn).length, ∀ X Y, RsbRuns body rg ι (rsbStepP rg hι hT hQ)
      (rsbUpd2 (Ψ k) .kn X .tK Y) (rsbUpd2 (Ψ (k + 1)) .kn X .tK Y) (rsbStepCost T w s m) := by
    intro k hk X Y
    rw [hkn] at hk
    have henv' : RsbEnv (rsbUpd2 (Ψ k) .kn X .tK Y) w p s m := by
      rw [hΨ]
      exact rsbEnv_upd2 (henv.update (by simp [RsbFreeReg]) _) (by simp [RsbFreeReg])
        (by simp [RsbFreeReg]) X Y
    refine (rsb_step_runs hrg hdisj hι hT hQ hA hm hw hp E H (rsbIter p m E H k) (hfit k hk) hfE
      _ henv' (by simp [hΨ]) (by simp [hΨ, hhv]) (by simp [hΨ, hef])).congr ?_
    funext r; cases r <;> simp [hΨ, rsbIter]
  have H₁ := rsb_rep_runs hrg hdisj (ra := .kn) (rt := .tK) (by decide) (rsbStepP rg hι hT hQ)
    (σ .kn) Ψ _ hbody
  have e₀ : rsbUpd2 (Ψ 0) .kn (σ .kn) .tK [] = σ := by
    funext r; cases r <;> simp [hΨ, rsbIter, hvk, htK]
  rw [e₀, hkn] at H₁
  refine H₁.congr ?_
  funext r; cases r <;> simp [hΨ, htK]

/-- The zero record. -/
lemma csyms_zero (A w : ℕ) : csyms A w 0 = List.replicate w (pairSym A false false) := by
  simp [csyms, coeffSyms, red, List.ofFn_const]

lemma cstream_replicate_zero (A w k : ℕ) :
    cstream A w (List.replicate k 0) = List.replicate (k * w) (pairSym A false false) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, cstream_cons, ih, csyms_zero, List.replicate_append_replicate,
      Nat.succ_mul, Nat.add_comm (k * w) w]

variable (rg) (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)

/-- **`B̃₀` on one line.** Select, halve, `K` Horner steps, the diagonal, and the padded output. -/
def rsbLineP : Pr P T Q A U :=
  .seq (rsbSelP rg) (.seq (rsbHalfP rg hι hT hQ) (.seq (rsbCopyTo rg .hv .vk)
    (.seq (rsbRep (rg .kn) (rg .tK) (rsbStepP rg hι hT hQ))
    (.seq (cmulStream (rsbCr rg .vk .df .dout) (rmulOne ι hι hT hQ (rsbCr rg .vk .df .dout)))
    (.seq (emptyR (rg .vk)) (.seq (moveR (rg .dout) (rg .dst) id)
    (.seq (umulSym 1 (pairSym A false false) (rg .tswn) (rg .dst) (rg .tC)) (emptyR (rg .hv)))))))))

/-- The step bound of one line. -/
def rsbLineCost (T w s t m K : ℕ) : ℕ :=
  K * (rsbStepCost T w s m + 6) + 2 * s * (rmulCost T w + 16 * w + 16) + 32 * t * w + 16 * t + 64

end Line

section LineProof

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

lemma rsbSel_full (ln : List GaussianInt) (mask : List Bool) (h : ln.length = mask.length) :
    rsbSel ln mask mask.length = ((ln.zip mask).filter (·.2)).map (·.1) := by
  rw [rsbSel, List.take_of_length_le (by simp [h])]

lemma rsbFree_vk : RsbFree .vk .df .dout := ⟨by decide, by decide, by decide, fun _ => ⟨by simp,
  by simp, by simp⟩⟩

set_option maxHeartbeats 2000000 in
/-- **`B̃₀` on one line, exactly.** The register `src` holds the line `N` (`t` records, numerators
at scale `2^p`) on top of `rest`, `msk` the row-selection mask, `ef`, `df`, `hf` the weight tables
and the halving constant, `kn` the step count `K`; the counters and scratch registers are as in
`RsbEnv`. Afterwards `src` holds `rest` and `dst` gains, reversed on top, the records
`rsbLineNum p K m E D N` followed by `t - s` zero records; every other register is as before. -/
theorem rsb_line_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p s t m K : ℕ} [NeZero s] [NeZero t] (hst : s < t) (hm : m ≤ s) (hp1 : 1 ≤ p)
    (hpw : p < w) (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ) (N : ZMod t → GaussianInt)
    (hfN : ∀ j, Fits w (N j)) (hfE : ∀ ℓ, ∀ h ∈ rsbHs m, Fits w (rsbReal (E ℓ h)))
    (hfD : ∀ ℓ, Fits w (rsbReal (D ℓ)))
    (hfit : ∀ k ≤ K, ∀ ℓ, Fits w (rsbIter p m E (rsbHalf (s := s) N) k ℓ))
    (σ : RsbR → List (Fin (A + 4))) (henv : RsbEnv σ w p s m) (rest : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w (rsbArr N) ++ rest)
    (hmsk : σ .msk = (rsbMask s t).map bitSymbol)
    (hef : σ .ef = cstream A w (rsbETab s m E))
    (hdf : σ .df = cstream A w (rsbArr fun ℓ => rsbReal (D ℓ)))
    (hhf : σ .hf = csyms A w (rsbReal (2 ^ (p - 1))))
    (hkn : (σ .kn).length = K) (htswn : (σ .tswn).length = (t - s) * w)
    (hms : σ .ms = []) (hsr : σ .sr = []) (hsel : σ .sel = []) (hhv : σ .hv = [])
    (hvk : σ .vk = []) (hdout : σ .dout = []) (htK : σ .tK = []) :
    RsbRuns body rg ι (rsbLineP rg hι hT hQ) σ
      (Function.update (Function.update σ .src rest) .dst
        ((cstream A w (rsbArr (rsbLineNum p K m E D N) ++ List.replicate (t - s) 0)).reverse ++
          σ .dst))
      (rsbLineCost T w s t m K) := by
  have hs : 1 ≤ s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hwn := henv.ready.wn
  have hw : 1 ≤ w := by omega
  have hlen : (rsbArr N).length = (rsbMask s t).length := by
    rw [length_rsbArr, length_rsbMask]
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = rsbArr fun ℓ : ZMod s => N (rowIndex s t ℓ) := ⟨_, rfl⟩
  -- selection
  have h₁ := rsb_sel_runs (body := body) (ι := ι) hrg hdisj σ (rsbMask s t) (rsbArr N) rest hlen
    hmsk hms hsrc hsr hsel henv.tC hwn
  rw [rsbSel_full _ _ hlen, rsb_filter_mask hst N, ← hSL, length_rsbMask] at h₁
  -- halving
  have h₂ := rsb_half_runs (body := body) (ι := ι) hι hT hQ hrg hdisj hA hp1 hpw
    (Function.update (Function.update σ .src rest) .sel (cstream A w SL))
    ((henv.ready.update .src (fun c => by simp) _).update .sel (fun c => by simp) _) SL
    (by rw [hSL]; intro a ha; simp only [rsbArr, List.mem_map] at ha
        obtain ⟨_, _, rfl⟩ := ha; exact hfN _)
    (by simp) (by simp [hhf]) (by simp [hhv])
  have eH : SL.map (tdivN 1) = rsbArr (rsbHalf (s := s) N) := by
    rw [hSL]; simp only [rsbArr, List.map_map]; rfl
  rw [eH] at h₂
  have e₂ := h₂.congr (show _ = Function.update (Function.update σ .src rest) .hv
      (cstream A w (rsbArr (rsbHalf (s := s) N))) by funext r; cases r <;> simp [hsel])
  -- the first iterate
  have h₃ := (rsb_copyTo_runs' (body := body) hrg hdisj (a := .hv) (b := .vk)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
    (Function.update (Function.update σ .src rest) .hv (cstream A w (rsbArr (rsbHalf (s := s) N))))
    (cstream A w (rsbArr (rsbHalf (s := s) N))) [] (by simp) (by simp [hvk]) (by simp [henv.b1])
    (by simp [henv.tC])).congr (by rw [List.append_nil])
  -- the Neumann loop
  have henv₃ : RsbEnv (Function.update (Function.update (Function.update σ .src rest) .hv
      (cstream A w (rsbArr (rsbHalf (s := s) N)))) .vk
      (cstream A w (rsbArr (rsbHalf (s := s) N)))) w p s m :=
    ((henv.update (by simp [RsbFreeReg]) _).update (by simp [RsbFreeReg]) _).update
      (by simp [RsbFreeReg]) _
  have h₄ := rsb_iter_runs (body := body) hrg hdisj hι hT hQ hA (K := K) hm hw (by omega) E
    (rsbHalf (s := s) N) (fun k hk => hfit k hk.le) hfE _ henv₃ (by simp) (by simp) (by simp [hef])
    (by simp [htK]) (by simp [hkn])
  -- the diagonal
  obtain ⟨VK, hVK⟩ : ∃ VK, VK = rsbIter p m E (rsbHalf (s := s) N) K := ⟨_, rfl⟩
  rw [← hVK] at h₄
  have h₅ := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA rsbFree_vk
    (ρ := Function.update (Function.update (Function.update (Function.update σ .src rest) .hv
      (cstream A w (rsbArr (rsbHalf (s := s) N)))) .vk
      (cstream A w (rsbArr (rsbHalf (s := s) N)))) .vk (cstream A w (rsbArr VK)))
    ((((henv.ready.update .src (fun c => by simp) _).update .hv (fun c => by simp) _).update .vk
      (fun c => by simp) _).update .vk (fun c => by simp) _) hw (by omega)
    (rsbArr VK) (rsbArr fun ℓ => rsbReal (D ℓ)) (by simp [length_rsbArr])
    (by intro a ha; simp only [rsbArr, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha
        rw [hVK]; exact hfit K le_rfl _)
    (by intro a ha; simp only [rsbArr, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha
        exact ⟨hfD _, rfl⟩)
    (by simp) (by simp [hdf])
  have eD : List.zipWith (fun a b => tdivN p (a * b)) (rsbArr VK) (rsbArr fun ℓ => rsbReal (D ℓ)) =
      rsbArr (rsbLineNum p K m E D N) := by
    rw [rsbArr, rsbArr, rsb_zipWith_map, rsbArr, hVK]; rfl
  rw [eD] at h₅
  have h₆ := rsb_emptyR_runs (body := body) (ι := ι) hrg .vk
    (Function.update (Function.update (Function.update (Function.update (Function.update σ .src
      rest) .hv (cstream A w (rsbArr (rsbHalf (s := s) N)))) .vk
      (cstream A w (rsbArr (rsbHalf (s := s) N)))) .vk
      (cstream A w (rsbArr VK))) .dout (cstream A w (rsbArr (rsbLineNum p K m E D N)) ++
        Function.update (Function.update (Function.update (Function.update σ .src rest) .hv
          (cstream A w (rsbArr (rsbHalf (s := s) N)))) .vk
          (cstream A w (rsbArr (rsbHalf (s := s) N)))) .vk
          (cstream A w (rsbArr VK)) .dout))
  have e₆ := h₆.congr (show _ = Function.update (Function.update (Function.update σ .src rest)
      .hv (cstream A w (rsbArr (rsbHalf (s := s) N)))) .dout
      (cstream A w (rsbArr (rsbLineNum p K m E D N))) by
    funext r; cases r <;> simp [hdout, hvk])
  -- the output
  obtain ⟨τ, hτ⟩ : ∃ τ : RsbR → List (Fin (A + 4)), τ = Function.update
      (Function.update σ .src rest) .hv (cstream A w (rsbArr (rsbHalf (s := s) N))) := ⟨_, rfl⟩
  rw [← hτ] at e₂ h₃ h₄ h₅ e₆
  have h₇ := (rsb_moveR_runs (body := body) (ι := ι) hrg (a := .dout) (b := .dst) (by decide)
    (Function.update τ .dout (cstream A w (rsbArr (rsbLineNum p K m E D N))))).congr
    (show _ = Function.update τ .dst ((cstream A w (rsbArr (rsbLineNum p K m E D N))).reverse ++
      σ .dst) by funext r; cases r <;> simp [hτ, hdout])
  have h₈ := (rsb_umulSym_runs (body := body) (ι := ι) hrg (pairSym A false false) (c := .tswn)
    (a := .dst) (t := .tC) (by decide) (by decide) (by decide)
    (Function.update τ .dst ((cstream A w (rsbArr (rsbLineNum p K m E D N))).reverse ++ σ .dst))
    (by simp [hτ, henv.tC])).congr
    (show _ = Function.update τ .dst (List.replicate ((t - s) * w) (pairSym A false false) ++
      ((cstream A w (rsbArr (rsbLineNum p K m E D N))).reverse ++ σ .dst)) by
      funext r; cases r <;> simp [hτ, htswn])
  have h₉ := rsb_emptyR_runs (body := body) (ι := ι) hrg .hv
    (Function.update τ .dst (List.replicate ((t - s) * w) (pairSym A false false) ++
      ((cstream A w (rsbArr (rsbLineNum p K m E D N))).reverse ++ σ .dst)))
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj e₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj e₆ (RsbRuns.seq hdisj h₇
    (RsbRuns.seq hdisj h₈ h₉)))))))).congr ?_).mono ?_
  · have hz : (cstream A w (rsbArr (rsbLineNum p K m E D N) ++ List.replicate (t - s) 0)).reverse =
        List.replicate ((t - s) * w) (pairSym A false false) ++
          (cstream A w (rsbArr (rsbLineNum p K m E D N))).reverse := by
      rw [reverse_cstream_append, cstream_replicate_zero, List.reverse_replicate]
    rw [hz, List.append_assoc]
    funext r; cases r <;> simp [hτ, hhv]
  · have hsel_len : SL.length = s := by rw [hSL, length_rsbArr]
    have hts : (t - s) * w ≤ t * w := Nat.mul_le_mul_right w (Nat.sub_le t s)
    have hsw : s * w ≤ t * w := Nat.mul_le_mul_right w hst.le
    simp [hsel_len, length_rsbArr, hsr, hsel, hhv, hvk, hdout, htswn, hτ]
    unfold rsbLineCost
    generalize rmulCost T w = R
    generalize rsbStepCost T w s m = SC
    nlinarith

end LineProof

end

end IntegerMultBounds.MathlibTM2.Fast
