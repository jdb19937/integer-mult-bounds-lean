module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBCore

/-!
# Line-machine pieces shared by the `B̃₀` machines

Stream lemmas (`drop_cstream`, `take_cstream`, `reverse_cstream_append`, …), the row selection
`rsbSel`, `rsbSelP` (`rsb_sel_runs`: one record of `src` kept per set mask bit), the
subtraction body `rsbSubBody` (`rsb_subBody_runs`), the product environment `RsbEnv` with its
free registers `RsbFreeReg`, and the record copy `rsbCopyTo` (`rsb_copyTo_runs`). The banded
line (`Fast/BandLine*`) builds on them.

The Neumann line machine (`rsbLineP`, `rsb_line_runs`, `rsbLineCost`) was removed with the
Neumann `B̃₀`; restore from `1cb2723b`.
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

lemma tableOut_single (g : GaussianInt → GaussianInt → GaussianInt) (l : List GaussianInt)
    (c : GaussianInt) : tableOut g (l.map fun a => [a]) [c] = l.map fun a => g a c := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [tableOut] at ih ⊢; exact ih

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- The registers of a product call. -/
abbrev rsbCr (rg : RsbR → Fin T) (x y o : RsbR) : CR → Fin T := fun c => rg (rsbRemap x y o c)

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

variable {body : P → Pr P T Q A U} {rg}

end Half


/-- The off-diagonal weight table: for `ℓ = 0, …, s - 1` the real entries `E ℓ h`, `h` over
`rsbHs m`. -/
def rsbETab (s m : ℕ) (E : ZMod s → ℤ → ℤ) : List GaussianInt :=
  (List.range s).flatMap fun ℓ : ℕ => (rsbHs m).map fun h : ℤ => rsbReal (E (ℓ : ZMod s) h)

/-! ### Window sums -/

section Sums

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- Subtract the record on top of `pr` from the record on `ac`. -/
def rsbSubBody (rg : RsbR → Fin T) : Pr P T Q A U :=
  .seq (rsbSubWord (rg .ac) (rg .pr) (rg .ac2) (rg (.cm .wn)) (rg .tA))
    (moveR (rg .ac2) (rg .ac) id)

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

end Sums


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

end Step

section StepProof

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

lemma rsb_length_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ x, (f x).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, h, ih, Nat.succ_mul, Nat.add_comm]

end StepProof

/-! ### The Neumann loop and the line -/

section Line

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

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

end Line

section LineProof

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

lemma rsbSel_full (ln : List GaussianInt) (mask : List Bool) (h : ln.length = mask.length) :
    rsbSel ln mask mask.length = ((ln.zip mask).filter (·.2)).map (·.1) := by
  rw [rsbSel, List.take_of_length_le (by simp [h])]

end LineProof

end

end IntegerMultBounds.MathlibTM2.Fast
