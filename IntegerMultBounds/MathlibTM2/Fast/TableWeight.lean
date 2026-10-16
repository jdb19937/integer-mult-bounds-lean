module

public import IntegerMultBounds.MathlibTM2.Fast.TableExp
public import IntegerMultBounds.Resampling.TableIdx

/-!
# Streams of the weight tables

For one axis with lengths `s < t`, parameter `α` and precision `p`, the table machines write
the integer weight tables `tableA`, `tableE`, `tableD` of `Resampling.WeightTable` (the tables of
`Mult.Pipeline.lineA` and `Mult.Pipeline.lineB`) as streams of real coefficients
`coeffSyms A w (red w ⟨entry, 0⟩)`. Every stream program has 48 variables: the weight routine
`tblExpCode` on variables `0 … 33` (`piN p` in `18`, `p` in `19`, the exponent numerator in `20`,
the denominator in `21`, the sign in `22`, the result in `23`), the inputs `s`, `t`, `α` in
`34 … 36`, and its own counters above. `tblPiSetup48` first computes `piN p` with the embedded
`tblPiCode` (`tbl_pi48_do`).

## Stream orders

* `tblStreamA`: rows `k = 0, …, t − 1`; in row `k` the window `tblWinA s t m k`, the integers
  `⌊s k / t⌋ − m + i`, `i = 0, …, 2m`. `tbl_floor_centre`: `⌊resampCentre s t k⌋ = ⌊s k / t⌋`;
  `tblWinA_pairwise`, `tblWinA_toFinset`: the window is `truncWindow s t m k` in increasing order.
* `tblStreamE`: rows `ℓ = 0, …, s − 1`; in row `ℓ` the window `tblWinE m`, the integers
  `−m, …, −1, 1, …, m` (`tblWinE_pairwise`, `tblWinE_toFinset`: `offDiagWindow m` in increasing
  order).
* `tblStreamD`: `ℓ = 0, …, s − 1`.

## Entries in naturals

* `tbl_tableA_eq`: `tableA k j = expPiNat true p (x²) (α² t²) / α` with `x = |s k − t j|`
  (`tblGaussX`, from `TableIdx.gauss_num`).
* `tbl_tableE_eq`: `tableE ℓ (±g) = expPiNat true p (α² (A² − B²)) (s²)` with `A = |t h + rr ℓ|`
  (`tblOffA`) and `B = |rr (ℓ + h)|` from the residue `tblOffR` (`tbl_res_nat`, `tbl_res_neg`).
* `tbl_tableD_eq`: `tableD ℓ = expPiNat false p (α² cen²) (s²) / 2^(2α²)` with
  `cen = |rr ℓ|` (`tblCen`).

## Theorems

For each table, `tblStream*_do` (the program emits the stream, with an explicit atom bound
`#entries · (310 p + c) + O(p + t)`) and `tblStream*_host` (on the host, the output register gains
exactly the stream, in at most `atoms · tblC W w + 2 |stream| + 2` steps). The word-size
hypothesis is `α² ((s + t)(m + 1))² 2^(13p+8) < 2^W` (`m = 0` for `tableD`).
`TblDo.keep`: variables outside `TblCode.tblDsts` keep their values.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Fast.TableNum IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
open IntegerMultBounds.Resampling.WeightTable (tableA tableE tableD rr)
open IntegerMultBounds.MathlibTM2.Layer


/-! ### Written variables -/

section Keep

variable {n A W w : ℕ}

/-- The variable an instruction writes. -/
def TblIns.tblDst : TblIns n → List (Fin n)
  | .add _ _ c => [c]
  | .sub _ _ c => [c]
  | .mul _ _ c => [c]
  | .div _ _ c => [c]
  | .mod _ _ c => [c]
  | .copy _ c => [c]
  | .zero c => [c]
  | .inc c => [c]
  | .emit _ _ => []

/-- The variables a program writes. -/
def TblCode.tblDsts : TblCode n → List (Fin n)
  | .ins i => i.tblDst
  | .seq c d => c.tblDsts ++ d.tblDsts
  | .ite _ _ c d => c.tblDsts ++ d.tblDsts
  | .loop _ _ c => c.tblDsts

theorem TblIns.run_keep (i : TblIns n) (st : TblSt n A) (x : Fin n) (hx : x ∉ i.tblDst) :
    (i.run A W w st).val x = st.val x := by
  cases i <;> simp_all [TblIns.tblDst, TblIns.run, Function.update_of_ne]

theorem TblBig.keep {c : TblCode n} {st st' : TblSt n A} {k : ℕ} (h : TblBig A W w c st st' k)
    (x : Fin n) (hx : x ∉ c.tblDsts) : st'.val x = st.val x := by
  induction h with
  | ins i st => exact TblIns.run_keep i st x hx
  | seq _ _ ih₁ ih₂ =>
    simp only [TblCode.tblDsts, List.mem_append, not_or] at hx
    rw [ih₂ hx.2, ih₁ hx.1]
  | iteT _ _ ih =>
    simp only [TblCode.tblDsts, List.mem_append, not_or] at hx
    exact ih hx.1
  | iteF _ _ ih =>
    simp only [TblCode.tblDsts, List.mem_append, not_or] at hx
    exact ih hx.2
  | loopF _ => rfl
  | loopT _ _ _ ih₁ ih₂ => rw [ih₂ hx, ih₁ hx]

/-- Variables a program does not write keep their values. -/
theorem TblDo.keep {c : TblCode n} {st : TblSt n A} {P : TblSt n A → Prop} {K : ℕ}
    (h : TblDo A W w c st P K) :
    TblDo A W w c st (fun s => P s ∧ ∀ x, x ∉ c.tblDsts → s.val x = st.val x) K := by
  obtain ⟨st', k, hb, hp, hk⟩ := h
  exact ⟨st', k, hb, ⟨hp, fun x hx => hb.keep x hx⟩, hk⟩

end Keep

/-! ### Helpers -/

theorem tbl_pairs_red (A w x : ℕ) :
    tblPairs A w x 0 = coeffSyms A w (red w ⟨(x : ℤ), 0⟩) := by
  simp [tblPairs, red]

theorem tbl_castLE_ne {m n : ℕ} (h : m ≤ n) (x : Fin n) (hx : m ≤ x.val) :
    ∀ y : Fin m, Fin.castLE h y ≠ x := fun y hy => by
  have := congrArg Fin.val hy; simp at this; omega

/-- The variables of `tblPiCode` inside a 48-variable stream program: `piN P` in `18` (the slot
of the weight routine), the rest (with `P` in `0`) on scratch variables of the routine. -/
def tblPiMap48 : Fin 18 → Fin 48 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18, 16, 17]

theorem tblPiMap48_inj : Function.Injective tblPiMap48 := by decide

/-- The weight routine inside a 48-variable stream program: its variables are the first 34. -/
def tblExpMap48 : Fin 34 → Fin 48 := Fin.castLE (by norm_num)

/-- The magnitude of the centered residue: `u` if `2u < s`, else `s − u`. -/
def tblCen (s u : ℕ) : ℕ := if u + u < s then u else s - u

theorem tbl_res_nat (s t x : ℕ) : TableIdx.res s t (x : ℤ) = t * x % s := by
  unfold TableIdx.res
  rw [show (t : ℤ) * (x : ℤ) = ((t * x : ℕ) : ℤ) by push_cast; ring, ← Int.natCast_mod,
    Int.toNat_natCast]

theorem tbl_rr_sq_nat (s t x : ℕ) (hs : 0 < s) :
    (rr s t (x : ℤ)) ^ 2 = ((tblCen s (t * x % s) : ℕ) : ℤ) ^ 2 := by
  rw [TableIdx.rr_sq s t hs, tbl_res_nat, tblCen]
  congr 3
  simp only [two_mul]

/-- The diagonal table entry in naturals. -/
theorem tbl_tableD_eq (s t α p ℓ : ℕ) (hs : 0 < s) (hℓ : ℓ < s) (hp : 13 ≤ p) :
    tableD s t α p (ℓ : ZMod s) = ((expPiNat false p (α * α * (tblCen s (t * ℓ % s) *
      tblCen s (t * ℓ % s))) (s * s) / 2 ^ (α * α + α * α) : ℕ) : ℤ) := by
  rw [tableD_nat s t α p hp, tableDNat, ZMod.val_natCast_of_lt hℓ]
  congr 1
  have h2 : ((α : ℤ) ^ 2 * (rr s t (ℓ : ℤ)) ^ 2).toNat =
      α * α * (tblCen s (t * ℓ % s) * tblCen s (t * ℓ % s)) := by
    rw [tbl_rr_sq_nat s t ℓ hs]
    rw [show (α : ℤ) ^ 2 * ((tblCen s (t * ℓ % s) : ℕ) : ℤ) ^ 2 =
      ((α * α * (tblCen s (t * ℓ % s) * tblCen s (t * ℓ % s)) : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
  rw [h2, sq, show 2 * α ^ 2 = α * α + α * α by ring]

/-! ### Streams on the host -/

section StreamHost

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → IntegerMultBounds.MathlibTM2.Host.Pr P T Q A U} {n : ℕ}
  {rg : TblR n → Fin T}

/-- A program emitting the list `L` (from an empty `acc`) within `K` atoms writes `L` onto the
output register `out` as `tblHost`, first symbol on top, in at most
`K · tblC W w + 2 |L| + 2` steps. -/
theorem tbl_stream_host (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) {c : TblCode n} {st : TblSt n A} {L : List (Fin (A + 4))} {K : ℕ}
    (h : TblDo A W w c st (fun s' => s'.acc = L.reverse ++ st.acc) K)
    (hst : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = []) (v : IntegerMultBounds.MathlibTM2.Host.HS T Q A U)
    (S : IntegerMultBounds.MathlibTM2.Host.Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ K * tblC W w + 2 * L.length + 2 ∧
      IntegerMultBounds.MathlibTM2.Stack.Exec body (tblHost rg c out) (IntegerMultBounds.MathlibTM2.Host.mk v S) m (IntegerMultBounds.MathlibTM2.Host.mk v' S') ∧
      S'.R out = L ++ S.R out ∧ (∃ st' : TblSt n A, tblHolds rg S' (tblRho W wl nl st')) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨v', S', m, st', hp, hu, hm, he, hout', hS', h1, h2, h3, h4⟩ :=
    tblHost_runs (body := body) hrg hout wl nl hwl hnl hw h hst v S hS
  rw [hacc, List.append_nil] at hp
  rw [hp, List.reverse_reverse] at hout'
  rw [hp, List.length_reverse] at hm
  exact ⟨v', S', m, hu, hm, he, hout', ⟨_, hS'⟩, h1, h2, h3, h4⟩

end StreamHost

/-! ### The diagonal table -/

local notation "kS" => (34 : Fin 48)
local notation "kT" => (35 : Fin 48)
local notation "kAl" => (36 : Fin 48)
local notation "kL" => (37 : Fin 48)
local notation "kZ" => (38 : Fin 48)
local notation "kU" => (39 : Fin 48)
local notation "kTmp" => (40 : Fin 48)
local notation "kAA" => (41 : Fin 48)
local notation "kEnt" => (42 : Fin 48)
local notation "kE2" => (43 : Fin 48)
local notation "kPw" => (44 : Fin 48)
local notation "kI" => (45 : Fin 48)
local notation "kMn" => (46 : Fin 48)

/-- One diagonal entry `ℓ` (in `kL`): `a = α² · cen(tℓ mod s)²` into variable `20`, the weight
routine, the division by `2^(2α²)` and the emission. -/
def tblDiagBody : TblCode 48 :=
  tblBlock 48 [.mul kT kL kU, .mod kU kS kU] (.add kU kU kTmp) ;;
    .ite kTmp kS (.ins (.copy kU kMn)) (.ins (.sub kS kU kMn)) ;;
    tblBlock 48 [.mul kMn kMn kTmp] (.mul kAA kTmp 20) ;;
    tblExpCode.rename tblExpMap48 ;;
    tblBlock 48 [.div 23 kPw kEnt] (.emit kEnt kZ)

/-- The setup of a stream program: `p` (in `19`) copied to `0` and `piN p` into `18`. -/
def tblPiSetup48 : TblCode 48 := tblBlock 48 [] (.copy 19 0) ;; tblPiCode.rename tblPiMap48

/-- The diagonal stream program: `s`, `t`, `α` in `34 … 36`, `p` in `19`. -/
def tblStreamDCode : TblCode 48 :=
  tblPiSetup48 ;;
    tblBlock 48 [.zero kZ, .mul kAl kAl kAA, .add kAA kAA kE2, .mul kS kS 21] (.zero 22) ;;
    tblPow2 kPw kE2 kI ;;
    tblFor kL kS tblDiagBody

theorem tbl_cen_le (s u : ℕ) (hu : u < s) : 2 * tblCen s u ≤ s := by
  unfold tblCen; split_ifs <;> omega

theorem tbl_diag_pos (p s α m : ℕ) (hp : 2 ≤ p) (hs : 0 < s) (hm : 2 * m ≤ s) (hαp : α ^ 2 ≤ p) :
    piN p * (α * α * (m * m)) / (s * s) < p * 2 ^ (5 * p) := by
  have hpi := tbl_piN_lt p hp
  set Y := piN p * (α * α * (m * m)) / (s * s) with hY
  have h1 : Y * (s * s) ≤ piN p * (α * α * (m * m)) := Nat.div_mul_le_self _ _
  have h2 : 4 * (α * α * (m * m)) ≤ α * α * (s * s) := by
    have : (2 * m) * (2 * m) ≤ s * s := Nat.mul_le_mul hm hm
    nlinarith
  have hss : 0 < s * s := Nat.mul_pos hs hs
  have h3 : 4 * Y * (s * s) ≤ piN p * (α * α) * (s * s) := by
    calc 4 * Y * (s * s) = 4 * (Y * (s * s)) := by ring
      _ ≤ 4 * (piN p * (α * α * (m * m))) := Nat.mul_le_mul_left _ h1
      _ = piN p * (4 * (α * α * (m * m))) := by ring
      _ ≤ piN p * (α * α * (s * s)) := Nat.mul_le_mul_left _ h2
      _ = piN p * (α * α) * (s * s) := by ring
  have h4 : 4 * Y ≤ piN p * (α * α) := Nat.le_of_mul_le_mul_right h3 hss
  have h5 : piN p * (α * α) ≤ piN p * p := Nat.mul_le_mul_left _ (by rw [← sq]; exact hαp)
  have h6 : piN p * p < 4 * 2 ^ (5 * p) * p := Nat.mul_lt_mul_of_pos_right hpi (by omega)
  have : 4 * Y < 4 * (p * 2 ^ (5 * p)) := by
    calc 4 * Y ≤ piN p * p := h4.trans h5
      _ < 4 * 2 ^ (5 * p) * p := h6
      _ = 4 * (p * 2 ^ (5 * p)) := by ring
  omega

/-- Consequences of the word-size hypothesis of the stream programs. -/
theorem tbl_W_facts {W p α N : ℕ} (hα : 2 ≤ α) (hN : 1 ≤ N)
    (hW : α ^ 2 * N ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) :
    13 * p + 8 < W ∧ α ^ 2 * N ^ 2 * 2 ^ (5 * p + 2) < 2 ^ W ∧ N * N < 2 ^ W ∧
      α * α * (N * N) < 2 ^ W := by
  have h1 : 1 ≤ α ^ 2 * N ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : 2 ^ (13 * p + 8) < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ h1) hW
  have h3 : 13 * p + 8 < W := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  have h4 : 2 ^ (5 * p + 2) ≤ 2 ^ (13 * p + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 1 ≤ 2 ^ (13 * p + 8) := Nat.one_le_two_pow
  refine ⟨h3, lt_of_le_of_lt (Nat.mul_le_mul_left _ h4) hW, ?_, ?_⟩
  · have : N * N ≤ α ^ 2 * N ^ 2 * 2 ^ (13 * p + 8) := by
      have hα1 : 1 ≤ α ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc N * N = 1 * N ^ 2 * 1 := by ring
        _ ≤ α ^ 2 * N ^ 2 * 2 ^ (13 * p + 8) := by gcongr
    omega
  · have : α * α * (N * N) ≤ α ^ 2 * N ^ 2 * 2 ^ (13 * p + 8) := by
      calc α * α * (N * N) = α ^ 2 * N ^ 2 * 1 := by ring
        _ ≤ α ^ 2 * N ^ 2 * 2 ^ (13 * p + 8) := by gcongr
    omega

theorem tblDiagBody_do {A W w : ℕ} (st : TblSt 48 A) {s t α p j : ℕ}
    (h18 : st.val 18 = piN p) (h19 : st.val 19 = p) (h21 : st.val 21 = s * s) (h22 : st.val 22 = 0)
    (hS : st.val kS = s) (hT : st.val kT = t) (hAA : st.val kAA = α * α)
    (hPw : st.val kPw = 2 ^ (α * α + α * α)) (hZ : st.val kZ = 0) (hL : st.val kL = j)
    (hj : j < s) (hp : 13 ≤ p) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p)
    (hW : α ^ 2 * (s + t) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) :
    TblDo A W w tblDiagBody st (fun s' => s'.acc =
      (coeffSyms A w (red w ⟨tableD s t α p (j : ZMod s), 0⟩)).reverse ++ st.acc)
      (310 * p + 120) := by
  obtain ⟨hW1, hW2, hW3, hW4⟩ := tbl_W_facts hα (by omega : 1 ≤ s + t) hW
  have hs : 0 < s := by omega
  obtain ⟨u, hu⟩ : ∃ u, u = t * j % s := ⟨_, rfl⟩
  have hus : u < s := hu ▸ Nat.mod_lt _ hs
  obtain ⟨m, hm⟩ : ∃ m, m = tblCen s u := ⟨_, rfl⟩
  have hm2 : 2 * m ≤ s := hm ▸ tbl_cen_le s u hus
  have hNN : s * s ≤ (s + t) * (s + t) := Nat.mul_le_mul (by omega) (by omega)
  have htj : t * j ≤ (s + t) * (s + t) := Nat.mul_le_mul (by omega) (by omega)
  have hmm : m * m ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
  have hst : s + t ≤ (s + t) * (s + t) := Nat.le_mul_self _
  have htjW : t * j < 2 ^ W := lt_of_le_of_lt htj hW3
  have h4N : 4 * ((s + t) * (s + t)) < 2 ^ W :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by nlinarith)) hW4
  -- `u` and `u + u`
  refine (TblDo.block _ _ ?_ rfl).seq (K₂ := 2 + (2 + (310 * p + 100 + 2))) (fun s₁ hs₁ => ?_)
    |>.mono (fun _ h => h) (by simp; omega)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hT, hL, hS]
    rw [← hu]
    omega
  subst hs₁
  have hU₁ : (tblExactList A w ([.mul kT kL kU, .mod kU kS kU] ++ [.add kU kU kTmp]) st).val kU = u := by
    simp [tblExactList, TblIns.exact, hT, hL, hS, hu]
  have hTmp₁ : (tblExactList A w ([.mul kT kL kU, .mod kU kS kU] ++ [.add kU kU kTmp]) st).val kTmp = u + u := by
    simp [tblExactList, TblIns.exact, hT, hL, hS, hu]
  set s₁ := tblExactList A w ([.mul kT kL kU, .mod kU kS kU] ++ [.add kU kU kTmp]) st with hs₁
  have hS₁ : s₁.val kS = s := by simp [hs₁, tblExactList, TblIns.exact, hS]
  -- the centered magnitude
  have hite : TblDo A W w (.ite kTmp kS (.ins (.copy kU kMn)) (.ins (.sub kS kU kMn))) s₁
      (fun s₂ => s₂ = ⟨Function.update s₁.val kMn m, s₁.acc⟩) 2 := by
    by_cases hc : u + u < s
    · refine TblDo.iteT (by rw [hTmp₁, hS₁]; exact hc) (TblDo.insX _ (by trivial) ?_)
      simp [TblIns.exact, hU₁, hm, tblCen, hc]
    · refine TblDo.iteF (by rw [hTmp₁, hS₁]; exact hc) (TblDo.insX _ ?_ ?_)
      · simp only [TblIns.fits, hS₁, hU₁]; omega
      · simp [TblIns.exact, hU₁, hS₁, hm, tblCen, hc]
  refine hite.seq (fun s₂ hs₂ => ?_)
  subst hs₂
  have hfx : ∀ x : Fin 48, 34 ≤ x.val → ∀ y : Fin 34, tblExpMap48 y ≠ x := fun x hx =>
    tbl_castLE_ne _ x hx
  have hmmW : m * m < 2 ^ W := by omega
  have ha : α * α * (m * m) ≤ α * α * ((s + t) * (s + t)) := Nat.mul_le_mul_left _ (by omega)
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₃ hs₃ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact]
    refine ⟨hmmW, ?_⟩
    rw [hs₁]; simp [tblExactList, TblIns.exact, hAA]
    omega
  subst hs₃
  set s₃ := tblExactList A w ([.mul kMn kMn kTmp] ++ [.mul kAA kTmp 20])
    ⟨Function.update s₁.val kMn m, s₁.acc⟩ with hs₃
  have hv₃ : s₃.val 18 = piN p ∧ s₃.val 19 = p ∧ s₃.val 20 = α * α * (m * m) ∧
      s₃.val 21 = s * s ∧ s₃.val 22 = 0 ∧ s₃.val kPw = 2 ^ (α * α + α * α) ∧ s₃.val kZ = 0 ∧
      s₃.acc = st.acc := by
    simp [hs₃, hs₁, tblExactList, TblIns.exact, h18, h19, h21, h22, hAA, hPw, hZ]
  obtain ⟨g18, g19, g20, g21, g22, gPw, gZ, gacc⟩ := hv₃
  have hexp := (tblExp_do (A := A) (W := W) (w := w) (s₃.restrict tblExpMap48) (p := p)
    (a := α * α * (m * m)) (b := s * s) false g18 g19 g20 g21 (by simp only [Bool.false_eq_true, ite_false]; exact g22) hp (by omega)
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ (by rw [sq, sq]; exact ha)) hW2)
    (fun _ => tbl_diag_pos p s α m (by omega) hs hm2 hαp)).rename (Fin.castLE_injective _)
  refine hexp.seq (K₂ := 2) (fun s₄ ⟨⟨hres, _, _, _, _, _, hacc₄⟩, hfr₄⟩ => ?_)
  have hres' : s₄.val 23 = expPiNat false p (α * α * (m * m)) (s * s) := hres
  have hacc₄' : s₄.acc = s₃.acc := hacc₄
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  have hPw₄ : s₄.val kPw = 2 ^ (α * α + α * α) := by rw [hfr₄ _ (hfx _ (by decide)), gPw]
  have hZ₄ : s₄.val kZ = 0 := by rw [hfr₄ _ (hfx _ (by decide)), gZ]
  simp [tblExactList, TblIns.exact, hres', hPw₄, hZ₄, hacc₄', gacc]
  rw [tbl_pairs_red, tbl_tableD_eq s t α p j hs hj hp, ← hu, ← hm]

/-- The diagonal stream of one axis: `ℓ = 0, …, s − 1`, each entry `tableD ℓ` as a real
coefficient of width `w`. -/
def tblStreamD (A w s t α p : ℕ) : List (Fin (A + 4)) :=
  (List.range s).flatMap fun ℓ : ℕ => coeffSyms A w (red w ⟨tableD s t α p (ℓ : ZMod s), 0⟩)

theorem tbl_range_flatMap_succ {β : Type} (f : ℕ → List β) (j : ℕ) :
    ((List.range (j + 1)).flatMap f).reverse = (f j).reverse ++ ((List.range j).flatMap f).reverse := by
  rw [List.range_succ, List.flatMap_append, List.reverse_append]
  simp

/-- The setup of a stream program: `p` copied to `0`, `piN p` into `18` by the embedded `π`
machine. -/
theorem tbl_pi48_do {A W w : ℕ} (st : TblSt 48 A) {p : ℕ} (hp' : st.val 19 = p) (hp : 2 ≤ p)
    (hW : 5 * p + 16 ≤ W) :
    TblDo A W w tblPiSetup48 st
      (fun s => s.val 18 = piN p ∧ s.acc = st.acc ∧ ∀ x : Fin 48, 19 ≤ x.val → s.val x = st.val x)
      (1 + (150 * p + 400)) := by
  refine (TblDo.block (P := fun s => s = ⟨Function.update st.val 0 p, st.acc⟩) [] (.copy 19 0)
    ⟨trivial, trivial⟩ (by simp [tblExactList, TblIns.exact, hp'])).seq (fun s₀ hs₀ => ?_)
  subst hs₀
  refine ((tblPi_do (A := A) (W := W) (w := w) (TblSt.restrict tblPiMap48
    ⟨Function.update st.val 0 p, st.acc⟩) (P := p) hp (by simp [tblPiMap48, tblPiIn]) hW).rename
    tblPiMap48_inj).mono (fun s ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, fun x hx => ?_⟩) le_rfl
  rw [h3 x (fun y hy => by
    have := congrArg Fin.val hy
    fin_cases y <;> simp [tblPiMap48] at this <;> omega)]
  simp [Function.update_of_ne (show x ≠ 0 by intro h; subst h; simp at hx)]

/-- **The diagonal stream.** From `s`, `t`, `α` in variables `34 … 36` and `p` in `19`, with
`13 ≤ p`, `2 ≤ α`, `α² ≤ p`, `0 < s` and `α² (s + t)² 2^(13p+8) < 2^W`, `tblStreamDCode` emits
`tblStreamD` within `s (310 p + 123) + 160 p + 450` atoms. -/
theorem tblStreamD_do {A W w : ℕ} (st : TblSt 48 A) {s t α p : ℕ}
    (hs' : st.val 34 = s) (ht' : st.val 35 = t) (hα' : st.val 36 = α) (hp' : st.val 19 = p)
    (hp : 13 ≤ p) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hs : 0 < s)
    (hW : α ^ 2 * (s + t) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) :
    TblDo A W w tblStreamDCode st (fun s' => s'.acc = (tblStreamD A w s t α p).reverse ++ st.acc)
      (s * (310 * p + 123) + (160 * p + 450)) := by
  obtain ⟨hW1, hW2, hW3, hW4⟩ := tbl_W_facts hα (by omega : 1 ≤ s + t) hW
  have hNN : s * s ≤ (s + t) * (s + t) := Nat.mul_le_mul (by omega) (by omega)
  have hst : s + t ≤ (s + t) * (s + t) := Nat.le_mul_self _
  have hαα : α * α ≤ α * α * ((s + t) * (s + t)) := Nat.le_mul_of_pos_right _ (by positivity)
  have hαW : α * α + α * α < W := by nlinarith
  have h2αα : α * α + α * α < 2 ^ W := lt_trans hαW Nat.lt_two_pow_self
  have hαα' : α * α ≤ p := by rw [← sq]; exact hαp
  refine ((tbl_pi48_do (W := W) (w := w) st hp' (by omega) (by omega)).seq
    (K₂ := 5 + (4 * (α * α + α * α) + 5 + (1 + (s * (310 * p + 120 + 1 + 2) + 2))))
    (fun s₁ ⟨h18₁, hacc₁, hfr₁⟩ => ?_)).mono (fun _ h => h) (by nlinarith)
  -- constants
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₂ hs₂ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hfr₁ (36 : Fin 48) (by decide), hα',
      hfr₁ (34 : Fin 48) (by decide), hs']
    omega
  subst hs₂
  set s₂ := tblExactList A w ([.zero kZ, .mul kAl kAl kAA, .add kAA kAA kE2, .mul kS kS 21] ++
    [.zero 22]) s₁ with hs₂
  have hv₂ : s₂.val 18 = piN p ∧ s₂.val 19 = p ∧ s₂.val 21 = s * s ∧ s₂.val 22 = 0 ∧
      s₂.val kS = s ∧ s₂.val kT = t ∧ s₂.val kAA = α * α ∧ s₂.val kE2 = α * α + α * α ∧
      s₂.val kZ = 0 ∧ s₂.acc = st.acc := by
    simp [hs₂, tblExactList, TblIns.exact, h18₁, hfr₁ (19 : Fin 48) (by decide),
      hfr₁ (34 : Fin 48) (by decide), hfr₁ (35 : Fin 48) (by decide), hfr₁ (36 : Fin 48) (by decide),
      hp', hs', ht', hα', hacc₁]
  obtain ⟨g18, g19, g21, g22, gS, gT, gAA, gE2, gZ, gacc⟩ := hv₂
  have hpow := tblPow2_do (A := A) (W := W) (w := w) (c := kPw) (e := kE2) (i := kI) (by decide)
    (by decide) (by decide) s₂ (by rw [gE2]; exact hαW)
  rw [gE2] at hpow
  refine hpow.seq (fun s₃ ⟨hPw₃, _, hfr₃, hacc₃⟩ => ?_)
  let F : ℕ → List (Fin (A + 4)) := fun ℓ : ℕ =>
    coeffSyms A w (red w ⟨tableD s t α p (ℓ : ZMod s), 0⟩)
  let Inv : ℕ → TblSt 48 A → Prop := fun j s' =>
    s'.acc = ((List.range j).flatMap F).reverse ++ st.acc ∧ s'.val 18 = piN p ∧ s'.val 19 = p ∧
    s'.val 21 = s * s ∧ s'.val 22 = 0 ∧ s'.val kS = s ∧ s'.val kT = t ∧ s'.val kAA = α * α ∧
    s'.val kPw = 2 ^ (α * α + α * α) ∧ s'.val kZ = 0
  refine TblDo.for s (310 * p + 120) (by rw [hfr₃ _ (by decide) (by decide), gS])
    (lt_of_le_of_lt (by omega) hW3) (by decide) Inv ?_ ?_ ?_
  · refine ⟨by simp [hacc₃, gacc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · rw [Function.update_of_ne (by decide), hfr₃ 18 (by decide) (by decide), g18]
    · rw [Function.update_of_ne (by decide), hfr₃ 19 (by decide) (by decide), g19]
    · rw [Function.update_of_ne (by decide), hfr₃ 21 (by decide) (by decide), g21]
    · rw [Function.update_of_ne (by decide), hfr₃ 22 (by decide) (by decide), g22]
    · rw [Function.update_of_ne (by decide), hfr₃ kS (by decide) (by decide), gS]
    · rw [Function.update_of_ne (by decide), hfr₃ kT (by decide) (by decide), gT]
    · rw [Function.update_of_ne (by decide), hfr₃ kAA (by decide) (by decide), gAA]
    · rw [Function.update_of_ne (by decide), hPw₃]
    · rw [Function.update_of_ne (by decide), hfr₃ kZ (by decide) (by decide), gZ]
  · intro j hj s' ⟨hacc', h18', h19', h21', h22', hS', hT', hAA', hPw', hZ'⟩ hL' hS''
    refine (tblDiagBody_do s' h18' h19' h21' h22' hS' hT' hAA' hPw' hZ' hL' hj hp hα hαp hW).keep.mono
      (fun s'' ⟨hacc'', hk⟩ => ?_) le_rfl
    refine ⟨by rw [hk _ (by decide), hL'], by rw [hk _ (by decide), hS'], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · simp only; rw [hacc'', hacc', tbl_range_flatMap_succ, List.append_assoc]
    all_goals
      dsimp only
      rwa [Function.update_of_ne (by decide), hk _ (by decide)]
  · intro s' ⟨hacc', _⟩ _ _
    rw [hacc', tblStreamD]

theorem length_tblStreamD (A w s t α p : ℕ) : (tblStreamD A w s t α p).length = s * w := by
  simp [tblStreamD, List.length_flatMap, List.sum_replicate]

section DHost

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → IntegerMultBounds.MathlibTM2.Host.Pr P T Q A U}
  {rg : TblR 48 → Fin T}

/-- **The diagonal stream on the host.** The output register `out` gains exactly
`tblStreamD A w s t α p` (`s w` symbols: `coeffSyms A w (red w ⟨tableD s t α p ℓ, 0⟩)` for
`ℓ = 0, …, s − 1`), in at most `(s (310 p + 123) + 160 p + 450) · tblC W w + 2 s w + 2` steps. -/
theorem tblStreamD_host (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (st : TblSt 48 A) (hst : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    {s t α p : ℕ} (hs' : st.val 34 = s) (ht' : st.val 35 = t) (hα' : st.val 36 = α)
    (hp' : st.val 19 = p) (hp : 13 ≤ p) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hs : 0 < s)
    (hW : α ^ 2 * (s + t) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) (v : IntegerMultBounds.MathlibTM2.Host.HS T Q A U)
    (S : IntegerMultBounds.MathlibTM2.Host.Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, v'.user = v.user ∧
      m ≤ (s * (310 * p + 123) + (160 * p + 450)) * tblC W w + 2 * (s * w) + 2 ∧
      IntegerMultBounds.MathlibTM2.Stack.Exec body (tblHost rg tblStreamDCode out) (IntegerMultBounds.MathlibTM2.Host.mk v S) m
        (IntegerMultBounds.MathlibTM2.Host.mk v' S') ∧
      S'.R out = tblStreamD A w s t α p ++ S.R out ∧
      (∃ st' : TblSt 48 A, tblHolds rg S' (tblRho W wl nl st')) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  have h := tbl_stream_host (body := body) hrg hout wl nl hwl hnl hw
    (tblStreamD_do st hs' ht' hα' hp' hp hα hαp hs hW) hst hacc v S hS
  rwa [length_tblStreamD] at h

end DHost

/-! ### The Gaussian table -/

/-- The window of row `k` of `Ã`, increasing: `⌊s k / t⌋ − m + i`, `i = 0, …, 2m`. -/
def tblWinA (s t m k : ℕ) : List ℤ :=
  (List.range (2 * m + 1)).map fun i : ℕ => ((s * k / t : ℕ) : ℤ) - m + i

theorem tbl_floor_centre (s t k : ℕ) (hk : k < t) :
    ⌊IntegerMultBounds.NLogN.resampCentre s t (k : ZMod t)⌋ = ((s * k / t : ℕ) : ℤ) := by
  have : NeZero t := ⟨by omega⟩
  unfold IntegerMultBounds.NLogN.resampCentre
  rw [ZMod.val_natCast_of_lt hk,
    show (s : ℝ) * k / t = ((s * k : ℕ) : ℝ) / (t : ℕ) by push_cast; ring,
    Int.floor_div_natCast, Int.floor_natCast]
  push_cast
  rfl

theorem tblWinA_pairwise (s t m k : ℕ) : (tblWinA s t m k).Pairwise (· < ·) := by
  unfold tblWinA
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp ?_
  intro a b h
  omega

theorem tblWinA_toFinset (s t m k : ℕ) (hk : k < t) :
    (tblWinA s t m k).toFinset = IntegerMultBounds.NLogN.truncWindow s t m (k : ZMod t) := by
  ext j
  simp only [tblWinA, List.mem_toFinset, List.mem_map, List.mem_range,
    IntegerMultBounds.NLogN.truncWindow, Finset.mem_Icc, tbl_floor_centre s t k hk]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h
    refine ⟨(j - ((s * k / t : ℕ) : ℤ) + m).toNat, by omega, by omega⟩

/-- The Gaussian exponent numerator `|s k − t j|` of the entry `j = ⌊s k / t⌋ − m + i`. -/
def tblGaussX (s t m k i : ℕ) : ℕ :=
  if i ≤ m then s * k % t + t * (m - i) else t * (i - m) - s * k % t

theorem tbl_tableA_eq (s t α p m k i : ℕ) (ht : 0 < t) (hk : k < t) (hp : 13 ≤ p) :
    tableA s t α p (k : ZMod t) (((s * k / t : ℕ) : ℤ) - m + i) =
      ((expPiNat true p (tblGaussX s t m k i * tblGaussX s t m k i) (α * α * (t * t)) / α : ℕ) : ℤ) := by
  rw [tableA_nat s t α p hp, tableANat, ZMod.val_natCast_of_lt hk, TableIdx.gauss_num s t m k i ht]
  congr 3
  · unfold tblGaussX; split_ifs <;> ring
  · ring

local notation "aK" => (37 : Fin 48)
local notation "aM" => (39 : Fin 48)
local notation "aI" => (40 : Fin 48)
local notation "aCnt" => (41 : Fin 48)
local notation "aU" => (42 : Fin 48)
local notation "aX" => (43 : Fin 48)
local notation "aTmp" => (44 : Fin 48)
local notation "aEnt" => (45 : Fin 48)

/-- One Gaussian entry `(k, i)`, with `u = s k mod t` in `aU`: `x = |s k − t j|` (`tblGaussX`),
`a = x²` into variable `20`, the weight routine, the division by `α` and the emission. -/
def tblGaussBody : TblCode 48 :=
  .ite aM aI
    (tblBlock 48 [.sub aI aM aTmp, .mul kT aTmp aTmp] (.sub aTmp aU aX))
    (tblBlock 48 [.sub aM aI aTmp, .mul kT aTmp aTmp] (.add aU aTmp aX)) ;;
    tblBlock 48 [] (.mul aX aX 20) ;;
    tblExpCode.rename tblExpMap48 ;;
    tblBlock 48 [.div 23 kAl aEnt] (.emit aEnt kZ)

/-- Row `k` (in `aK`) of the Gaussian table: `u = s k mod t`, then the `2m + 1` entries. -/
def tblRowABody : TblCode 48 :=
  tblBlock 48 [.mul kS aK aU] (.mod aU kT aU) ;; tblFor aI aCnt tblGaussBody

/-- The Gaussian stream program: `s`, `t`, `α` in `34 … 36`, `m` in `39`, `p` in `19`. -/
def tblStreamACode : TblCode 48 :=
  tblPiSetup48 ;;
    tblBlock 48 [.zero kZ, .zero 22, .inc 22, .mul kAl kAl aX, .mul kT kT aTmp, .mul aX aTmp 21,
      .add aM aM aCnt] (.inc aCnt) ;;
    tblFor aK kT tblRowABody

theorem tbl_gaussX_le (s t m k i : ℕ) (ht : 0 < t) (hi : i < 2 * m + 1) :
    tblGaussX s t m k i ≤ t * (m + 1) := by
  have hu := Nat.mod_lt (s * k) ht
  unfold tblGaussX
  split_ifs with h
  · have : t * (m - i) ≤ t * m := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · have h1 : t * (i - m) ≤ t * m := Nat.mul_le_mul_left _ (by omega)
    have h2 : t * m ≤ t * (m + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem tblGaussBody_do {A W w : ℕ} (st : TblSt 48 A) {s t α p m k i : ℕ}
    (h18 : st.val 18 = piN p) (h19 : st.val 19 = p) (h21 : st.val 21 = α * α * (t * t))
    (h22 : st.val 22 = 1) (hT : st.val kT = t) (hAl : st.val kAl = α) (hZ : st.val kZ = 0)
    (hM : st.val aM = m) (hI : st.val aI = i) (hU : st.val aU = s * k % t)
    (hk : k < t) (hi : i < 2 * m + 1) (hp : 13 ≤ p) (hα : 2 ≤ α)
    (hW : α ^ 2 * ((s + t) * (m + 1)) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) :
    TblDo A W w tblGaussBody st (fun s' => s'.acc = (coeffSyms A w (red w
      ⟨tableA s t α p (k : ZMod t) (((s * k / t : ℕ) : ℤ) - m + i), 0⟩)).reverse ++ st.acc)
      (310 * p + 107) := by
  have ht : 0 < t := by omega
  obtain ⟨hW1, hW2, hW3, hW4⟩ := tbl_W_facts hα (Nat.mul_pos (by omega) (by omega)) hW
  set N := (s + t) * (m + 1) with hN
  have hmN : m + 1 ≤ N := Nat.le_mul_of_pos_left _ (by omega)
  have h4N : 4 * (N * N) < 2 ^ W :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by nlinarith)) hW4
  obtain ⟨u, hu⟩ : ∃ u, u = s * k % t := ⟨_, rfl⟩
  have hut : u < t := hu ▸ Nat.mod_lt _ ht
  obtain ⟨x, hx⟩ : ∃ x, x = tblGaussX s t m k i := ⟨_, rfl⟩
  have hxle : x ≤ t * (m + 1) := hx ▸ tbl_gaussX_le s t m k i ht hi
  have htN : t * (m + 1) ≤ N := Nat.mul_le_mul_right _ (by omega)
  have hNN : N ≤ N * N := Nat.le_mul_self _
  have htm : t * m ≤ N := le_trans (Nat.mul_le_mul_left _ (by omega)) htN
  have htm1 : t * (m + 1) = t * m + t := by ring
  have hxx : x * x ≤ N * N := Nat.mul_le_mul (hxle.trans htN) (hxle.trans htN)
  have hfx : ∀ x : Fin 48, 34 ≤ x.val → ∀ y : Fin 34, tblExpMap48 y ≠ x := fun x hx =>
    tbl_castLE_ne _ x hx
  -- `x = |s k − t j|`
  have hite : TblDo A W w (.ite aM aI
      (tblBlock 48 [.sub aI aM aTmp, .mul kT aTmp aTmp] (.sub aTmp aU aX))
      (tblBlock 48 [.sub aM aI aTmp, .mul kT aTmp aTmp] (.add aU aTmp aX))) st
      (fun s₁ => s₁.val aX = x ∧ s₁.val 18 = piN p ∧ s₁.val 19 = p ∧ s₁.val 21 = α * α * (t * t) ∧
        s₁.val 22 = 1 ∧ s₁.val kAl = α ∧ s₁.val kZ = 0 ∧ s₁.acc = st.acc) 4 := by
    by_cases hc : m < i
    · have hmi : t * (i - m) ≤ t * m := Nat.mul_le_mul_left _ (by omega)
      have hut' : u ≤ t * (i - m) := le_trans hut.le (Nat.le_mul_of_pos_right _ (by omega))
      refine TblDo.iteT (by rw [hM, hI]; exact hc) (TblDo.block _ _ ?_ ?_)
      · simp [tblFitsList, TblIns.fits, TblIns.exact, hM, hI, hT, hU, ← hu]
        omega
      · simp [tblExactList, TblIns.exact, hM, hI, hT, hU, ← hu, hx, tblGaussX, h18, h19, h21, h22,
          hAl, hZ]
        omega
    · have hmi : t * (m - i) ≤ t * m := Nat.mul_le_mul_left _ (by omega)
      refine TblDo.iteF (by rw [hM, hI]; exact hc) (TblDo.block _ _ ?_ ?_)
      · simp [tblFitsList, TblIns.fits, TblIns.exact, hM, hI, hT, hU, ← hu]
        omega
      · simp [tblExactList, TblIns.exact, hM, hI, hT, hU, ← hu, hx, tblGaussX, h18, h19, h21, h22,
          hAl, hZ]
        omega
  refine (hite.seq (K₂ := 1 + (310 * p + 100 + 2)) (fun s₁ ⟨hX₁, g18, g19, g21, g22, gAl, gZ, gacc⟩ =>
    ?_)).mono (fun _ h => h) (by omega)
  refine (TblDo.block _ _ (by simp [tblFitsList, TblIns.fits, hX₁]; omega) rfl).seq
    (fun s₂ hs₂ => ?_)
  subst hs₂
  set s₂ := tblExactList A w ([] ++ [.mul aX aX 20]) s₁ with hs₂
  have hv₂ : s₂.val 18 = piN p ∧ s₂.val 19 = p ∧ s₂.val 20 = x * x ∧ s₂.val 21 = α * α * (t * t) ∧
      s₂.val 22 = 1 ∧ s₂.val kAl = α ∧ s₂.val kZ = 0 ∧ s₂.acc = st.acc := by
    simp [hs₂, tblExactList, TblIns.exact, hX₁, g18, g19, g21, g22, gAl, gZ, gacc]
  obtain ⟨f18, f19, f20, f21, f22, fAl, fZ, facc⟩ := hv₂
  have hxa : x * x ≤ α ^ 2 * N ^ 2 := by
    have h1 : 1 ≤ α ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc x * x ≤ 1 * (N * N) := by rw [one_mul]; exact hxx
      _ ≤ α ^ 2 * N ^ 2 := by rw [← sq]; exact Nat.mul_le_mul_right _ h1
  have hexp := (tblExp_do (A := A) (W := W) (w := w) (s₂.restrict tblExpMap48) (p := p)
    (a := x * x) (b := α * α * (t * t)) true f18 f19 f20 f21 (by simp only [ite_true]; exact f22) hp (by omega)
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ hxa) hW2)
    (fun h => absurd h (by decide))).rename (Fin.castLE_injective _)
  refine hexp.seq (K₂ := 2) (fun s₃ ⟨⟨hres, _, _, _, _, _, hacc₃⟩, hfr₃⟩ => ?_)
  have hres' : s₃.val 23 = expPiNat true p (x * x) (α * α * (t * t)) := hres
  have hacc₃' : s₃.acc = s₂.acc := hacc₃
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  have hAl₃ : s₃.val kAl = α := by rw [hfr₃ _ (hfx _ (by decide)), fAl]
  have hZ₃ : s₃.val kZ = 0 := by rw [hfr₃ _ (hfx _ (by decide)), fZ]
  rw [tbl_tableA_eq s t α p m k i ht hk hp, ← hx, ← tbl_pairs_red]
  simp [tblExactList, TblIns.exact, hres', hAl₃, hZ₃, hacc₃', facc]

/-- The Gaussian entry `(k, i)` as a coefficient. -/
def tblEntA (A w s t α p m k i : ℕ) : List (Fin (A + 4)) :=
  coeffSyms A w (red w ⟨tableA s t α p (k : ZMod t) (((s * k / t : ℕ) : ℤ) - m + i), 0⟩)

theorem tblRowABody_do {A W w : ℕ} (st : TblSt 48 A) {s t α p m k : ℕ}
    (h18 : st.val 18 = piN p) (h19 : st.val 19 = p) (h21 : st.val 21 = α * α * (t * t))
    (h22 : st.val 22 = 1) (hS : st.val kS = s) (hT : st.val kT = t) (hAl : st.val kAl = α)
    (hZ : st.val kZ = 0) (hM : st.val aM = m) (hCnt : st.val aCnt = 2 * m + 1)
    (hK : st.val aK = k) (hk : k < t) (hp : 13 ≤ p) (hα : 2 ≤ α)
    (hW : α ^ 2 * ((s + t) * (m + 1)) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) :
    TblDo A W w tblRowABody st (fun s' => s'.acc =
      ((List.range (2 * m + 1)).flatMap (tblEntA A w s t α p m k)).reverse ++ st.acc)
      (2 + (1 + ((2 * m + 1) * (310 * p + 107 + 1 + 2) + 2))) := by
  have ht : 0 < t := by omega
  obtain ⟨hW1, hW2, hW3, hW4⟩ :=
    tbl_W_facts hα (Nat.mul_pos (Nat.add_pos_right s ht) (Nat.succ_pos m)) hW
  obtain ⟨N, hN⟩ : ∃ N, N = (s + t) * (m + 1) := ⟨_, rfl⟩
  rw [← hN] at hW3 hW4
  have hmN : m + 1 ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hNN : N ≤ N * N := Nat.le_mul_self _
  have hsN : s + t ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hsk : s * k ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  have h4N : 4 * (N * N) < 2 ^ W :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by nlinarith)) hW4
  have h2m : 2 * m + 1 < 2 ^ W := by omega
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₁ hs₁ => ?_)
  · simp [tblFitsList, TblIns.fits, hS, hK]; omega
  subst hs₁
  set s₁ := tblExactList A w ([.mul kS aK aU] ++ [.mod aU kT aU]) st with hs₁
  have hv₁ : s₁.val aU = s * k % t ∧ s₁.val 18 = piN p ∧ s₁.val 19 = p ∧
      s₁.val 21 = α * α * (t * t) ∧ s₁.val 22 = 1 ∧ s₁.val kT = t ∧ s₁.val kAl = α ∧
      s₁.val kZ = 0 ∧ s₁.val aM = m ∧ s₁.val aCnt = 2 * m + 1 ∧ s₁.acc = st.acc := by
    simp [hs₁, tblExactList, TblIns.exact, hS, hK, hT, h18, h19, h21, h22, hAl, hZ, hM, hCnt]
  obtain ⟨gU, g18, g19, g21, g22, gT, gAl, gZ, gM, gCnt, gacc⟩ := hv₁
  let Inv : ℕ → TblSt 48 A → Prop := fun i s' =>
    s'.acc = ((List.range i).flatMap (tblEntA A w s t α p m k)).reverse ++ st.acc ∧
    s'.val 18 = piN p ∧ s'.val 19 = p ∧ s'.val 21 = α * α * (t * t) ∧ s'.val 22 = 1 ∧
    s'.val kT = t ∧ s'.val kAl = α ∧ s'.val kZ = 0 ∧ s'.val aM = m ∧ s'.val aU = s * k % t
  refine TblDo.for (2 * m + 1) (310 * p + 107) gCnt h2m (by decide) Inv ?_ ?_ ?_
  · refine ⟨by simp [gacc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
      rw [Function.update_of_ne (by decide)] <;> assumption
  · intro i hi s' ⟨hacc', h18', h19', h21', h22', hT', hAl', hZ', hM', hU'⟩ hI' hCnt'
    refine (tblGaussBody_do s' h18' h19' h21' h22' hT' hAl' hZ' hM' hI' hU' hk hi hp hα
      hW).keep.mono (fun s'' ⟨hacc'', hkp⟩ => ?_) le_rfl
    refine ⟨by rw [hkp _ (by decide), hI'], by rw [hkp _ (by decide), hCnt'], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only; rw [hacc'', hacc', tbl_range_flatMap_succ, List.append_assoc]; rfl
    all_goals
      dsimp only
      rwa [Function.update_of_ne (by decide), hkp _ (by decide)]
  · intro s' ⟨hacc', _⟩ _ _
    exact hacc'

/-- The Gaussian stream of one axis: rows `k = 0, …, t − 1`, and in row `k` the window
`tblWinA s t m k` (`truncWindow s t m k` in increasing order), each entry `tableA k j` as a real
coefficient of width `w`. -/
def tblStreamA (A w s t α p m : ℕ) : List (Fin (A + 4)) :=
  (List.range t).flatMap fun k : ℕ => (tblWinA s t m k).flatMap fun j : ℤ =>
    coeffSyms A w (red w ⟨tableA s t α p (k : ZMod t) j, 0⟩)

theorem tblStreamA_eq (A w s t α p m : ℕ) : tblStreamA A w s t α p m =
    (List.range t).flatMap fun k : ℕ => (List.range (2 * m + 1)).flatMap (tblEntA A w s t α p m k) := by
  simp only [tblStreamA, tblWinA, List.flatMap_map]
  rfl

theorem length_tblStreamA (A w s t α p m : ℕ) :
    (tblStreamA A w s t α p m).length = t * (2 * m + 1) * w := by
  simp [tblStreamA, tblWinA, List.length_flatMap, List.sum_replicate, List.flatMap_map]
  ring

/-- **The Gaussian stream.** From `s`, `t`, `α`, `m` in variables `34, 35, 36, 39` and `p` in `19`,
with `13 ≤ p`, `2 ≤ α`, `0 < t` and `α² ((s + t)(m + 1))² 2^(13p+8) < 2^W`, `tblStreamACode`
emits `tblStreamA` within `t (2m + 1) (310 p + 110) + 8 t + 150 p + 420` atoms. -/
theorem tblStreamA_do {A W w : ℕ} (st : TblSt 48 A) {s t α p m : ℕ}
    (hs' : st.val 34 = s) (ht' : st.val 35 = t) (hα' : st.val 36 = α) (hm' : st.val 39 = m)
    (hp' : st.val 19 = p) (hp : 13 ≤ p) (hα : 2 ≤ α) (ht : 0 < t)
    (hW : α ^ 2 * ((s + t) * (m + 1)) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) :
    TblDo A W w tblStreamACode st (fun s' => s'.acc = (tblStreamA A w s t α p m).reverse ++ st.acc)
      (t * (2 * m + 1) * (310 * p + 110) + 8 * t + (150 * p + 420)) := by
  obtain ⟨hW1, hW2, hW3, hW4⟩ :=
    tbl_W_facts hα (Nat.mul_pos (Nat.add_pos_right s ht) (Nat.succ_pos m)) hW
  obtain ⟨N, hN⟩ : ∃ N, N = (s + t) * (m + 1) := ⟨_, rfl⟩
  rw [← hN] at hW3 hW4
  have hmN : m + 1 ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hsN : s + t ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hNN : N ≤ N * N := Nat.le_mul_self _
  have h4N : 4 * (N * N) < 2 ^ W :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by nlinarith)) hW4
  have hαα : α * α * (t * t) ≤ α * α * (N * N) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have hαα' : α * α ≤ α * α * (t * t) := Nat.le_mul_of_pos_right _ (by positivity)
  have htt : t * t ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  refine ((tbl_pi48_do (W := W) (w := w) st hp' (by omega) (by omega)).seq
    (K₂ := 8 + (1 + (t * (2 + (1 + ((2 * m + 1) * (310 * p + 107 + 1 + 2) + 2)) + 1 + 2) + 2)))
    (fun s₁ ⟨h18₁, hacc₁, hfr₁⟩ => ?_)).mono (fun _ h => h) (by nlinarith)
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₂ hs₂ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hfr₁ (36 : Fin 48) (by decide),
      hfr₁ (35 : Fin 48) (by decide), hfr₁ (39 : Fin 48) (by decide), hα', ht', hm']
    omega
  subst hs₂
  set s₂ := tblExactList A w ([.zero kZ, .zero 22, .inc 22, .mul kAl kAl aX, .mul kT kT aTmp,
    .mul aX aTmp 21, .add aM aM aCnt] ++ [.inc aCnt]) s₁ with hs₂
  have hv₂ : s₂.val 18 = piN p ∧ s₂.val 19 = p ∧ s₂.val 21 = α * α * (t * t) ∧ s₂.val 22 = 1 ∧
      s₂.val kS = s ∧ s₂.val kT = t ∧ s₂.val kAl = α ∧ s₂.val kZ = 0 ∧ s₂.val aM = m ∧
      s₂.val aCnt = 2 * m + 1 ∧ s₂.acc = st.acc := by
    simp [hs₂, tblExactList, TblIns.exact, h18₁, hfr₁ (19 : Fin 48) (by decide),
      hfr₁ (34 : Fin 48) (by decide), hfr₁ (35 : Fin 48) (by decide),
      hfr₁ (36 : Fin 48) (by decide), hfr₁ (39 : Fin 48) (by decide), hp', hs', ht', hα', hm',
      hacc₁]
    omega
  obtain ⟨g18, g19, g21, g22, gS, gT, gAl, gZ, gM, gCnt, gacc⟩ := hv₂
  let G : ℕ → List (Fin (A + 4)) := fun k =>
    (List.range (2 * m + 1)).flatMap (tblEntA A w s t α p m k)
  let Inv : ℕ → TblSt 48 A → Prop := fun k s' =>
    s'.acc = ((List.range k).flatMap G).reverse ++ st.acc ∧ s'.val 18 = piN p ∧
    s'.val 19 = p ∧ s'.val 21 = α * α * (t * t) ∧ s'.val 22 = 1 ∧ s'.val kS = s ∧
    s'.val kT = t ∧ s'.val kAl = α ∧ s'.val kZ = 0 ∧ s'.val aM = m ∧ s'.val aCnt = 2 * m + 1
  refine TblDo.for t (2 + (1 + ((2 * m + 1) * (310 * p + 107 + 1 + 2) + 2))) gT (by omega)
    (by decide) Inv ?_ ?_ ?_
  · refine ⟨by simp [gacc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
      rw [Function.update_of_ne (by decide)] <;> assumption
  · intro k hk s' ⟨hacc', h18', h19', h21', h22', hS', hT', hAl', hZ', hM', hCnt'⟩ hK' _
    refine (tblRowABody_do s' h18' h19' h21' h22' hS' hT' hAl' hZ' hM' hCnt' hK' hk hp hα
      hW).keep.mono (fun s'' ⟨hacc'', hkp⟩ => ?_) le_rfl
    refine ⟨by rw [hkp _ (by decide), hK'], by rw [hkp _ (by decide), hT'], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only; rw [hacc'', hacc', tbl_range_flatMap_succ G k, List.append_assoc]
    all_goals
      dsimp only
      rwa [Function.update_of_ne (by decide), hkp _ (by decide)]
  · intro s' ⟨hacc', _⟩ _ _
    rw [hacc', tblStreamA_eq]

/-! ### The off-diagonal table -/

theorem tbl_res_neg (s t n : ℕ) (hs : 0 < s) :
    TableIdx.res s t (-(n : ℤ)) = (s - t * n % s) % s := by
  unfold TableIdx.res
  have hdm := Nat.div_add_mod (t * n) s
  have hlt := Nat.mod_lt (t * n) hs
  have e : (t : ℤ) * -(n : ℤ) = ((s - t * n % s : ℕ) : ℤ) + (s : ℤ) * (-(((t * n / s : ℕ) : ℤ) + 1)) := by
    have : ((t * n : ℕ) : ℤ) = s * ((t * n / s : ℕ) : ℤ) + ((t * n % s : ℕ) : ℤ) := by
      exact_mod_cast hdm.symm
    push_cast [Nat.cast_sub hlt.le] at this ⊢
    linarith
  rw [e, Int.add_mul_emod_self_left, ← Int.natCast_mod, Int.toNat_natCast]

/-- `|t h + rr ℓ|` for `h = ±g`: `rr ℓ = u − [2u ≥ s] s` with `u = t ℓ mod s`. -/
def tblOffA (s t ℓ : ℕ) (neg : Bool) (g : ℕ) : ℕ :=
  let u := t * ℓ % s
  let cs := if u + u < s then 0 else s
  let P := if neg then u else t * g + u
  let M := if neg then t * g + cs else cs
  if P < M then M - P else P - M

/-- The residue `t (ℓ + h) mod s` for `h = ±g`. -/
def tblOffR (s t ℓ : ℕ) (neg : Bool) (g : ℕ) : ℕ :=
  if neg then (if g ≤ ℓ then t * (ℓ - g) % s else (s - t * (g - ℓ) % s) % s)
  else t * (ℓ + g) % s

/-- The exponent numerator of `tableE` divided by `α²`, in naturals. -/
def tblOffD (s t ℓ : ℕ) (neg : Bool) (g : ℕ) : ℕ :=
  tblOffA s t ℓ neg g * tblOffA s t ℓ neg g -
    tblCen s (tblOffR s t ℓ neg g) * tblCen s (tblOffR s t ℓ neg g)

theorem tbl_rr_sq_res (s t : ℕ) (x : ℤ) (hs : 0 < s) :
    (rr s t x) ^ 2 = ((tblCen s (TableIdx.res s t x) : ℕ) : ℤ) ^ 2 := by
  rw [TableIdx.rr_sq s t hs, tblCen]
  congr 3
  simp only [two_mul]

theorem tbl_absdiff_sq (P M : ℕ) :
    (((if P < M then M - P else P - M : ℕ) : ℤ)) ^ 2 = ((P : ℤ) - M) ^ 2 := by
  split_ifs with h
  · rw [Nat.cast_sub h.le]; ring
  · rw [Nat.cast_sub (not_lt.mp h)]

theorem tbl_offA_sq (s t ℓ : ℕ) (neg : Bool) (g : ℕ) (hs : 0 < s) :
    ((t : ℤ) * (if neg then -(g : ℤ) else g) + rr s t (ℓ : ℤ)) ^ 2 =
      ((tblOffA s t ℓ neg g : ℕ) : ℤ) ^ 2 := by
  rw [TableIdx.rr_eq s t hs, tbl_res_nat]
  unfold tblOffA
  simp only
  rw [tbl_absdiff_sq]
  cases neg <;> by_cases hc : t * ℓ % s + t * ℓ % s < s <;>
    simp [hc, show (2 * (t * ℓ % s) < s) ↔ (t * ℓ % s + t * ℓ % s < s) by omega] <;> ring

theorem tbl_offR_eq (s t ℓ : ℕ) (neg : Bool) (g : ℕ) (hs : 0 < s) :
    TableIdx.res s t ((ℓ : ℤ) + (if neg then -(g : ℤ) else g)) = tblOffR s t ℓ neg g := by
  unfold tblOffR
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (ℓ : ℤ) + g = ((ℓ + g : ℕ) : ℤ) by push_cast; ring, tbl_res_nat]
  · simp only [ite_true]
    split_ifs with h
    · rw [show (ℓ : ℤ) + -g = ((ℓ - g : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring, tbl_res_nat]
    · rw [show (ℓ : ℤ) + -g = -((g - ℓ : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : ℓ ≤ g)]; ring,
        tbl_res_neg s t _ hs]

theorem tbl_toNat_sq_sub (α A B : ℕ) :
    (((α : ℤ) ^ 2 * ((A : ℤ) ^ 2 - (B : ℤ) ^ 2)).toNat) = α * α * (A * A - B * B) := by
  by_cases h : B * B ≤ A * A
  · rw [show (α : ℤ) ^ 2 * ((A : ℤ) ^ 2 - (B : ℤ) ^ 2) = ((α * α * (A * A - B * B) : ℕ) : ℤ) by
      push_cast [Nat.cast_sub h]; ring, Int.toNat_natCast]
  · have h' : A * A - B * B = 0 := by omega
    rw [h', Nat.mul_zero]
    apply Int.toNat_eq_zero.mpr
    have : (A : ℤ) ^ 2 - (B : ℤ) ^ 2 ≤ 0 := by
      have : ((A * A : ℕ) : ℤ) ≤ ((B * B : ℕ) : ℤ) := by exact_mod_cast (not_le.mp h).le
      push_cast at this; nlinarith
    nlinarith [sq_nonneg (α : ℤ)]

/-- The off-diagonal table entry in naturals, for `h = ±g`. -/
theorem tbl_tableE_eq (s t α p ℓ g : ℕ) (neg : Bool) (hs : 0 < s) (hℓ : ℓ < s) (hp : 13 ≤ p) :
    tableE s t α p (ℓ : ZMod s) (if neg then -(g : ℤ) else g) =
      (expPiNat true p (α * α * tblOffD s t ℓ neg g) (s * s) : ℤ) := by
  rw [tableE_nat s t α p hp, WeightNat.tableENat, ZMod.val_natCast_of_lt hℓ, tbl_offA_sq s t ℓ neg g hs,
    tbl_rr_sq_res s t _ hs, tbl_offR_eq s t ℓ neg g hs, tbl_toNat_sq_sub, sq]
  rfl

/-- The off-diagonal window `−m, …, −1, 1, …, m` in increasing order. -/
def tblWinE (m : ℕ) : List ℤ :=
  (List.range m).map (fun i : ℕ => -((m - i : ℕ) : ℤ)) ++
    (List.range m).map (fun i : ℕ => ((i + 1 : ℕ) : ℤ))

theorem tblWinE_pairwise (m : ℕ) : (tblWinE m).Pairwise (· < ·) := by
  unfold tblWinE
  rw [List.pairwise_append, List.pairwise_map, List.pairwise_map]
  refine ⟨List.Pairwise.imp_of_mem (fun ha hb h => by simp only [List.mem_range] at ha hb; omega)
    List.pairwise_lt_range, List.pairwise_lt_range.imp (fun h => by omega), ?_⟩
  intro a ha b hb
  simp only [List.mem_map, List.mem_range] at ha hb
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  omega

theorem tblWinE_toFinset (m : ℕ) :
    (tblWinE m).toFinset = IntegerMultBounds.NLogN.offDiagWindow m := by
  ext h
  simp only [tblWinE, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_range,
    IntegerMultBounds.NLogN.mem_offDiagWindow]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> omega
  · intro ⟨h0, hm⟩
    rcases lt_or_gt_of_ne h0 with hn | hp
    · exact Or.inl ⟨m - h.natAbs, by omega, by omega⟩
    · exact Or.inr ⟨h.natAbs - 1, by omega, by omega⟩

local notation "eL" => (37 : Fin 48)
local notation "eM" => (39 : Fin 48)
local notation "eI" => (40 : Fin 48)
local notation "eU" => (41 : Fin 48)
local notation "eCS" => (42 : Fin 48)
local notation "eAA" => (43 : Fin 48)

/-- The common tail of an off-diagonal entry, from `A` in `27` and the residue `r` in `28`:
`B = cen r`, `D = A² − B²` (truncated), `a = α² D` into `20`, the weight routine, the emission. -/
def tblOffTail : TblCode 48 :=
  tblBlock 48 [] (.add 28 28 0) ;;
    .ite 0 kS (.ins (.copy 28 29)) (.ins (.sub kS 28 29)) ;;
    tblBlock 48 [.mul 27 27 30] (.mul 29 29 31) ;;
    .ite 30 31 (.ins (.zero 32)) (.ins (.sub 30 31 32)) ;;
    tblBlock 48 [] (.mul eAA 32 20) ;;
    tblExpCode.rename tblExpMap48 ;;
    tblBlock 48 [] (.emit 23 kZ)

theorem tblOffTail_do {A W w : ℕ} (st : TblSt 48 A) {s α p a0 R N : ℕ}
    (h18 : st.val 18 = piN p) (h19 : st.val 19 = p) (h21 : st.val 21 = s * s)
    (h22 : st.val 22 = 1) (hS : st.val kS = s) (hAA : st.val eAA = α * α) (hZ : st.val kZ = 0)
    (hA : st.val 27 = a0) (hR : st.val 28 = R) (hRs : R < s) (ha0 : a0 ≤ N) (hsN : s ≤ N)
    (hp : 13 ≤ p) (hW1 : 13 * p + 8 < W) (hW2 : α ^ 2 * N ^ 2 * 2 ^ (5 * p + 2) < 2 ^ W)
    (hW4 : α * α * (N * N) < 2 ^ W) (h4N : 4 * (N * N) < 2 ^ W) :
    TblDo A W w tblOffTail st (fun s' => s'.acc = (tblPairs A w (expPiNat true p
      (α * α * (a0 * a0 - tblCen s R * tblCen s R)) (s * s)) 0).reverse ++ st.acc)
      (310 * p + 112) := by
  have hfx : ∀ x : Fin 48, 34 ≤ x.val → ∀ y : Fin 34, tblExpMap48 y ≠ x := fun x hx =>
    tbl_castLE_ne _ x hx
  have hNN : N ≤ N * N := Nat.le_mul_self _
  have hcen : tblCen s R ≤ s := by unfold tblCen; split_ifs <;> omega
  have hBB : tblCen s R * tblCen s R ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  have hAA' : a0 * a0 ≤ N * N := Nat.mul_le_mul ha0 ha0
  obtain ⟨D, hD⟩ : ∃ D, D = a0 * a0 - tblCen s R * tblCen s R := ⟨_, rfl⟩
  have hDN : α * α * D ≤ α * α * (N * N) := Nat.mul_le_mul_left _ (by omega)
  -- `r + r`
  refine (TblDo.block _ _ (by simp [tblFitsList, TblIns.fits, hR]; omega) rfl).seq
    (K₂ := 2 + (2 + (2 + (1 + (310 * p + 100 + 1))))) (fun s₁ hs₁ => ?_) |>.mono (fun _ h => h)
    (by simp; omega)
  subst hs₁
  set s₁ := tblExactList A w ([] ++ [.add 28 28 0]) st with hs₁
  have hv₁ : s₁.val 0 = R + R ∧ s₁.val kS = s ∧ s₁.val 28 = R ∧ s₁.val 27 = a0 := by
    simp [hs₁, tblExactList, TblIns.exact, hR, hS, hA]
  obtain ⟨f0, fS, fR, fA⟩ := hv₁
  -- `B = cen r`
  have hcenC : TblDo A W w (.ite 0 kS (.ins (.copy 28 29)) (.ins (.sub kS 28 29))) s₁
      (fun s₂ => s₂ = ⟨Function.update s₁.val 29 (tblCen s R), s₁.acc⟩) 2 := by
    by_cases hc : R + R < s
    · refine TblDo.iteT (by rw [f0, fS]; exact hc) (TblDo.insX _ (by trivial) ?_)
      simp [TblIns.exact, fR, tblCen, hc]
    · refine TblDo.iteF (by rw [f0, fS]; exact hc) (TblDo.insX _ ?_ ?_)
      · simp only [TblIns.fits, fS, fR]; omega
      · simp [TblIns.exact, fR, fS, tblCen, hc]
  refine hcenC.seq (fun s₂ hs₂ => ?_)
  subst hs₂
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₃ hs₃ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, fA]; omega
  subst hs₃
  set s₃ := tblExactList A w ([.mul 27 27 30] ++ [.mul 29 29 31])
    ⟨Function.update s₁.val 29 (tblCen s R), s₁.acc⟩ with hs₃
  have hv₃ : s₃.val 30 = a0 * a0 ∧ s₃.val 31 = tblCen s R * tblCen s R := by
    simp [hs₃, tblExactList, TblIns.exact, fA]
  obtain ⟨f30, f31⟩ := hv₃
  have hDC : TblDo A W w (.ite 30 31 (.ins (.zero 32)) (.ins (.sub 30 31 32))) s₃
      (fun s₄ => s₄ = ⟨Function.update s₃.val 32 D, s₃.acc⟩) 2 := by
    by_cases hc : a0 * a0 < tblCen s R * tblCen s R
    · refine TblDo.iteT (by rw [f30, f31]; exact hc) (TblDo.insX _ (by trivial) ?_)
      simp [TblIns.exact, hD, Nat.sub_eq_zero_of_le hc.le]
    · refine TblDo.iteF (by rw [f30, f31]; exact hc) (TblDo.insX _ ?_ ?_)
      · simp only [TblIns.fits, f30, f31]; omega
      · simp [TblIns.exact, f30, f31, hD]
  refine hDC.seq (fun s₄ hs₄ => ?_)
  subst hs₄
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₅ hs₅ => ?_)
  · simp [tblFitsList, TblIns.fits, hs₃, hs₁, tblExactList, TblIns.exact, hAA]; omega
  subst hs₅
  set s₅ := tblExactList A w ([] ++ [.mul eAA 32 20]) ⟨Function.update s₃.val 32 D, s₃.acc⟩
    with hs₅
  have hv₅ : s₅.val 18 = piN p ∧ s₅.val 19 = p ∧ s₅.val 20 = α * α * D ∧ s₅.val 21 = s * s ∧
      s₅.val 22 = 1 ∧ s₅.val kZ = 0 ∧ s₅.acc = st.acc := by
    simp [hs₅, hs₃, hs₁, tblExactList, TblIns.exact, h18, h19, h21, h22, hAA, hZ]
  obtain ⟨g18, g19, g20, g21, g22, gZ, gacc⟩ := hv₅
  have hexp := (tblExp_do (A := A) (W := W) (w := w) (s₅.restrict tblExpMap48) (p := p)
    (a := α * α * D) (b := s * s) true g18 g19 g20 g21 (by simp only [ite_true]; exact g22) hp
    (by omega) (lt_of_le_of_lt (Nat.mul_le_mul_right _ (by rw [sq, sq]; exact hDN)) hW2)
    (fun h => absurd h (by decide))).rename (Fin.castLE_injective _)
  refine hexp.seq (K₂ := 1) (fun s₆ ⟨⟨hres, _, _, _, _, _, hacc₆⟩, hfr₆⟩ => ?_)
  have hres' : s₆.val 23 = expPiNat true p (α * α * D) (s * s) := hres
  have hacc₆' : s₆.acc = s₅.acc := hacc₆
  have hZ₆ : s₆.val kZ = 0 := by rw [hfr₆ _ (hfx _ (by decide)), gZ]
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  simp [tblExactList, TblIns.exact, hres', hZ₆, hacc₆', gacc, hD]

/-- `A := |P − M|` from `P` in `25` and `M` in `26`. -/
def tblAbsDiff : TblCode 48 := .ite 25 26 (.ins (.sub 26 25 27)) (.ins (.sub 25 26 27))

theorem tblAbsDiff_do {A W w : ℕ} (st : TblSt 48 A) {P M : ℕ} (hP : st.val 25 = P)
    (hM : st.val 26 = M) (hPW : P < 2 ^ W) (hMW : M < 2 ^ W) :
    TblDo A W w tblAbsDiff st
      (fun s => s = ⟨Function.update st.val 27 (if P < M then M - P else P - M), st.acc⟩) 2 := by
  by_cases hc : P < M
  · refine TblDo.iteT (by rw [hP, hM]; exact hc) (TblDo.insX _ ?_ ?_)
    · simp only [TblIns.fits, hP, hM]; omega
    · simp [TblIns.exact, hP, hM, hc]
  · refine TblDo.iteF (by rw [hP, hM]; exact hc) (TblDo.insX _ ?_ ?_)
    · simp only [TblIns.fits, hP, hM]; omega
    · simp [TblIns.exact, hP, hM, hc]

/-- The entry `h = −(m − i)` of row `ℓ`. -/
def tblOffNegBody : TblCode 48 :=
  tblBlock 48 [.sub eM eI 24, .mul kT 24 33, .copy eU 25] (.add 33 eCS 26) ;; tblAbsDiff ;;
    .ite eL 24 (tblBlock 48 [.sub 24 eL 0, .mul kT 0 1, .mod 1 kS 1, .sub kS 1 28] (.mod 28 kS 28))
      (tblBlock 48 [.sub eL 24 0, .mul kT 0 1] (.mod 1 kS 28)) ;;
    tblOffTail

/-- The entry `h = i + 1` of row `ℓ`. -/
def tblOffPosBody : TblCode 48 :=
  tblBlock 48 [.copy eI 24, .inc 24, .mul kT 24 33, .add 33 eU 25] (.copy eCS 26) ;; tblAbsDiff ;;
    tblBlock 48 [.add eL 24 0, .mul kT 0 1] (.mod 1 kS 28) ;;
    tblOffTail

/-- The off-diagonal entry `(ℓ, h)` as a coefficient. -/
def tblEntE (A w s t α p ℓ : ℕ) (h : ℤ) : List (Fin (A + 4)) :=
  coeffSyms A w (red w ⟨tableE s t α p (ℓ : ZMod s) h, 0⟩)

/-- The facts on the word size used by the off-diagonal bodies. -/
structure TblOffW (W p α s t m N : ℕ) : Prop where
  hN : N = (s + t) * (m + 1)
  h1 : 13 * p + 8 < W
  h2 : α ^ 2 * N ^ 2 * 2 ^ (5 * p + 2) < 2 ^ W
  h4 : α * α * (N * N) < 2 ^ W
  h4N : 4 * (N * N) < 2 ^ W

theorem tblOffW_of {W p α s t m : ℕ} (hα : 2 ≤ α) (hst : 0 < s + t)
    (hW : α ^ 2 * ((s + t) * (m + 1)) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) :
    TblOffW W p α s t m ((s + t) * (m + 1)) := by
  obtain ⟨hW1, hW2, _, hW4⟩ := tbl_W_facts hα (Nat.mul_pos hst (Nat.succ_pos m)) hW
  exact ⟨rfl, hW1, hW2, hW4, lt_of_le_of_lt (Nat.mul_le_mul_right _ (by nlinarith)) hW4⟩

theorem tblOffNegBody_do {A W w : ℕ} (st : TblSt 48 A) {s t α p m ℓ i N : ℕ}
    (h18 : st.val 18 = piN p) (h19 : st.val 19 = p) (h21 : st.val 21 = s * s)
    (h22 : st.val 22 = 1) (hS : st.val kS = s) (hT : st.val kT = t) (hAA : st.val eAA = α * α)
    (hZ : st.val kZ = 0) (hM : st.val eM = m) (hI : st.val eI = i) (hL : st.val eL = ℓ)
    (hU : st.val eU = t * ℓ % s) (hCS : st.val eCS = if t * ℓ % s + t * ℓ % s < s then 0 else s)
    (hi : i < m) (hℓ : ℓ < s) (hp : 13 ≤ p) (hW : TblOffW W p α s t m N) :
    TblDo A W w tblOffNegBody st (fun s' => s'.acc =
      (tblEntE A w s t α p ℓ (-((m - i : ℕ) : ℤ))).reverse ++ st.acc) (310 * p + 124) := by
  obtain ⟨hN, hW1, hW2, hW4, h4N⟩ := hW
  have hs : 0 < s := by omega
  have hNe : N = s * m + s + t * m + t := by rw [hN]; ring
  have hNN : N ≤ N * N := Nat.le_mul_self _
  have hmN : m + 1 ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨g, hg⟩ : ∃ g, g = m - i := ⟨_, rfl⟩
  have hgm : g ≤ m := by omega
  have htg : t * g ≤ t * m := Nat.mul_le_mul_left _ hgm
  obtain ⟨u, hu⟩ : ∃ u, u = t * ℓ % s := ⟨_, rfl⟩
  have hus : u < s := hu ▸ Nat.mod_lt _ hs
  rw [← hu] at hU hCS
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = if u + u < s then 0 else s := ⟨_, rfl⟩
  rw [← hcs] at hCS
  have hcsl : cs ≤ s := by rw [hcs]; split_ifs <;> omega
  -- `g`, `t g`, `P = u`, `M = t g + cs`
  refine (TblDo.block _ _ ?_ rfl).seq (K₂ := 2 + (6 + (310 * p + 112))) (fun s₁ hs₁ => ?_)
    |>.mono (fun _ h => h) (by simp; omega)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hM, hI, hT, hCS, ← hg]
    omega
  subst hs₁
  set s₁ := tblExactList A w ([.sub eM eI 24, .mul kT 24 33, .copy eU 25] ++ [.add 33 eCS 26]) st
    with hs₁
  have hv₁ : s₁.val 24 = g ∧ s₁.val 25 = u ∧ s₁.val 26 = t * g + cs := by
    simp [hs₁, tblExactList, TblIns.exact, hM, hI, hT, hU, hCS, ← hg]
  obtain ⟨f24, f25, f26⟩ := hv₁
  refine (tblAbsDiff_do s₁ f25 f26 (by omega) (by omega)).seq (fun s₂ hs₂ => ?_)
  subst hs₂
  obtain ⟨a0, ha0⟩ : ∃ a0, a0 = tblOffA s t ℓ true g := ⟨_, rfl⟩
  have ha0' : (if u < t * g + cs then t * g + cs - u else u - (t * g + cs)) = a0 := by
    rw [ha0, tblOffA, ← hu, ← hcs]; rfl
  have ha0N : a0 ≤ N := by rw [← ha0']; split_ifs <;> omega
  obtain ⟨R, hR⟩ : ∃ R, R = tblOffR s t ℓ true g := ⟨_, rfl⟩
  have hRs : R < s := by
    rw [hR, tblOffR]; simp only [ite_true]; split_ifs <;> exact Nat.mod_lt _ hs
  set s₂ : TblSt 48 A := ⟨Function.update s₁.val 27
    (if u < t * g + cs then t * g + cs - u else u - (t * g + cs)), s₁.acc⟩ with hs₂
  have hv₂ : s₂.val 24 = g ∧ s₂.val eL = ℓ ∧ s₂.val kT = t ∧ s₂.val kS = s := by
    simp [hs₂, hs₁, tblExactList, TblIns.exact, hM, hI, hT, hL, hS, ← hg]
  obtain ⟨e24, eL₂, eT, eS⟩ := hv₂
  have hres : TblDo A W w (.ite eL 24
      (tblBlock 48 [.sub 24 eL 0, .mul kT 0 1, .mod 1 kS 1, .sub kS 1 28] (.mod 28 kS 28))
      (tblBlock 48 [.sub eL 24 0, .mul kT 0 1] (.mod 1 kS 28))) s₂
      (fun s₃ => s₃.val 28 = R ∧ s₃.val 27 = a0 ∧ s₃.val 18 = piN p ∧ s₃.val 19 = p ∧
        s₃.val 21 = s * s ∧ s₃.val 22 = 1 ∧ s₃.val kS = s ∧ s₃.val eAA = α * α ∧
        s₃.val kZ = 0 ∧ s₃.acc = st.acc) 6 := by
    have hcom : s₂.val 27 = a0 ∧ s₂.val 18 = piN p ∧ s₂.val 19 = p ∧ s₂.val 21 = s * s ∧
        s₂.val 22 = 1 ∧ s₂.val eAA = α * α ∧ s₂.val kZ = 0 ∧ s₂.acc = st.acc := by
      simp [hs₂, hs₁, tblExactList, TblIns.exact, ha0', h18, h19, h21, h22, hAA, hZ]
    obtain ⟨c27, c18, c19, c21, c22, cAA, cZ, cacc⟩ := hcom
    by_cases hc : ℓ < g
    · have hx : t * (g - ℓ) ≤ t * m := Nat.mul_le_mul_left _ (by omega)
      have hy := Nat.mod_lt (t * (g - ℓ)) hs
      refine TblDo.iteT (by rw [eL₂, e24]; exact hc) (TblDo.block _ _ ?_ ?_)
      · simp [tblFitsList, TblIns.fits, TblIns.exact, e24, eL₂, eT, eS]; omega
      · simp [tblExactList, TblIns.exact, e24, eL₂, eT, eS, c27, c18, c19, c21, c22, cAA, cZ, cacc,
          hR, tblOffR, show ¬ g ≤ ℓ by omega]
    · have hx : t * (ℓ - g) ≤ t * s := Nat.mul_le_mul_left _ (by omega)
      have hts : t * s ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
      refine TblDo.iteF (by rw [eL₂, e24]; exact hc) ((TblDo.block _ _ ?_ ?_).mono (fun _ h => h)
        (by simp))
      · simp [tblFitsList, TblIns.fits, TblIns.exact, e24, eL₂, eT]; omega
      · simp [tblExactList, TblIns.exact, e24, eL₂, eT, eS, c27, c18, c19, c21, c22, cAA, cZ, cacc,
          hR, tblOffR, show g ≤ ℓ by omega]
  refine hres.seq (fun s₃ ⟨g28, g27, g18, g19, g21, g22, gS, gAA, gZ, gacc⟩ => ?_)
  refine (tblOffTail_do s₃ g18 g19 g21 g22 gS gAA gZ g27 g28 hRs ha0N (by omega) hp hW1 hW2 hW4
    h4N).mono (fun s' h => ?_) le_rfl
  have hh : (-((m - i : ℕ) : ℤ)) = (if true then -(g : ℤ) else g) := by simp [hg]
  rw [h, gacc, tbl_pairs_red, tblEntE, hh, tbl_tableE_eq s t α p ℓ g true hs hℓ hp]
  simp only [tblOffD, ← ha0, ← hR]

theorem tblOffPosBody_do {A W w : ℕ} (st : TblSt 48 A) {s t α p m ℓ i N : ℕ}
    (h18 : st.val 18 = piN p) (h19 : st.val 19 = p) (h21 : st.val 21 = s * s)
    (h22 : st.val 22 = 1) (hS : st.val kS = s) (hT : st.val kT = t) (hAA : st.val eAA = α * α)
    (hZ : st.val kZ = 0) (hI : st.val eI = i) (hL : st.val eL = ℓ)
    (hU : st.val eU = t * ℓ % s) (hCS : st.val eCS = if t * ℓ % s + t * ℓ % s < s then 0 else s)
    (hi : i < m) (hℓ : ℓ < s) (hp : 13 ≤ p) (hW : TblOffW W p α s t m N) :
    TblDo A W w tblOffPosBody st (fun s' => s'.acc =
      (tblEntE A w s t α p ℓ ((i + 1 : ℕ) : ℤ)).reverse ++ st.acc) (310 * p + 122) := by
  obtain ⟨hN, hW1, hW2, hW4, h4N⟩ := hW
  have hs : 0 < s := by omega
  have hNe : N = s * m + s + t * m + t := by rw [hN]; ring
  have hNN : N ≤ N * N := Nat.le_mul_self _
  have hmN : m + 1 ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hsm : m ≤ s * m := Nat.le_mul_of_pos_left _ hs
  obtain ⟨g, hg⟩ : ∃ g, g = i + 1 := ⟨_, rfl⟩
  have hgm : g ≤ m := by omega
  have htg : t * g ≤ t * m := Nat.mul_le_mul_left _ hgm
  obtain ⟨u, hu⟩ : ∃ u, u = t * ℓ % s := ⟨_, rfl⟩
  have hus : u < s := hu ▸ Nat.mod_lt _ hs
  rw [← hu] at hU hCS
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = if u + u < s then 0 else s := ⟨_, rfl⟩
  rw [← hcs] at hCS
  have hcsl : cs ≤ s := by rw [hcs]; split_ifs <;> omega
  have htl : t * (ℓ + g) ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  refine (TblDo.block _ _ ?_ rfl).seq (K₂ := 2 + (3 + (310 * p + 112))) (fun s₁ hs₁ => ?_)
    |>.mono (fun _ h => h) (by simp; omega)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hI, hT, hU, ← hg]
    omega
  subst hs₁
  set s₁ := tblExactList A w ([.copy eI 24, .inc 24, .mul kT 24 33, .add 33 eU 25] ++
    [.copy eCS 26]) st with hs₁
  have hv₁ : s₁.val 24 = g ∧ s₁.val 25 = t * g + u ∧ s₁.val 26 = cs := by
    simp [hs₁, tblExactList, TblIns.exact, hI, hT, hU, hCS, ← hg]
  obtain ⟨f24, f25, f26⟩ := hv₁
  refine (tblAbsDiff_do s₁ f25 f26 (by omega) (by omega)).seq (fun s₂ hs₂ => ?_)
  subst hs₂
  obtain ⟨a0, ha0⟩ : ∃ a0, a0 = tblOffA s t ℓ false g := ⟨_, rfl⟩
  have ha0' : (if t * g + u < cs then cs - (t * g + u) else t * g + u - cs) = a0 := by
    rw [ha0, tblOffA, ← hu, ← hcs]; rfl
  have ha0N : a0 ≤ N := by rw [← ha0']; split_ifs <;> omega
  obtain ⟨R, hR⟩ : ∃ R, R = tblOffR s t ℓ false g := ⟨_, rfl⟩
  have hRs : R < s := by rw [hR, tblOffR]; exact Nat.mod_lt _ hs
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₃ hs₃ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hs₁, tblExactList, hI, hT, hL, ← hg]
    omega
  subst hs₃
  have hv₃ : ∀ s₃ : TblSt 48 A, s₃ = tblExactList A w ([.add eL 24 0, .mul kT 0 1] ++
      [.mod 1 kS 28]) ⟨Function.update s₁.val 27
        (if t * g + u < cs then cs - (t * g + u) else t * g + u - cs), s₁.acc⟩ →
      s₃.val 28 = R ∧ s₃.val 27 = a0 ∧ s₃.val 18 = piN p ∧ s₃.val 19 = p ∧
        s₃.val 21 = s * s ∧ s₃.val 22 = 1 ∧ s₃.val kS = s ∧ s₃.val eAA = α * α ∧
        s₃.val kZ = 0 ∧ s₃.acc = st.acc := by
    intro s₃ hs₃
    subst hs₃
    simp [hs₁, tblExactList, TblIns.exact, hI, hT, hL, hS, ha0', h18, h19, h21, h22, hAA, hZ, hR,
      tblOffR, ← hg]
  obtain ⟨g28, g27, g18, g19, g21, g22, gS, gAA, gZ, gacc⟩ := hv₃ _ rfl
  refine (tblOffTail_do _ g18 g19 g21 g22 gS gAA gZ g27 g28 hRs ha0N (by omega) hp hW1 hW2 hW4
    h4N).mono (fun s' h => ?_) le_rfl
  have hh : ((i + 1 : ℕ) : ℤ) = (if false then -(g : ℤ) else g) := by simp [hg]
  rw [h, gacc, tbl_pairs_red, tblEntE, hh, tbl_tableE_eq s t α p ℓ g false hs hℓ hp]
  simp only [tblOffD, ← ha0, ← hR]

/-- Row `ℓ` (in `eL`) of the off-diagonal table: `u = t ℓ mod s`, `cs = [2u ≥ s] s`, then the
entries `h = −m, …, −1` and `h = 1, …, m`. -/
def tblRowEBody : TblCode 48 :=
  tblBlock 48 [.mul kT eL eU, .mod eU kS eU] (.add eU eU 0) ;;
    .ite 0 kS (.ins (.zero eCS)) (.ins (.copy kS eCS)) ;;
    tblFor eI eM tblOffNegBody ;; tblFor eI eM tblOffPosBody

/-- The off-diagonal stream program: `s`, `t`, `α`, `m` in variables `34, 35, 36, 39`, `p` in
`19`. -/
def tblStreamECode : TblCode 48 :=
  tblPiSetup48 ;;
    tblBlock 48 [.zero kZ, .zero 22, .inc 22, .mul kS kS 21] (.mul kAl kAl eAA) ;;
    tblFor eL kS tblRowEBody

theorem tblRowEBody_do {A W w : ℕ} (st : TblSt 48 A) {s t α p m ℓ N : ℕ}
    (h18 : st.val 18 = piN p) (h19 : st.val 19 = p) (h21 : st.val 21 = s * s)
    (h22 : st.val 22 = 1) (hS : st.val kS = s) (hT : st.val kT = t) (hAA : st.val eAA = α * α)
    (hZ : st.val kZ = 0) (hM : st.val eM = m) (hL : st.val eL = ℓ) (hℓ : ℓ < s) (hp : 13 ≤ p)
    (hW : TblOffW W p α s t m N) :
    TblDo A W w tblRowEBody st (fun s' => s'.acc =
      ((List.range m).flatMap (fun i => tblEntE A w s t α p ℓ (-((m - i : ℕ) : ℤ))) ++
        (List.range m).flatMap (fun i => tblEntE A w s t α p ℓ ((i + 1 : ℕ) : ℤ))).reverse ++
        st.acc)
      (3 + (2 + ((1 + (m * (310 * p + 124 + 1 + 2) + 2)) +
        (1 + (m * (310 * p + 122 + 1 + 2) + 2))))) := by
  have hW' := hW
  obtain ⟨hN, hW1, hW2, hW4, h4N⟩ := hW'
  have hs : 0 < s := by omega
  have hNN : N ≤ N * N := Nat.le_mul_self _
  have hmN : m + 1 ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hsN : s + t ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
  have htl : t * ℓ ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  have hus := Nat.mod_lt (t * ℓ) hs
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₁ hs₁ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hT, hL, hS]; omega
  subst hs₁
  set s₁ := tblExactList A w ([.mul kT eL eU, .mod eU kS eU] ++ [.add eU eU 0]) st with hs₁
  have hv₁ : s₁.val 0 = t * ℓ % s + t * ℓ % s ∧ s₁.val kS = s ∧ s₁.val eU = t * ℓ % s := by
    simp [hs₁, tblExactList, TblIns.exact, hT, hL, hS]
  obtain ⟨f0, fS, fU⟩ := hv₁
  have hcs : TblDo A W w (.ite 0 kS (.ins (.zero eCS)) (.ins (.copy kS eCS))) s₁
      (fun s₂ => s₂ = ⟨Function.update s₁.val eCS
        (if t * ℓ % s + t * ℓ % s < s then 0 else s), s₁.acc⟩) 2 := by
    by_cases hc : t * ℓ % s + t * ℓ % s < s
    · exact TblDo.iteT (by rw [f0, fS]; exact hc) (TblDo.insX _ (by trivial) (by simp [TblIns.exact, hc]))
    · exact TblDo.iteF (by rw [f0, fS]; exact hc)
        (TblDo.insX _ (by trivial) (by simp [TblIns.exact, hc, fS]))
  refine hcs.seq (fun s₂ hs₂ => ?_)
  subst hs₂
  set s₂ : TblSt 48 A := ⟨Function.update s₁.val eCS
    (if t * ℓ % s + t * ℓ % s < s then 0 else s), s₁.acc⟩ with hs₂
  have hv₂ : s₂.val 18 = piN p ∧ s₂.val 19 = p ∧ s₂.val 21 = s * s ∧ s₂.val 22 = 1 ∧
      s₂.val kS = s ∧ s₂.val kT = t ∧ s₂.val eAA = α * α ∧ s₂.val kZ = 0 ∧ s₂.val eM = m ∧
      s₂.val eL = ℓ ∧ s₂.val eU = t * ℓ % s ∧
      s₂.val eCS = (if t * ℓ % s + t * ℓ % s < s then 0 else s) ∧ s₂.acc = st.acc := by
    simp [hs₂, hs₁, tblExactList, TblIns.exact, h18, h19, h21, h22, hS, hT, hAA, hZ, hM, hL]
  obtain ⟨g18, g19, g21, g22, gS, gT, gAA, gZ, gM, gL, gU, gCS, gacc⟩ := hv₂
  let Fn : ℕ → List (Fin (A + 4)) := fun i => tblEntE A w s t α p ℓ (-((m - i : ℕ) : ℤ))
  let Fp : ℕ → List (Fin (A + 4)) := fun i => tblEntE A w s t α p ℓ ((i + 1 : ℕ) : ℤ)
  let Inv : List (Fin (A + 4)) → (ℕ → List (Fin (A + 4))) → ℕ → TblSt 48 A → Prop :=
    fun pre F i s' => s'.acc = ((List.range i).flatMap F).reverse ++ pre ∧ s'.val 18 = piN p ∧
      s'.val 19 = p ∧ s'.val 21 = s * s ∧ s'.val 22 = 1 ∧ s'.val kS = s ∧ s'.val kT = t ∧
      s'.val eAA = α * α ∧ s'.val kZ = 0 ∧ s'.val eL = ℓ ∧ s'.val eU = t * ℓ % s ∧
      s'.val eCS = (if t * ℓ % s + t * ℓ % s < s then 0 else s)
  have hmW : m < 2 ^ W := by omega
  refine (TblDo.for (P := fun s => Inv st.acc Fn m s ∧ s.val eM = m) m (310 * p + 124) gM hmW
    (by decide) (Inv st.acc Fn) ?_ ?_ ?_).seq (fun s₃ ⟨⟨h3acc, h3⟩, hM₃⟩ => ?_)
  · refine ⟨by simp [gacc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
      rw [Function.update_of_ne (by decide)] <;> assumption
  · intro i hi s' ⟨hacc', h18', h19', h21', h22', hS', hT', hAA', hZ', hL', hU', hCS'⟩ hI' hM'
    refine (tblOffNegBody_do s' h18' h19' h21' h22' hS' hT' hAA' hZ' hM' hI' hL' hU' hCS' hi hℓ hp
      hW).keep.mono (fun s'' ⟨hacc'', hkp⟩ => ?_) le_rfl
    refine ⟨by rw [hkp _ (by decide), hI'], by rw [hkp _ (by decide), hM'], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show _ = _; rw [hacc'', hacc', tbl_range_flatMap_succ Fn i, List.append_assoc]
    all_goals
      dsimp only
      rwa [Function.update_of_ne (by decide), hkp _ (by decide)]
  · intro s' h _ hM'
    exact ⟨h, hM'⟩
  obtain ⟨h18', h19', h21', h22', hS', hT', hAA', hZ', hL', hU', hCS'⟩ := h3
  refine (TblDo.for m (310 * p + 122) hM₃ hmW (by decide)
    (Inv (((List.range m).flatMap Fn).reverse ++ st.acc) Fp) ?_ ?_ ?_)
  · refine ⟨by simp [h3acc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
      rw [Function.update_of_ne (by decide)] <;> assumption
  · intro i hi s' ⟨hacc', h18', h19', h21', h22', hS', hT', hAA', hZ', hL', hU', hCS'⟩ hI' hM'
    refine (tblOffPosBody_do s' h18' h19' h21' h22' hS' hT' hAA' hZ' hI' hL' hU' hCS' hi hℓ hp
      hW).keep.mono (fun s'' ⟨hacc'', hkp⟩ => ?_) le_rfl
    refine ⟨by rw [hkp _ (by decide), hI'], by rw [hkp _ (by decide), hM'], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show _ = _; rw [hacc'', hacc', tbl_range_flatMap_succ Fp i, List.append_assoc]
    all_goals
      dsimp only
      rwa [Function.update_of_ne (by decide), hkp _ (by decide)]
  · intro s' ⟨hacc', _⟩ _ _
    rw [hacc', List.reverse_append, List.append_assoc]

/-- The off-diagonal stream of one axis: rows `ℓ = 0, …, s − 1`, and in row `ℓ` the window
`tblWinE m` (`offDiagWindow m` in increasing order), each entry `tableE ℓ h` as a real
coefficient of width `w`. -/
def tblStreamE (A w s t α p m : ℕ) : List (Fin (A + 4)) :=
  (List.range s).flatMap fun ℓ : ℕ => (tblWinE m).flatMap fun h : ℤ =>
    coeffSyms A w (red w ⟨tableE s t α p (ℓ : ZMod s) h, 0⟩)

theorem tblStreamE_eq (A w s t α p m : ℕ) : tblStreamE A w s t α p m =
    (List.range s).flatMap fun ℓ : ℕ =>
      (List.range m).flatMap (fun i => tblEntE A w s t α p ℓ (-((m - i : ℕ) : ℤ))) ++
        (List.range m).flatMap (fun i => tblEntE A w s t α p ℓ ((i + 1 : ℕ) : ℤ)) := by
  simp only [tblStreamE, tblWinE, List.flatMap_append, List.flatMap_map]
  rfl

theorem length_tblStreamE (A w s t α p m : ℕ) :
    (tblStreamE A w s t α p m).length = s * (2 * m) * w := by
  simp [tblStreamE, tblWinE, List.length_flatMap, List.sum_replicate, List.flatMap_map]
  ring

/-- **The off-diagonal stream.** From `s`, `t`, `α`, `m` in variables `34, 35, 36, 39` and `p` in
`19`, with `13 ≤ p`, `2 ≤ α`, `0 < s` and `α² ((s + t)(m + 1))² 2^(13p+8) < 2^W`,
`tblStreamECode` emits `tblStreamE` within `s (2m) (310 p + 126) + 14 s + 150 p + 420` atoms. -/
theorem tblStreamE_do {A W w : ℕ} (st : TblSt 48 A) {s t α p m : ℕ}
    (hs' : st.val 34 = s) (ht' : st.val 35 = t) (hα' : st.val 36 = α) (hm' : st.val 39 = m)
    (hp' : st.val 19 = p) (hp : 13 ≤ p) (hα : 2 ≤ α) (hs : 0 < s)
    (hW : α ^ 2 * ((s + t) * (m + 1)) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) :
    TblDo A W w tblStreamECode st (fun s' => s'.acc = (tblStreamE A w s t α p m).reverse ++ st.acc)
      (s * (2 * m) * (310 * p + 126) + 14 * s + (150 * p + 420)) := by
  have hOW := tblOffW_of hα (by omega : 0 < s + t) hW
  have hOW' := hOW
  obtain ⟨hN, hW1, hW2, hW4, h4N⟩ := hOW'
  set N := (s + t) * (m + 1)
  have hNN : N ≤ N * N := Nat.le_mul_self _
  have hsN : s + t ≤ N := Nat.le_mul_of_pos_right _ (by omega)
  have hss : s * s ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  have hαα : α * α ≤ α * α * (N * N) := Nat.le_mul_of_pos_right _ (by positivity)
  refine ((tbl_pi48_do (W := W) (w := w) st hp' (by omega) (by omega)).seq
    (K₂ := 5 + (1 + (s * (3 + (2 + ((1 + (m * (310 * p + 124 + 1 + 2) + 2)) +
        (1 + (m * (310 * p + 122 + 1 + 2) + 2)))) + 1 + 2) + 2)))
    (fun s₁ ⟨h18₁, hacc₁, hfr₁⟩ => ?_)).mono (fun _ h => h) (by nlinarith)
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₂ hs₂ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hfr₁ (34 : Fin 48) (by decide),
      hfr₁ (36 : Fin 48) (by decide), hs', hα']
    omega
  subst hs₂
  set s₂ := tblExactList A w ([.zero kZ, .zero 22, .inc 22, .mul kS kS 21] ++ [.mul kAl kAl eAA])
    s₁ with hs₂
  have hv₂ : s₂.val 18 = piN p ∧ s₂.val 19 = p ∧ s₂.val 21 = s * s ∧ s₂.val 22 = 1 ∧
      s₂.val kS = s ∧ s₂.val kT = t ∧ s₂.val eAA = α * α ∧ s₂.val kZ = 0 ∧ s₂.val eM = m ∧
      s₂.acc = st.acc := by
    simp [hs₂, tblExactList, TblIns.exact, h18₁, hfr₁ (19 : Fin 48) (by decide),
      hfr₁ (34 : Fin 48) (by decide), hfr₁ (35 : Fin 48) (by decide),
      hfr₁ (36 : Fin 48) (by decide), hfr₁ (39 : Fin 48) (by decide), hp', hs', ht', hα', hm',
      hacc₁]
  obtain ⟨g18, g19, g21, g22, gS, gT, gAA, gZ, gM, gacc⟩ := hv₂
  let G : ℕ → List (Fin (A + 4)) := fun ℓ =>
    (List.range m).flatMap (fun i => tblEntE A w s t α p ℓ (-((m - i : ℕ) : ℤ))) ++
      (List.range m).flatMap (fun i => tblEntE A w s t α p ℓ ((i + 1 : ℕ) : ℤ))
  let Inv : ℕ → TblSt 48 A → Prop := fun ℓ s' =>
    s'.acc = ((List.range ℓ).flatMap G).reverse ++ st.acc ∧ s'.val 18 = piN p ∧
    s'.val 19 = p ∧ s'.val 21 = s * s ∧ s'.val 22 = 1 ∧ s'.val kS = s ∧ s'.val kT = t ∧
    s'.val eAA = α * α ∧ s'.val kZ = 0 ∧ s'.val eM = m
  refine TblDo.for s _ gS (by omega) (by decide) Inv ?_ ?_ ?_
  · refine ⟨by simp [gacc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
      rw [Function.update_of_ne (by decide)] <;> assumption
  · intro ℓ hℓ s' ⟨hacc', h18', h19', h21', h22', hS', hT', hAA', hZ', hM'⟩ hL' _
    refine (tblRowEBody_do s' h18' h19' h21' h22' hS' hT' hAA' hZ' hM' hL' hℓ hp
      hOW).keep.mono (fun s'' ⟨hacc'', hkp⟩ => ?_) le_rfl
    refine ⟨by rw [hkp _ (by decide), hL'], by rw [hkp _ (by decide), hS'], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · show _ = _; rw [hacc'', hacc', tbl_range_flatMap_succ G ℓ, List.append_assoc]
    all_goals
      dsimp only
      rwa [Function.update_of_ne (by decide), hkp _ (by decide)]
  · intro s' ⟨hacc', _⟩ _ _
    rw [hacc', tblStreamE_eq]

section AEHost

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → IntegerMultBounds.MathlibTM2.Host.Pr P T Q A U}
  {rg : TblR 48 → Fin T}

/-- **The Gaussian stream on the host.** The output register `out` gains exactly
`tblStreamA A w s t α p m` (`t (2m + 1) w` symbols), in at most
`(t (2m + 1) (310 p + 110) + 8 t + 150 p + 420) · tblC W w + 2 t (2m + 1) w + 2` steps. -/
theorem tblStreamA_host (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (st : TblSt 48 A) (hst : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    {s t α p m : ℕ} (hs' : st.val 34 = s) (ht' : st.val 35 = t) (hα' : st.val 36 = α)
    (hm' : st.val 39 = m) (hp' : st.val 19 = p) (hp : 13 ≤ p) (hα : 2 ≤ α) (ht : 0 < t)
    (hW : α ^ 2 * ((s + t) * (m + 1)) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) (v : IntegerMultBounds.MathlibTM2.Host.HS T Q A U)
    (S : IntegerMultBounds.MathlibTM2.Host.Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ (t * (2 * m + 1) * (310 * p + 110) + 8 * t + (150 * p + 420)) * tblC W w +
        2 * (t * (2 * m + 1) * w) + 2 ∧
      IntegerMultBounds.MathlibTM2.Stack.Exec body (tblHost rg tblStreamACode out) (IntegerMultBounds.MathlibTM2.Host.mk v S) n
        (IntegerMultBounds.MathlibTM2.Host.mk v' S') ∧
      S'.R out = tblStreamA A w s t α p m ++ S.R out ∧
      (∃ st' : TblSt 48 A, tblHolds rg S' (tblRho W wl nl st')) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  have h := tbl_stream_host (body := body) hrg hout wl nl hwl hnl hw
    (tblStreamA_do st hs' ht' hα' hm' hp' hp hα ht hW) hst hacc v S hS
  rwa [length_tblStreamA] at h

/-- **The off-diagonal stream on the host.** The output register `out` gains exactly
`tblStreamE A w s t α p m` (`s (2m) w` symbols), in at most
`(s (2m) (310 p + 126) + 14 s + 150 p + 420) · tblC W w + 2 s (2m) w + 2` steps. -/
theorem tblStreamE_host (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (st : TblSt 48 A) (hst : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    {s t α p m : ℕ} (hs' : st.val 34 = s) (ht' : st.val 35 = t) (hα' : st.val 36 = α)
    (hm' : st.val 39 = m) (hp' : st.val 19 = p) (hp : 13 ≤ p) (hα : 2 ≤ α) (hs : 0 < s)
    (hW : α ^ 2 * ((s + t) * (m + 1)) ^ 2 * 2 ^ (13 * p + 8) < 2 ^ W) (v : IntegerMultBounds.MathlibTM2.Host.HS T Q A U)
    (S : IntegerMultBounds.MathlibTM2.Host.Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ (s * (2 * m) * (310 * p + 126) + 14 * s + (150 * p + 420)) * tblC W w +
        2 * (s * (2 * m) * w) + 2 ∧
      IntegerMultBounds.MathlibTM2.Stack.Exec body (tblHost rg tblStreamECode out) (IntegerMultBounds.MathlibTM2.Host.mk v S) n
        (IntegerMultBounds.MathlibTM2.Host.mk v' S') ∧
      S'.R out = tblStreamE A w s t α p m ++ S.R out ∧
      (∃ st' : TblSt 48 A, tblHolds rg S' (tblRho W wl nl st')) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  have h := tbl_stream_host (body := body) hrg hout wl nl hwl hnl hw
    (tblStreamE_do st hs' ht' hα' hm' hp' hp hα hs hW) hst hacc v S hS
  rwa [length_tblStreamE] at h

end AEHost

end IntegerMultBounds.MathlibTM2.Fast.TableVM
