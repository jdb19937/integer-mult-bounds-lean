module

public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGenM

/-!
# The writer of the chunk exchange stream

A table-machine program (`IntegerMultBounds.MathlibTM2.Fast.TableVM`) `ldxCode` that emits the description stream
`ldlXcStream A w (layXcs es ℓ K B)` of the chunk exchanges of the layout `layPerm es ℓ K`
(`IntegerMultBounds.MathlibTM2.Fast.Layout`): per exchange of the chunk pair `(p, k)` the five words
`tblPairs A w v 0` of its header values `v = P, G, B', K, K` (`layXcDims`).

**Inputs** (variables `0 … 4`): `N = es.sum`, `ℓ`, `K`, `D = es.length`, `B`.

**Program.** With `q = (ℓ - 1) / K` and `m = D q` chunks, the inverse `σ⁻¹` of the remaining
chunk permutation of the scan `laySwaps m (layTr D q)` is kept as a packed array in radix
`m + 1` (`ldwPack`), initially `c ↦ (c mod D) q + c / D` (`layTr D q`). For the positions
`k = m - 1, …, 0`: read `p = σ⁻¹ k`; if `p ≠ k`, emit the header words of `(p, k)`
(`ldxEmit`: the offsets `layXcO K p k`, the factors `2^(n - (o₀ + K))`, `2^(o₀ - (o₁ + K))`,
`2^(o₁ - K)` and the products of `swapDims` for the case of `(p, k)`) and compose `σ` with the
transposition of `p` and `k`, which swaps the values `p` and `k` in the array (`ldxSwapBlk`).

**Result** (`ldx_do`): the emitted symbols are `ldlXcStream A w (layXcs es ℓ K B)`, for every
emission width `w`, within `ldxAtoms N D q` atoms, provided `(N + 1)^N < 2^W`,
`N + B + 4 ≤ W` and `ℓ < 2^W`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.Rounds

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

local notation "xN" => (0 : Fin 40)
local notation "xL" => (1 : Fin 40)
local notation "xK" => (2 : Fin 40)
local notation "xD" => (3 : Fin 40)
local notation "xB" => (4 : Fin 40)
local notation "xR" => (5 : Fin 40)
local notation "xV" => (6 : Fin 40)
local notation "xV2" => (7 : Fin 40)
local notation "xRc" => (8 : Fin 40)
local notation "xc" => (9 : Fin 40)
local notation "xk" => (10 : Fin 40)
local notation "xm" => (11 : Fin 40)
local notation "xq" => (12 : Fin 40)
local notation "xkk" => (13 : Fin 40)
local notation "xkx" => (14 : Fin 40)
local notation "xp" => (15 : Fin 40)
local notation "xo0" => (16 : Fin 40)
local notation "xo1" => (17 : Fin 40)
local notation "xe" => (18 : Fin 40)
local notation "xN0" => (19 : Fin 40)
local notation "xN1" => (20 : Fin 40)
local notation "xN2" => (21 : Fin 40)
local notation "xtK" => (22 : Fin 40)
local notation "xP" => (23 : Fin 40)
local notation "xG" => (24 : Fin 40)
local notation "xT" => (25 : Fin 40)
local notation "xB3" => (26 : Fin 40)
local notation "xBp" => (27 : Fin 40)
local notation "xy" => (28 : Fin 40)
local notation "xy2" => (29 : Fin 40)
local notation "xt" => (30 : Fin 40)
local notation "xOne" => (31 : Fin 40)
local notation "xZero" => (32 : Fin 40)
local notation "xTwo" => (33 : Fin 40)
local notation "xk2" => (34 : Fin 40)
local notation "xLm1" => (35 : Fin 40)
local notation "xtmp" => (36 : Fin 40)
local notation "xtmp2" => (37 : Fin 40)

/-! ### The code -/

/-- `dst := 2 ^ (b - (a + K))`. -/
def ldxTriple (a b dst : Fin 40) : TblCode 40 :=
  .ins (.add a xK xtmp) ;; .ins (.sub b xtmp xe) ;; tblPow2 dst xe xk2

/-- The factors `N₀ = 2^(n - (o₀ + K))`, `N₁ = 2^(o₀ - (o₁ + K))`,
`N₂ = 2^(o₁ - (0 + K))`. -/
def ldxCommon : TblCode 40 :=
  ldxTriple xo0 xN xN0 ;; ldxTriple xo1 xo0 xN1 ;; ldxTriple xZero xo1 xN2

/-- `p > 0`: offsets `(k K, p K, 0)`, slots `0, 1`: `(N₀, N₁, N₂ 2^K N₃)`. -/
def ldxCase1 : TblCode 40 :=
  .ins (.mul xkx xK xo0) ;; .ins (.mul xp xK xo1) ;; ldxCommon ;; .ins (.copy xN0 xP) ;;
    .ins (.copy xN1 xG) ;; .ins (.mul xN2 xtK xT) ;; .ins (.mul xT xOne xT)

/-- `p = 0`, `k < 2`: offsets `(2 K, K, 0)`, slots `1, 2`: `(N₀ 2^K N₁, N₂, N₃)`. -/
def ldxCase2 : TblCode 40 :=
  .ins (.add xK xK xo0) ;; .ins (.copy xK xo1) ;; ldxCommon ;; .ins (.mul xN0 xtK xP) ;;
    .ins (.mul xP xN1 xP) ;; .ins (.copy xN2 xG) ;; .ins (.copy xOne xT)

/-- `p = 0`, `2 ≤ k`: offsets `(k K, K, 0)`, slots `0, 2`: `(N₀, N₁ 2^K N₂, N₃)`. -/
def ldxCase3 : TblCode 40 :=
  .ins (.mul xkx xK xo0) ;; .ins (.copy xK xo1) ;; ldxCommon ;; .ins (.copy xN0 xP) ;;
    .ins (.mul xN1 xtK xG) ;; .ins (.mul xG xN2 xG) ;; .ins (.copy xOne xT)

/-- The five header words of the exchange of the chunks `p < k`. -/
def ldxEmit : TblCode 40 :=
  tblPow2 xtK xK xk2 ;; .ite xZero xp ldxCase1 (.ite xkx xTwo ldxCase2 ldxCase3) ;;
    .ins (.mul xT xB3 xBp) ;; .ins (.emit xP xZero) ;; .ins (.emit xG xZero) ;;
    .ins (.emit xBp xZero) ;; .ins (.emit xK xZero) ;; .ins (.emit xK xZero)

/-- `y2 := y` for `y ≠ k` (`y ≠ p`), `p` for `y = k`. -/
def ldxNeP : TblCode 40 :=
  .ite xy xkx (.ins (.copy xy xy2)) (.ite xkx xy (.ins (.copy xy xy2)) (.ins (.copy xp xy2)))

/-- `y2 :=` the image of `y` under the transposition of `p` and `k`. -/
def ldxSwapBlk : TblCode 40 :=
  .ite xy xp ldxNeP (.ite xp xy ldxNeP (.ins (.copy xkx xy2)))

/-- One exchange: its header words, then the transposition of `p` and `k` in the array. -/
def ldxXs : TblCode 40 := ldxEmit ;; ldwMap xV xV2 xRc xR xc xm xt xy xy2 ldxSwapBlk

/-- One position `k = m - 1 - k'` of the scan. -/
def ldxBody : TblCode 40 :=
  .ins (.sub xm xOne xtmp) ;; .ins (.sub xtmp xkk xkx) ;; ldwPowR xRc xR xkx xk ;;
    ldwField xV xRc xR xt xp ;; .ite xp xkx ldxXs (.ite xkx xp ldxXs (.ins (.zero xtmp)))

/-- The constants. -/
def ldxInitBlk : TblCode 40 :=
  tblBlock 40 [.zero xZero, .zero xOne, .inc xOne, .zero xTwo, .inc xTwo, .inc xTwo,
    .sub xL xOne xLm1, .div xLm1 xK xq, .mul xD xq xm, .add xm xOne xR, .add xB xB xB3,
    .add xB3 xB xB3] (.zero xV)

/-- `y2 := (c mod D) q + c / D`, the entry `c` of the inverse of `layTr D q`. -/
def ldxInitMapBlk : TblCode 40 :=
  .ins (.mod xc xD xtmp) ;; .ins (.mul xtmp xq xtmp) ;; .ins (.div xc xD xtmp2) ;;
    .ins (.add xtmp xtmp2 xy2)

/-- **The writer of the chunk exchange stream.** -/
def ldxCode : TblCode 40 :=
  ldxInitBlk ;; ldwMap xV xV2 xRc xR xc xm xt xy xy2 ldxInitMapBlk ;; tblFor xkk xm ldxBody

/-! ### Transpositions of the packed inverse -/

/-- The transposition of `p` and `k` on the naturals. -/
def ldxSw (p k y : ℕ) : ℕ := if y = p then k else if y = k then p else y

/-- The inverse of a permutation of `Fin m` as a function on the naturals. -/
def ldxTau {m : ℕ} (σ : Equiv.Perm (Fin m)) (c : ℕ) : ℕ :=
  if h : c < m then (σ.symm ⟨c, h⟩ : ℕ) else 0

theorem ldxTau_lt {m : ℕ} (σ : Equiv.Perm (Fin m)) {c : ℕ} (hc : c < m) : ldxTau σ c < m := by
  simp [ldxTau, hc]

theorem ldxTau_swap {m : ℕ} (σ : Equiv.Perm (Fin m)) (a b : Fin m) {c : ℕ} (hc : c < m) :
    ldxTau (σ * Equiv.swap a b) c = ldxSw a b (ldxTau σ c) := by
  simp only [ldxTau, hc, ↓reduceDIte, Equiv.Perm.mul_def, Equiv.symm_trans_apply,
    Equiv.symm_swap, Equiv.swap_apply_def, ldxSw]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> simp_all [Fin.ext_iff]

theorem ldxSw_lt {m p k y : ℕ} (hp : p < m) (hk : k < m) (hy : y < m) : ldxSw p k y < m := by
  unfold ldxSw; split_ifs <;> omega

variable {A W w : ℕ}

theorem ldxSwapBlk_do (s : TblSt 40 A) :
    TblDo A W w ldxSwapBlk s (fun s' => s'.val xy2 = ldxSw (s.val xp) (s.val xkx) (s.val xy) ∧
      ldwFr s s' [xy2] ∧ s'.acc = s.acc) 5 := by
  have fr : ∀ v : ℕ, ldwFr s ⟨Function.update s.val xy2 v, s.acc⟩ [xy2] := by
    intro v x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [Function.update_of_ne hx]
  have hne : ∀ (h : s.val xy ≠ s.val xp), TblDo A W w ldxNeP s (fun s' =>
      s'.val xy2 = ldxSw (s.val xp) (s.val xkx) (s.val xy) ∧ ldwFr s s' [xy2] ∧ s'.acc = s.acc)
      3 := by
    intro h
    unfold ldxNeP
    by_cases h₁ : s.val xy < s.val xkx
    · refine TblDo.mono (K := 1 + 1) ?_ (fun _ h => h) (by norm_num)
      refine TblDo.iteT h₁ (TblDo.ins _ ?_)
      refine ⟨?_, fr _, rfl⟩
      simp only [TblIns.run, Function.update_self, ldxSw]
      split_ifs <;> omega
    · refine TblDo.iteF h₁ ?_
      by_cases h₂ : s.val xkx < s.val xy
      · refine TblDo.iteT h₂ (TblDo.ins _ ?_)
        refine ⟨?_, fr _, rfl⟩
        simp only [TblIns.run, Function.update_self, ldxSw]
        split_ifs <;> omega
      · refine TblDo.iteF h₂ (TblDo.ins _ ?_)
        refine ⟨?_, fr _, rfl⟩
        simp only [TblIns.run, Function.update_self, ldxSw]
        split_ifs <;> omega
  unfold ldxSwapBlk
  by_cases h₁ : s.val xy < s.val xp
  · refine TblDo.mono (K := 3 + 1) ?_ (fun _ h => h) (by norm_num)
    exact TblDo.iteT h₁ (hne (by omega))
  · refine TblDo.iteF h₁ ?_
    by_cases h₂ : s.val xp < s.val xy
    · exact TblDo.iteT h₂ (hne (by omega))
    · refine TblDo.mono (K := 1 + 1) ?_ (fun _ h => h) (by norm_num)
      refine TblDo.iteF h₂ (TblDo.ins _ ?_)
      refine ⟨?_, fr _, rfl⟩
      simp only [TblIns.run, Function.update_self, ldxSw]
      split_ifs <;> omega

/-! ### The factors -/

theorem ldxTriple_do (a b dst : Fin 40) (hb : b ≠ xtmp) (h2 : dst ≠ xe) (h3 : dst ≠ xk2)
    (s : TblSt 40 A) {Kv av bv : ℕ} (hK : s.val xK = Kv) (ha : s.val a = av) (hbv : s.val b = bv)
    (hle : av + Kv ≤ bv) (hbW : bv < W) (hb2 : bv < 2 ^ W) :
    TblDo A W w (ldxTriple a b dst) s (fun s' => s'.val dst = 2 ^ (bv - (av + Kv)) ∧
      ldwFr s s' [xtmp, xe, dst, xk2] ∧ s'.acc = s.acc) (4 * bv + 7) := by
  refine TblDo.mono (K := 1 + (1 + (4 * (bv - (av + Kv)) + 5))) ?_ (fun _ h => h) (by omega)
  refine (TblDo.insX (.add a xK xtmp)
    (P := fun s1 => s1 = ⟨Function.update s.val xtmp (av + Kv), s.acc⟩)
    (by simp only [TblIns.fits, ha, hK]; omega) (by simp [TblIns.exact, ha, hK])).seq
    fun s1 hs1 => ?_
  subst hs1
  have hb1 : (Function.update s.val xtmp (av + Kv)) b = bv := by
    rw [Function.update_of_ne hb, hbv]
  refine (TblDo.insX (.sub b xtmp xe)
    (P := fun s2 => s2 = ⟨Function.update (Function.update s.val xtmp (av + Kv)) xe
      (bv - (av + Kv)), s.acc⟩)
    (by simp only [TblIns.fits, hb1, Function.update_self]; omega)
    (by simp only [TblIns.exact, hb1, Function.update_self])).seq fun s2 hs2 => ?_
  subst hs2
  have hp := tblPow2_do (A := A) (W := W) (w := w) (c := dst) (e := xe) (i := xk2) h2 h3
    (by decide)
    ⟨Function.update (Function.update s.val xtmp (av + Kv)) xe (bv - (av + Kv)), s.acc⟩
    (by simp only [Function.update_self]; omega)
  simp only [Function.update_self] at hp
  refine hp.mono (fun s3 ⟨h1, _, hx, hacc⟩ => ⟨h1, fun x hx' => ?_, hacc⟩) le_rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
  rw [hx x hx'.2.2.1 hx'.2.2.2]
  exact (Function.update_of_ne hx'.2.1 _ _).trans (Function.update_of_ne hx'.1 _ _)

/-- The atoms of `ldxCommon`. -/
def ldxCommonAtoms (N : ℕ) : ℕ := 12 * N + 21

theorem ldxCommon_do (s : TblSt 40 A) {N Kv o0 o1 : ℕ} (hN : s.val xN = N) (hK : s.val xK = Kv)
    (hz : s.val xZero = 0) (h0 : s.val xo0 = o0) (h1 : s.val xo1 = o1) (hle0 : o0 + Kv ≤ N)
    (hle1 : o1 + Kv ≤ o0) (hle2 : 0 + Kv ≤ o1) (hNW : N < W) (hN2 : N < 2 ^ W) :
    TblDo A W w ldxCommon s (fun s' => s'.val xN0 = 2 ^ (N - (o0 + Kv)) ∧
      s'.val xN1 = 2 ^ (o0 - (o1 + Kv)) ∧ s'.val xN2 = 2 ^ (o1 - (0 + Kv)) ∧
      ldwFr s s' [xtmp, xe, xN0, xk2, xN1, xN2] ∧ s'.acc = s.acc) (ldxCommonAtoms N) := by
  refine TblDo.mono (K := (4 * N + 7) + ((4 * o0 + 7) + (4 * o1 + 7))) ?_ (fun _ h => h)
    (by unfold ldxCommonAtoms; omega)
  refine (ldxTriple_do (A := A) (W := W) (w := w) xo0 xN xN0 (by decide) (by decide) (by decide)
    s hK h0 hN hle0 hNW hN2).seq fun s1 ⟨e1, fr1, a1⟩ => ?_
  have k1 : s1.val xK = Kv := by rw [fr1 _ (by decide), hK]
  have o01 : s1.val xo0 = o0 := by rw [fr1 _ (by decide), h0]
  have o11 : s1.val xo1 = o1 := by rw [fr1 _ (by decide), h1]
  have z1 : s1.val xZero = 0 := by rw [fr1 _ (by decide), hz]
  refine (ldxTriple_do (A := A) (W := W) (w := w) xo1 xo0 xN1 (by decide) (by decide)
    (by decide) s1 k1 o11 o01 hle1 (by omega) (by omega)).seq fun s2 ⟨e2, fr2, a2⟩ => ?_
  have k2 : s2.val xK = Kv := by rw [fr2 _ (by decide), k1]
  have o12 : s2.val xo1 = o1 := by rw [fr2 _ (by decide), o11]
  have z2 : s2.val xZero = 0 := by rw [fr2 _ (by decide), z1]
  refine (ldxTriple_do (A := A) (W := W) (w := w) xZero xo1 xN2 (by decide) (by decide)
    (by decide) s2 k2 z2 o12 hle2 (by omega) (by omega)).mono
    (fun s3 ⟨e3, fr3, a3⟩ => ⟨?_, ?_, e3, ?_, by rw [a3, a2, a1]⟩) le_rfl
  · rw [fr3 _ (by decide), fr2 _ (by decide), e1]
  · rw [fr3 _ (by decide), e2]
  · exact (fr1.trans fr2 (fun x hx => by simp only [List.mem_cons] at hx ⊢; tauto)
      (fun x hx => by simp only [List.mem_cons] at hx ⊢; tauto)).trans fr3 (fun x hx => hx)
      (fun x hx => by simp only [List.mem_cons] at hx ⊢; tauto)

/-! ### One instruction -/

theorem ldx_ins (i : TblIns 40) (c : Fin 40) (v : ℕ) {rest : TblCode 40} (s : TblSt 40 A)
    (hf : i.fits A W s) (he : i.exact A w s = ⟨Function.update s.val c v, s.acc⟩)
    {P : TblSt 40 A → Prop} {K : ℕ}
    (h : TblDo A W w rest ⟨Function.update s.val c v, s.acc⟩ P K) :
    TblDo A W w (.ins i ;; rest) s P (1 + K) :=
  (TblDo.insX i (P := fun s' => s' = ⟨Function.update s.val c v, s.acc⟩) hf he).seq
    fun _ hs' => hs' ▸ h

/-! ### The header values -/

section Dims

variable (n K B : ℕ) {p k : ℕ}

theorem ldx_dims1 (hp : 0 < p) :
    layXcDims n K (layXcO K p k) (layXcA p k) (layXcB p) B =
      (2 ^ (n - (k * K + K)), 2 ^ (k * K - (p * K + K)),
        2 ^ (p * K - (0 + K)) * 2 ^ K * 2 ^ 0 * (3 * B)) := by
  simp [layXcDims, IntegerMultBounds.MathlibTM2.Node.swapDims, layXcO, layXcA, layXcB, layN0, layN1, layN2, layN3, hp]

theorem ldx_dims2 (hp : p = 0) (hk : k < 2) :
    layXcDims n K (layXcO K p k) (layXcA p k) (layXcB p) B =
      (2 ^ (n - (2 * K + K)) * 2 ^ K * 2 ^ (2 * K - (K + K)), 2 ^ (K - (0 + K)),
        2 ^ 0 * (3 * B)) := by
  subst hp
  have hk' : ¬ 2 ≤ k := by omega
  simp [layXcDims, IntegerMultBounds.MathlibTM2.Node.swapDims, layXcO, layXcA, layXcB, layN0, layN1, layN2, layN3, hk']

theorem ldx_dims3 (hp : p = 0) (hk : 2 ≤ k) :
    layXcDims n K (layXcO K p k) (layXcA p k) (layXcB p) B =
      (2 ^ (n - (k * K + K)), 2 ^ (k * K - (K + K)) * 2 ^ K * 2 ^ (K - (0 + K)),
        2 ^ 0 * (3 * B)) := by
  subst hp
  simp [layXcDims, IntegerMultBounds.MathlibTM2.Node.swapDims, layXcO, layXcA, layXcB, layN0, layN1, layN2, layN3, hk]

theorem ldx_rec (A w : ℕ) (e : ℕ × ℕ) :
    ldlXcRec A w (layXcD n K B e).hs =
      tblPairs A w (layXcDims n K (layXcO K e.1 e.2) (layXcA e.1 e.2) (layXcB e.1) B).1 0 ++
      (tblPairs A w (layXcDims n K (layXcO K e.1 e.2) (layXcA e.1 e.2) (layXcB e.1) B).2.1 0 ++
      (tblPairs A w (layXcDims n K (layXcO K e.1 e.2) (layXcA e.1 e.2) (layXcB e.1) B).2.2 0 ++
      (tblPairs A w K 0 ++ tblPairs A w K 0))) := by
  have h := (layHdr_layHs n K (layXcO K e.1 e.2) (layXcA e.1 e.2) (layXcB e.1) B).1
  simp only [ldlXcRec, layXcD, h]
  rfl

end Dims

/-! ### The constants -/

/-- The constant variables of the writer. -/
structure ldxCore (s : TblSt 40 A) (N L K D B q : ℕ) : Prop where
  cN : s.val xN = N
  cL : s.val xL = L
  cK : s.val xK = K
  cD : s.val xD = D
  cB : s.val xB = B
  cR : s.val xR = D * q + 1
  cm : s.val xm = D * q
  cq : s.val xq = q
  one : s.val xOne = 1
  zero : s.val xZero = 0
  two : s.val xTwo = 2
  lm1 : s.val xLm1 = L - 1
  cB3 : s.val xB3 = B + B + B

theorem ldxCore.fr {s s' : TblSt 40 A} {N L K D B q : ℕ} (h : ldxCore s N L K D B q)
    {M : List (Fin 40)} (hfr : ldwFr s s' M)
    (hM : ∀ x ∈ M, x ∉ [xN, xL, xK, xD, xB, xR, xm, xq, xOne, xZero, xTwo, xLm1, xB3]) :
    ldxCore s' N L K D B q := by
  have e : ∀ x ∈ [xN, xL, xK, xD, xB, xR, xm, xq, xOne, xZero, xTwo, xLm1, xB3],
      s'.val x = s.val x := fun x hx => hfr x fun hm => hM x hm hx
  exact ⟨by rw [e _ (by decide)]; exact h.cN, by rw [e _ (by decide)]; exact h.cL,
    by rw [e _ (by decide)]; exact h.cK, by rw [e _ (by decide)]; exact h.cD,
    by rw [e _ (by decide)]; exact h.cB, by rw [e _ (by decide)]; exact h.cR,
    by rw [e _ (by decide)]; exact h.cm, by rw [e _ (by decide)]; exact h.cq,
    by rw [e _ (by decide)]; exact h.one, by rw [e _ (by decide)]; exact h.zero,
    by rw [e _ (by decide)]; exact h.two, by rw [e _ (by decide)]; exact h.lm1,
    by rw [e _ (by decide)]; exact h.cB3⟩

theorem ldx_fr_upd (s : TblSt 40 A) (c : Fin 40) (v : ℕ) :
    ldwFr s ⟨Function.update s.val c v, s.acc⟩ [c] := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  exact Function.update_of_ne hx _ _

theorem ldx_emit (a b : Fin 40) {rest : TblCode 40} (s : TblSt 40 A) {P : TblSt 40 A → Prop}
    {K : ℕ}
    (h : TblDo A W w rest ⟨s.val, (tblPairs A w (s.val a) (s.val b)).reverse ++ s.acc⟩ P K) :
    TblDo A W w (.ins (.emit a b) ;; rest) s P (1 + K) :=
  (TblDo.ins (.emit a b) (P := fun s' => s' = TblIns.run A W w (.emit a b) s) rfl).seq
    fun _ hs' => hs' ▸ h

theorem ldx_pow_le {a b n : ℕ} (h : a + b ≤ n) : 2 ^ a * 2 ^ b ≤ 2 ^ n := by
  rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) h

/-! ### The three cases -/

/-- The atoms of a case. -/
def ldxCaseAtoms (N : ℕ) : ℕ := ldxCommonAtoms N + 6

/-- The variables changed by a case. -/
def ldxCaseMods : List (Fin 40) := [xo0, xo1, xtmp, xe, xN0, xk2, xN1, xN2, xP, xG, xT]

theorem ldxCase1_do (B : ℕ) (s : TblSt 40 A) {n Kv p k : ℕ} (hN : s.val xN = n)
    (hK : s.val xK = Kv) (hz : s.val xZero = 0) (hone : s.val xOne = 1)
    (htK : s.val xtK = 2 ^ Kv) (hp : s.val xp = p) (hk : s.val xkx = k) (hp0 : 0 < p)
    (hpk : p < k) (hkn : k * Kv + Kv ≤ n) (hnW : n < W) :
    TblDo A W w ldxCase1 s (fun s' =>
      s'.val xP = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).1 ∧
      s'.val xG = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).2.1 ∧
      s'.val xT * (3 * B) = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).2.2 ∧
      ldwFr s s' ldxCaseMods ∧ s'.acc = s.acc) (ldxCaseAtoms n) := by
  rw [ldx_dims1 n Kv B hp0]
  have h2n : 2 ^ n < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hnW
  have hn2 : n < 2 ^ W := lt_of_lt_of_le Nat.lt_two_pow_self h2n.le
  have hpK : p * Kv + Kv ≤ k * Kv := by
    have := Nat.mul_le_mul_right Kv (show p + 1 ≤ k by omega); rw [Nat.add_mul] at this; omega
  have hKp : 0 + Kv ≤ p * Kv := by
    have := Nat.mul_le_mul_right Kv (show 1 ≤ p by omega); omega
  refine TblDo.mono (K := 1 + (1 + (ldxCommonAtoms n + (1 + (1 + (1 + 1)))))) ?_ (fun _ h => h)
    (by unfold ldxCaseAtoms; omega)
  refine ldx_ins (.mul xkx xK xo0) xo0 (k * Kv) s (by simp only [TblIns.fits, hk, hK]; omega)
    (by simp [TblIns.exact, hk, hK]) ?_
  set s1 : TblSt 40 A := ⟨Function.update s.val xo0 (k * Kv), s.acc⟩ with hs1
  refine ldx_ins (.mul xp xK xo1) xo1 (p * Kv) s1
    (by simp only [TblIns.fits, hs1]; rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hp, hK]; omega)
    (by simp only [TblIns.exact, hs1]; rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hp, hK]) ?_
  set s2 : TblSt 40 A := ⟨Function.update s1.val xo1 (p * Kv), s1.acc⟩ with hs2
  have fr2 : ldwFr s s2 [xo0, xo1] := (ldx_fr_upd s xo0 _).trans (ldx_fr_upd s1 xo1 _)
    (by simp) (by simp)
  have hc := ldxCommon_do (A := A) (W := W) (w := w) s2 (N := n) (Kv := Kv) (o0 := k * Kv)
    (o1 := p * Kv) (by rw [fr2 _ (by decide), hN]) (by rw [fr2 _ (by decide), hK])
    (by rw [fr2 _ (by decide), hz])
    (by simp only [hs2, hs1]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp only [hs2]; rw [Function.update_self]) hkn hpK hKp hnW hn2
  refine hc.seq fun s3 ⟨e0, e1, e2, fr3, a3⟩ => ?_
  have tK3 : s3.val xtK = 2 ^ Kv := by rw [fr3 _ (by decide), fr2 _ (by decide), htK]
  have one3 : s3.val xOne = 1 := by rw [fr3 _ (by decide), fr2 _ (by decide), hone]
  have hT : 2 ^ (p * Kv - (0 + Kv)) * 2 ^ Kv ≤ 2 ^ n := ldx_pow_le (by omega)
  refine ldx_ins (.copy xN0 xP) xP (2 ^ (n - (k * Kv + Kv))) s3 trivial
    (by simp [TblIns.exact, e0]) ?_
  set s4 : TblSt 40 A := ⟨Function.update s3.val xP (2 ^ (n - (k * Kv + Kv))), s3.acc⟩ with hs4
  refine ldx_ins (.copy xN1 xG) xG (2 ^ (k * Kv - (p * Kv + Kv))) s4 trivial
    (by simp only [TblIns.exact, hs4]; rw [Function.update_of_ne (by decide), e1]) ?_
  set s5 : TblSt 40 A := ⟨Function.update s4.val xG (2 ^ (k * Kv - (p * Kv + Kv))), s4.acc⟩
    with hs5
  have n25 : s5.val xN2 = 2 ^ (p * Kv - (0 + Kv)) := by
    simp only [hs5, hs4]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), e2]
  have tK5 : s5.val xtK = 2 ^ Kv := by
    simp only [hs5, hs4]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), tK3]
  refine ldx_ins (.mul xN2 xtK xT) xT (2 ^ (p * Kv - (0 + Kv)) * 2 ^ Kv) s5
    (by simp only [TblIns.fits, n25, tK5]; omega) (by simp [TblIns.exact, n25, tK5]) ?_
  set s6 : TblSt 40 A := ⟨Function.update s5.val xT (2 ^ (p * Kv - (0 + Kv)) * 2 ^ Kv), s5.acc⟩
    with hs6
  have one6 : s6.val xOne = 1 := by
    simp only [hs6, hs5, hs4]; rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), one3]
  have T6 : s6.val xT = 2 ^ (p * Kv - (0 + Kv)) * 2 ^ Kv := by simp [hs6]
  refine TblDo.insX (.mul xT xOne xT) (by simp only [TblIns.fits, T6, one6]; omega) ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [TblIns.exact, hs6, hs5, hs4]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  · simp only [TblIns.exact, hs6, hs5]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  · simp only [TblIns.exact, Function.update_self, T6, one6]
    ring
  · intro x hx
    simp only [ldxCaseMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [TblIns.exact, hs6, hs5, hs4]
    rw [Function.update_of_ne hx.2.2.2.2.2.2.2.2.2.2, Function.update_of_ne hx.2.2.2.2.2.2.2.2.2.2,
      Function.update_of_ne hx.2.2.2.2.2.2.2.2.2.1, Function.update_of_ne hx.2.2.2.2.2.2.2.2.1,
      fr3 x (by simp [hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.2.1]),
      fr2 x (by simp [hx.1, hx.2.1])]
  · simp [TblIns.exact, hs6, hs5, hs4, a3, hs2, hs1]

theorem ldxCase2_do (B : ℕ) (s : TblSt 40 A) {n Kv p k : ℕ} (hN : s.val xN = n)
    (hK : s.val xK = Kv) (hz : s.val xZero = 0) (hone : s.val xOne = 1)
    (htK : s.val xtK = 2 ^ Kv) (hp0 : p = 0) (hk2 : k < 2) (hn3 : Kv + Kv + Kv ≤ n)
    (hnW : n < W) :
    TblDo A W w ldxCase2 s (fun s' =>
      s'.val xP = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).1 ∧
      s'.val xG = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).2.1 ∧
      s'.val xT * (3 * B) = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).2.2 ∧
      ldwFr s s' ldxCaseMods ∧ s'.acc = s.acc) (ldxCaseAtoms n) := by
  rw [ldx_dims2 n Kv B hp0 hk2, two_mul]
  have h2n : 2 ^ n < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hnW
  have hn2 : n < 2 ^ W := lt_of_lt_of_le Nat.lt_two_pow_self h2n.le
  refine TblDo.mono (K := 1 + (1 + (ldxCommonAtoms n + (1 + (1 + (1 + 1)))))) ?_ (fun _ h => h)
    (by unfold ldxCaseAtoms; omega)
  refine ldx_ins (.add xK xK xo0) xo0 (Kv + Kv) s (by simp only [TblIns.fits, hK]; omega)
    (by simp [TblIns.exact, hK]) ?_
  set s1 : TblSt 40 A := ⟨Function.update s.val xo0 (Kv + Kv), s.acc⟩ with hs1
  refine ldx_ins (.copy xK xo1) xo1 Kv s1 trivial
    (by simp only [TblIns.exact, hs1]; rw [Function.update_of_ne (by decide), hK]) ?_
  set s2 : TblSt 40 A := ⟨Function.update s1.val xo1 Kv, s1.acc⟩ with hs2
  have fr2 : ldwFr s s2 [xo0, xo1] := (ldx_fr_upd s xo0 _).trans (ldx_fr_upd s1 xo1 _)
    (by simp) (by simp)
  have hc := ldxCommon_do (A := A) (W := W) (w := w) s2 (N := n) (Kv := Kv) (o0 := Kv + Kv)
    (o1 := Kv) (by rw [fr2 _ (by decide), hN]) (by rw [fr2 _ (by decide), hK])
    (by rw [fr2 _ (by decide), hz])
    (by simp only [hs2, hs1]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp only [hs2]; rw [Function.update_self]) hn3 (by omega) (by omega) hnW hn2
  refine hc.seq fun s3 ⟨e0, e1, e2, fr3, a3⟩ => ?_
  have tK3 : s3.val xtK = 2 ^ Kv := by rw [fr3 _ (by decide), fr2 _ (by decide), htK]
  have one3 : s3.val xOne = 1 := by rw [fr3 _ (by decide), fr2 _ (by decide), hone]
  have hP : 2 ^ (n - (Kv + Kv + Kv)) * 2 ^ Kv ≤ 2 ^ n := ldx_pow_le (by omega)
  have hP' : 2 ^ (n - (Kv + Kv + Kv)) * 2 ^ Kv * 2 ^ (Kv + Kv - (Kv + Kv)) ≤ 2 ^ n := by
    simpa using hP
  refine ldx_ins (.mul xN0 xtK xP) xP (2 ^ (n - (Kv + Kv + Kv)) * 2 ^ Kv) s3
    (by simp only [TblIns.fits, e0, tK3]; omega) (by simp [TblIns.exact, e0, tK3]) ?_
  set s4 : TblSt 40 A := ⟨Function.update s3.val xP (2 ^ (n - (Kv + Kv + Kv)) * 2 ^ Kv), s3.acc⟩
    with hs4
  have P4 : s4.val xP = 2 ^ (n - (Kv + Kv + Kv)) * 2 ^ Kv := by simp [hs4]
  have N14 : s4.val xN1 = 2 ^ (Kv + Kv - (Kv + Kv)) := by
    simp only [hs4]; rw [Function.update_of_ne (by decide), e1]
  refine ldx_ins (.mul xP xN1 xP) xP (2 ^ (n - (Kv + Kv + Kv)) * 2 ^ Kv * 2 ^ (Kv + Kv - (Kv + Kv)))
    s4 (by simp only [TblIns.fits, P4, N14]; omega) (by
      simp only [TblIns.exact]; rw [P4, N14]) ?_
  set s5 : TblSt 40 A := ⟨Function.update s4.val xP
    (2 ^ (n - (Kv + Kv + Kv)) * 2 ^ Kv * 2 ^ (Kv + Kv - (Kv + Kv))), s4.acc⟩ with hs5
  refine ldx_ins (.copy xN2 xG) xG (2 ^ (Kv - (0 + Kv))) s5 trivial (by
    simp only [TblIns.exact, hs5, hs4]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), e2]) ?_
  set s6 : TblSt 40 A := ⟨Function.update s5.val xG (2 ^ (Kv - (0 + Kv))), s5.acc⟩ with hs6
  have one6 : s6.val xOne = 1 := by
    simp only [hs6, hs5, hs4]; rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), one3]
  refine TblDo.insX (.copy xOne xT) trivial ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [TblIns.exact, hs6, hs5]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  · simp only [TblIns.exact, hs6]
    rw [Function.update_of_ne (by decide), Function.update_self]
  · simp only [TblIns.exact, Function.update_self, one6]
    simp
  · intro x hx
    simp only [ldxCaseMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [TblIns.exact, hs6, hs5, hs4]
    rw [Function.update_of_ne hx.2.2.2.2.2.2.2.2.2.2, Function.update_of_ne hx.2.2.2.2.2.2.2.2.2.1,
      Function.update_of_ne hx.2.2.2.2.2.2.2.2.1, Function.update_of_ne hx.2.2.2.2.2.2.2.2.1,
      fr3 x (by simp [hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.2.1]),
      fr2 x (by simp [hx.1, hx.2.1])]
  · simp [TblIns.exact, hs6, hs5, hs4, a3, hs2, hs1]

theorem ldxCase3_do (B : ℕ) (s : TblSt 40 A) {n Kv p k : ℕ} (hN : s.val xN = n)
    (hK : s.val xK = Kv) (hz : s.val xZero = 0) (hone : s.val xOne = 1)
    (htK : s.val xtK = 2 ^ Kv) (hk : s.val xkx = k) (hp0 : p = 0) (hk2 : 2 ≤ k)
    (hkn : k * Kv + Kv ≤ n) (hnW : n < W) :
    TblDo A W w ldxCase3 s (fun s' =>
      s'.val xP = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).1 ∧
      s'.val xG = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).2.1 ∧
      s'.val xT * (3 * B) = (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).2.2 ∧
      ldwFr s s' ldxCaseMods ∧ s'.acc = s.acc) (ldxCaseAtoms n) := by
  rw [ldx_dims3 n Kv B hp0 hk2]
  have h2n : 2 ^ n < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hnW
  have hn2 : n < 2 ^ W := lt_of_lt_of_le Nat.lt_two_pow_self h2n.le
  have hKk : Kv + Kv ≤ k * Kv := by
    have := Nat.mul_le_mul_right Kv hk2; omega
  refine TblDo.mono (K := 1 + (1 + (ldxCommonAtoms n + (1 + (1 + (1 + 1)))))) ?_ (fun _ h => h)
    (by unfold ldxCaseAtoms; omega)
  refine ldx_ins (.mul xkx xK xo0) xo0 (k * Kv) s (by simp only [TblIns.fits, hk, hK]; omega)
    (by simp [TblIns.exact, hk, hK]) ?_
  set s1 : TblSt 40 A := ⟨Function.update s.val xo0 (k * Kv), s.acc⟩ with hs1
  refine ldx_ins (.copy xK xo1) xo1 Kv s1 trivial
    (by simp only [TblIns.exact, hs1]; rw [Function.update_of_ne (by decide), hK]) ?_
  set s2 : TblSt 40 A := ⟨Function.update s1.val xo1 Kv, s1.acc⟩ with hs2
  have fr2 : ldwFr s s2 [xo0, xo1] := (ldx_fr_upd s xo0 _).trans (ldx_fr_upd s1 xo1 _)
    (by simp) (by simp)
  have hc := ldxCommon_do (A := A) (W := W) (w := w) s2 (N := n) (Kv := Kv) (o0 := k * Kv)
    (o1 := Kv) (by rw [fr2 _ (by decide), hN]) (by rw [fr2 _ (by decide), hK])
    (by rw [fr2 _ (by decide), hz])
    (by simp only [hs2, hs1]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp only [hs2]; rw [Function.update_self]) hkn hKk (by omega) hnW hn2
  refine hc.seq fun s3 ⟨e0, e1, e2, fr3, a3⟩ => ?_
  have tK3 : s3.val xtK = 2 ^ Kv := by rw [fr3 _ (by decide), fr2 _ (by decide), htK]
  have one3 : s3.val xOne = 1 := by rw [fr3 _ (by decide), fr2 _ (by decide), hone]
  have hG : 2 ^ (k * Kv - (Kv + Kv)) * 2 ^ Kv ≤ 2 ^ n := ldx_pow_le (by omega)
  have hG' : 2 ^ (k * Kv - (Kv + Kv)) * 2 ^ Kv * 2 ^ (Kv - (0 + Kv)) ≤ 2 ^ n := by
    simpa using hG
  refine ldx_ins (.copy xN0 xP) xP (2 ^ (n - (k * Kv + Kv))) s3 trivial
    (by simp [TblIns.exact, e0]) ?_
  set s4 : TblSt 40 A := ⟨Function.update s3.val xP (2 ^ (n - (k * Kv + Kv))), s3.acc⟩ with hs4
  have N14 : s4.val xN1 = 2 ^ (k * Kv - (Kv + Kv)) := by
    simp only [hs4]; rw [Function.update_of_ne (by decide), e1]
  have tK4 : s4.val xtK = 2 ^ Kv := by
    simp only [hs4]; rw [Function.update_of_ne (by decide), tK3]
  refine ldx_ins (.mul xN1 xtK xG) xG (2 ^ (k * Kv - (Kv + Kv)) * 2 ^ Kv) s4
    (by simp only [TblIns.fits, N14, tK4]; omega) (by simp [TblIns.exact, N14, tK4]) ?_
  set s5 : TblSt 40 A := ⟨Function.update s4.val xG (2 ^ (k * Kv - (Kv + Kv)) * 2 ^ Kv), s4.acc⟩
    with hs5
  have G5 : s5.val xG = 2 ^ (k * Kv - (Kv + Kv)) * 2 ^ Kv := by simp [hs5]
  have N25 : s5.val xN2 = 2 ^ (Kv - (0 + Kv)) := by
    simp only [hs5, hs4]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), e2]
  refine ldx_ins (.mul xG xN2 xG) xG (2 ^ (k * Kv - (Kv + Kv)) * 2 ^ Kv * 2 ^ (Kv - (0 + Kv))) s5
    (by simp only [TblIns.fits, G5, N25]; omega) (by
      simp only [TblIns.exact]; rw [G5, N25]) ?_
  set s6 : TblSt 40 A := ⟨Function.update s5.val xG
    (2 ^ (k * Kv - (Kv + Kv)) * 2 ^ Kv * 2 ^ (Kv - (0 + Kv))), s5.acc⟩ with hs6
  have one6 : s6.val xOne = 1 := by
    simp only [hs6, hs5, hs4]; rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), one3]
  refine TblDo.insX (.copy xOne xT) trivial ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [TblIns.exact, hs6, hs5, hs4]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  · simp only [TblIns.exact, hs6]
    rw [Function.update_of_ne (by decide), Function.update_self]
  · simp only [TblIns.exact, Function.update_self, one6]
    simp
  · intro x hx
    simp only [ldxCaseMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [TblIns.exact, hs6, hs5, hs4]
    rw [Function.update_of_ne hx.2.2.2.2.2.2.2.2.2.2, Function.update_of_ne hx.2.2.2.2.2.2.2.2.2.1,
      Function.update_of_ne hx.2.2.2.2.2.2.2.2.2.1, Function.update_of_ne hx.2.2.2.2.2.2.2.2.1,
      fr3 x (by simp [hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.2.1]),
      fr2 x (by simp [hx.1, hx.2.1])]
  · simp [TblIns.exact, hs6, hs5, hs4, a3, hs2, hs1]

/-! ### The header words of one exchange -/

/-- The atoms of `ldxEmit`. -/
def ldxEmitAtoms (N : ℕ) : ℕ := 16 * N + 40

/-- The variables changed by `ldxEmit`. -/
def ldxEmitMods : List (Fin 40) :=
  [xtK, xk2, xo0, xo1, xtmp, xe, xN0, xN1, xN2, xP, xG, xT, xBp]

theorem ldx_third_le {n Kv B m p k : ℕ} (hKm : Kv * m ≤ n) (hm3 : 3 ≤ m) (hpk : p < k)
    (hkm : k < m) :
    (layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B).2.2 ≤ 2 ^ n * (3 * B) := by
  obtain ⟨hO, _, _⟩ := layXcD_OK (B := B) hKm hm3 (e := (p, k)) hpk hkm
  have hO' : LayXcOK n Kv (layXcO Kv p k) := hO
  have hpos : ∀ e : ℕ, 0 < 2 ^ e := fun e => Nat.two_pow_pos e
  have h := (ldl_swapDims_le (N₀ := layN0 n Kv (layXcO Kv p k)) (N₁ := layN1 Kv (layXcO Kv p k))
    (N₂ := layN2 Kv (layXcO Kv p k)) (N₃ := layN3 (layXcO Kv p k)) Kv (hpos _) (hpos _) (hpos _)
    (hpos _) (layXcA p k) (layXcB p)).2.2
  rw [lay_rectSize hO'] at h
  exact Nat.mul_le_mul_right _ h

theorem ldxEmit_do (B : ℕ) (s : TblSt 40 A) {n ℓ Kv D q p k : ℕ}
    (hc : ldxCore s n ℓ Kv D B q) (hp : s.val xp = p) (hk : s.val xkx = k) (hpk : p < k)
    (hkm : k < D * q) (hKm : Kv * (D * q) ≤ n) (hm3 : 3 ≤ D * q) (hnW : n < W)
    (hWB : n + B + 4 ≤ W) :
    TblDo A W w ldxEmit s (fun s' => ldxCore s' n ℓ Kv D B q ∧ ldwFr s s' ldxEmitMods ∧
      s'.acc = (ldlXcRec A w (layXcD n Kv B (p, k)).hs).reverse ++ s.acc) (ldxEmitAtoms n) := by
  set X := layXcDims n Kv (layXcO Kv p k) (layXcA p k) (layXcB p) B with hX
  have hkn : k * Kv + Kv ≤ n := by
    have := Nat.mul_le_mul_right Kv (show k + 1 ≤ D * q by omega)
    rw [Nat.add_mul, Nat.mul_comm (D * q)] at this; omega
  have hn3 : Kv + Kv + Kv ≤ n := by
    have := Nat.mul_le_mul_right Kv hm3
    rw [Nat.mul_comm (D * q)] at this; omega
  have hKn : Kv ≤ n := by omega
  have h2n : 2 ^ n < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hnW
  have hB : 2 ^ n * (3 * B) < 2 ^ W := by
    have h3B : 3 * B < 2 ^ (B + 4) := by
      have := Nat.lt_two_pow_self (n := B)
      rw [pow_add]; omega
    calc 2 ^ n * (3 * B) < 2 ^ n * 2 ^ (B + 4) := Nat.mul_lt_mul_of_pos_left h3B (by positivity)
      _ = 2 ^ (n + B + 4) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hWB
  have hX22 : X.2.2 ≤ 2 ^ n * (3 * B) := ldx_third_le hKm hm3 hpk hkm
  refine TblDo.mono (K := (4 * Kv + 5) + ((ldxCaseAtoms n + 2) +
    (1 + (1 + (1 + (1 + (1 + 1))))))) ?_ (fun _ h => h)
    (by unfold ldxEmitAtoms ldxCaseAtoms ldxCommonAtoms; omega)
  -- tK := 2 ^ K
  have hp2 := tblPow2_do (A := A) (W := W) (w := w) (c := xtK) (e := xK) (i := xk2) (by decide)
    (by decide) (by decide) s (by rw [hc.cK]; omega)
  rw [hc.cK] at hp2
  refine hp2.seq fun s1 ⟨htK1, _, hx1, hacc1⟩ => ?_
  have fr1 : ldwFr s s1 [xtK, xk2] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact hx1 x hx.1 hx.2
  have c1 := hc.fr fr1 (by decide)
  have hp1 : s1.val xp = p := by rw [fr1 _ (by decide), hp]
  have hk1 : s1.val xkx = k := by rw [fr1 _ (by decide), hk]
  -- the case of `(p, k)`
  have hcase : TblDo A W w (.ite xZero xp ldxCase1 (.ite xkx xTwo ldxCase2 ldxCase3)) s1
      (fun s' => s'.val xP = X.1 ∧ s'.val xG = X.2.1 ∧ s'.val xT * (3 * B) = X.2.2 ∧
        ldwFr s1 s' ldxCaseMods ∧ s'.acc = s1.acc) (ldxCaseAtoms n + 2) := by
    by_cases hp0 : 0 < p
    · refine TblDo.mono (K := ldxCaseAtoms n + 1) ?_ (fun _ h => h) (by omega)
      refine TblDo.iteT (by rw [c1.zero, hp1]; exact hp0) ?_
      exact ldxCase1_do B s1 c1.cN c1.cK c1.zero c1.one htK1 hp1 hk1 hp0 hpk hkn hnW
    · refine TblDo.iteF (by rw [c1.zero, hp1]; exact hp0) ?_
      by_cases hk2 : k < 2
      · exact TblDo.iteT (by rw [c1.two, hk1]; exact hk2)
          (ldxCase2_do B s1 c1.cN c1.cK c1.zero c1.one htK1 (by omega) hk2 hn3 hnW)
      · exact TblDo.iteF (by rw [c1.two, hk1]; exact hk2)
          (ldxCase3_do B s1 c1.cN c1.cK c1.zero c1.one htK1 hk1 (by omega) (by omega) hkn hnW)
  refine hcase.seq fun s2 ⟨hP2, hG2, hT2, fr2, hacc2⟩ => ?_
  have c2 := c1.fr fr2 (by decide)
  have hBp : s2.val xT * s2.val xB3 = X.2.2 := by
    rw [c2.cB3, show B + B + B = 3 * B by ring, hT2]
  refine ldx_ins (.mul xT xB3 xBp) xBp X.2.2 s2 (by simp only [TblIns.fits, hBp]; omega)
    (by simp [TblIns.exact, hBp]) ?_
  set s3 : TblSt 40 A := ⟨Function.update s2.val xBp X.2.2, s2.acc⟩ with hs3
  have fr3 : ldwFr s2 s3 [xBp] := ldx_fr_upd s2 xBp _
  have c3 := c2.fr fr3 (by decide)
  have P3 : s3.val xP = X.1 := by rw [fr3 _ (by decide), hP2]
  have G3 : s3.val xG = X.2.1 := by rw [fr3 _ (by decide), hG2]
  have Bp3 : s3.val xBp = X.2.2 := by simp [hs3]
  -- the five words
  have K3 : s3.val xK = Kv := c3.cK
  have Z3 : s3.val xZero = 0 := c3.zero
  refine ldx_emit xP xZero s3 ?_
  refine ldx_emit xG xZero _ ?_
  refine ldx_emit xBp xZero _ ?_
  refine ldx_emit xK xZero _ ?_
  refine TblDo.ins _ ⟨c3.fr (M := []) (fun _ _ => rfl) (by simp), ?_, ?_⟩
  · intro x hx
    simp only [ldxEmitMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    show s3.val x = s.val x
    rw [fr3 x (by simp [hx.2.2.2.2.2.2.2.2.2.2.2.2]),
      fr2 x (by simp [ldxCaseMods, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.1, hx.2.1, hx.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.1,
        hx.2.2.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.2.2.2.1]),
      fr1 x (by simp [hx.1, hx.2.1])]
  · simp only [TblIns.run, P3, G3, Bp3, K3, Z3]
    rw [ldx_rec, show s3.acc = s.acc by rw [show s3.acc = s2.acc from rfl, hacc2, hacc1]]
    simp [List.reverse_append, List.append_assoc]
    rfl

/-! ### One position of the scan -/

/-- The record of the exchange `e`. -/
def ldxRecX (A w N K B : ℕ) (e : ℕ × ℕ) : List (Fin (A + 4)) :=
  ldlXcRec A w (layXcD N K B e).hs

/-- The atoms of one position of the scan. -/
def ldxBodyAtoms (N m : ℕ) : ℕ :=
  1 + (1 + ((4 * m + 5) + (2 + ((ldxEmitAtoms N + (m * (5 + 8) + 7)) + 2))))

theorem ldxBody_do (B : ℕ) (s : TblSt 40 A) {N ℓ Kv D q : ℕ} (hc : ldxCore s N ℓ Kv D B q)
    {k' : ℕ} (hk' : k' < D * q) (hkk : s.val xkk = k') (σ : Equiv.Perm (Fin (D * q)))
    (em : List (ℕ × ℕ)) (acc0 : List (Fin (A + 4)))
    (hV : s.val xV = ldwPack (D * q + 1) (ldxTau σ) (D * q))
    (hsw : laySwaps (D * q) (layTr D q) = em ++ laySwaps (D * q - k') σ)
    (hacc : s.acc = (em.flatMap (ldxRecX A w N Kv B)).reverse ++ acc0)
    (hspec : ∀ e ∈ laySwaps (D * q) (layTr D q), e.1 < e.2 ∧ e.2 < D * q)
    (h3 : ∀ e ∈ laySwaps (D * q) (layTr D q), 3 ≤ D * q)
    (hKm : Kv * (D * q) ≤ N) (hmN : D * q ≤ N) (hW : (N + 1) ^ N < 2 ^ W) (hNW : N < W)
    (hWB : N + B + 4 ≤ W) :
    TblDo A W w ldxBody s (fun s' => ldxCore s' N ℓ Kv D B q ∧ s'.val xkk = k' ∧
      ∃ (σ' : Equiv.Perm (Fin (D * q))) (em' : List (ℕ × ℕ)),
        s'.val xV = ldwPack (D * q + 1) (ldxTau σ') (D * q) ∧
        laySwaps (D * q) (layTr D q) = em' ++ laySwaps (D * q - (k' + 1)) σ' ∧
        s'.acc = (em'.flatMap (ldxRecX A w N Kv B)).reverse ++ acc0)
      (ldxBodyAtoms N (D * q)) := by
  obtain ⟨k, hkdef⟩ : ∃ k, k = D * q - 1 - k' := ⟨_, rfl⟩
  have hkm : k < D * q := by omega
  have hmk : D * q - k' = k + 1 := by omega
  have h2N : 2 ^ N < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hNW
  have hNW2 : N + 1 < 2 ^ W := lt_of_le_of_lt (Nat.lt_two_pow_self (n := N)) h2N
  have hmW : (D * q + 1) ^ (D * q) < 2 ^ W :=
    lt_of_le_of_lt ((Nat.pow_le_pow_left (by omega) (D * q)).trans
      (Nat.pow_le_pow_right (by omega) hmN)) hW
  have hRk : (D * q + 1) ^ k < 2 ^ W :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hkm.le) hmW
  refine TblDo.mono (K := 1 + (1 + ((4 * k + 5) + (2 + ((ldxEmitAtoms N +
    (D * q * (5 + 8) + 7)) + 2))))) ?_ (fun _ h => h) (by unfold ldxBodyAtoms; omega)
  -- k := m - 1 - k'
  refine ldx_ins (.sub xm xOne xtmp) xtmp (D * q - 1) s
    (by simp only [TblIns.fits, hc.cm, hc.one]; omega) (by simp [TblIns.exact, hc.cm, hc.one]) ?_
  have kk1 : (⟨Function.update s.val xtmp (D * q - 1), s.acc⟩ : TblSt 40 A).val xkk = k' := by
    show Function.update s.val xtmp (D * q - 1) xkk = k'
    rw [Function.update_of_ne (by decide), hkk]
  have t1 :
      (⟨Function.update s.val xtmp (D * q - 1), s.acc⟩ : TblSt 40 A).val xtmp = D * q - 1 :=
    Function.update_self (f := s.val) xtmp (D * q - 1)
  have fr1 := ldx_fr_upd s xtmp (D * q - 1)
  have a1 : (⟨Function.update s.val xtmp (D * q - 1), s.acc⟩ : TblSt 40 A).acc = s.acc := rfl
  generalize (⟨Function.update s.val xtmp (D * q - 1), s.acc⟩ : TblSt 40 A) = s1
    at kk1 t1 fr1 a1 ⊢
  refine ldx_ins (.sub xtmp xkk xkx) xkx k s1
    (by simp only [TblIns.fits, kk1, t1]; omega)
    (by simp only [TblIns.exact, kk1, t1, hkdef]) ?_
  have k2 : (⟨Function.update s1.val xkx k, s1.acc⟩ : TblSt 40 A).val xkx = k :=
    Function.update_self (f := s1.val) xkx k
  have fr2' := ldx_fr_upd s1 xkx k
  have a2 : (⟨Function.update s1.val xkx k, s1.acc⟩ : TblSt 40 A).acc = s.acc := a1
  generalize (⟨Function.update s1.val xkx k, s1.acc⟩ : TblSt 40 A) = s2 at k2 fr2' a2 ⊢
  have fr2 : ldwFr s s2 [xtmp, xkx] := fr1.trans fr2' (by simp) (by simp)
  have c2 := hc.fr fr2 (by decide)
  -- Rc := R ^ k, p := V / Rc % R
  have hpw := ldwPowR_do (A := A) (W := W) (w := w) (Rc := xRc) (R := xR) (e := xkx) (k := xk)
    (by decide) (by decide) (by decide) (by decide) (by decide) s2 (by rw [c2.cR]; omega)
    (by rw [c2.cR, k2]; exact hRk) (by rw [k2]; omega)
  rw [k2, c2.cR] at hpw
  refine hpw.seq fun s3 ⟨hRc3, _, fr3, a3⟩ => ?_
  have c3 := c2.fr fr3 (by decide)
  refine (ldwField_do (A := A) (W := W) (w := w) (V := xV) (Rc := xRc) (R := xR) (t := xt)
    (y := xp) (by decide) s3).seq fun s4 ⟨hp4, fr4, a4⟩ => ?_
  have c4 := c3.fr fr4 (by decide)
  have hV3 : s3.val xV = ldwPack (D * q + 1) (ldxTau σ) (D * q) := by
    rw [fr3 _ (by decide), fr2 _ (by decide), hV]
  have hp4' : s4.val xp = ldxTau σ k := by
    rw [hp4, hV3, hRc3, c3.cR]
    exact ldwPack_field (by omega) (fun c hc' => by have := ldxTau_lt σ hc'; omega) k hkm
  have hk4 : s4.val xkx = k := by rw [fr4 _ (by decide), fr3 _ (by decide), k2]
  have hkk4 : s4.val xkk = k' := by
    rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), hkk]
  have hacc4 : s4.acc = s.acc := by rw [a4, a3, a2]
  have htau : ldxTau σ k = (σ.symm ⟨k, hkm⟩ : ℕ) := by simp [ldxTau, hkm]
  have hlay : laySwaps (k + 1) σ = if (σ.symm ⟨k, hkm⟩ : ℕ) = k then laySwaps k σ
      else ((σ.symm ⟨k, hkm⟩ : ℕ), k) ::
        laySwaps k (σ * Equiv.swap (σ.symm ⟨k, hkm⟩) ⟨k, hkm⟩) := by
    rw [laySwaps, dite_eq_left hkm]
  by_cases hpk : (σ.symm ⟨k, hkm⟩ : ℕ) = k
  · -- no exchange
    rw [ite_eq_left hpk] at hlay
    have hpk4 : s4.val xp = k := by rw [hp4', htau, hpk]
    refine TblDo.mono (K := 1 + (1 + 1)) ?_ (fun _ h => h) (by omega)
    refine TblDo.iteF (by rw [hpk4, hk4]; omega) (TblDo.iteF (by rw [hpk4, hk4]; omega) ?_)
    refine TblDo.ins _ ⟨c4.fr (ldx_fr_upd s4 xtmp 0) (by decide), ?_, σ, em, ?_, ?_, ?_⟩
    · simp only [TblIns.run]; rw [Function.update_of_ne (by decide), hkk4]
    · simp only [TblIns.run]
      rw [Function.update_of_ne (by decide), fr4 _ (by decide), hV3]
    · rw [hsw, hmk, hlay, show D * q - (k' + 1) = k by omega]
    · simp only [TblIns.run]; rw [hacc4, hacc]
  · -- the exchange of `(p, k)`
    set p := (σ.symm ⟨k, hkm⟩ : ℕ) with hp
    rw [ite_eq_right hpk] at hlay
    have hmem : (p, k) ∈ laySwaps (D * q) (layTr D q) := by
      rw [hsw, hmk, hlay]; simp
    obtain ⟨hpk', -⟩ := hspec _ hmem
    have hm3 := h3 _ hmem
    have hp4'' : s4.val xp = p := by rw [hp4', htau]
    refine TblDo.mono (K := ((ldxEmitAtoms N + (D * q * (5 + 8) + 7)) + 1)) ?_ (fun _ h => h)
      (by omega)
    refine TblDo.iteT (by rw [hp4'', hk4]; exact hpk') ?_
    refine (ldxEmit_do (A := A) (W := W) (w := w) B s4 c4 hp4'' hk4 hpk' hkm hKm hm3
      (by omega) hWB).seq fun s5 ⟨c5, fr5, a5⟩ => ?_
    have hV5 : s5.val xV = ldwPack (D * q + 1) (ldxTau σ) (D * q) := by
      rw [fr5 _ (by decide), fr4 _ (by decide), hV3]
    have hm := ldwMap_do (A := A) (W := W) (w := w) (V := xV) (V2 := xV2) (Rc := xRc) (R := xR)
      (c := xc) (M := xm) (t := xt) (y := xy) (y2 := xy2) (blk := ldxSwapBlk) (by decide) s5
      (f := ldxTau σ) (G := fun _ y => ldxSw p k y) c5.cm c5.cR (by omega) hV5
      (fun c hc' => by have := ldxTau_lt σ hc'; omega)
      (fun c hc' => by
        have := ldxSw_lt (p := p) (k := k) (show p < D * q by omega) hkm (ldxTau_lt σ hc'); omega)
      hmW
      (by omega) [] (by simp) 5
      (fun j _ s' hfr' _ _ _ => by
        have hp' : s'.val xp = p := by rw [hfr' _ (by decide), fr5 _ (by decide), hp4'']
        have hk' : s'.val xkx = k := by rw [hfr' _ (by decide), fr5 _ (by decide), hk4]
        have := ldxSwapBlk_do (A := A) (W := W) (w := w) s'
        rw [hp', hk'] at this
        exact this)
    refine hm.mono (fun s6 ⟨hV6, fr6, a6⟩ => ⟨c5.fr fr6 (by decide), ?_,
      σ * Equiv.swap (σ.symm ⟨k, hkm⟩) ⟨k, hkm⟩, em ++ [(p, k)], ?_, ?_, ?_⟩) le_rfl
    · rw [fr6 _ (by decide), fr5 _ (by decide), hkk4]
    · rw [hV6]
      exact ldwPack_congr fun c hc' => (ldxTau_swap σ (σ.symm ⟨k, hkm⟩) ⟨k, hkm⟩ hc').symm
    · rw [hsw, hmk, hlay, show D * q - (k' + 1) = k by omega, List.append_assoc]
      rfl
    · rw [a6, a5, hacc4, hacc, List.flatMap_append, List.reverse_append, List.append_assoc]
      simp [ldxRecX]

/-! ### The whole writer -/

/-- The atoms of `ldxCode`. -/
def ldxAtoms (N D q : ℕ) : ℕ :=
  (12 + 1 + (D * q * (4 + 8) + 7)) + (1 + (D * q * (ldxBodyAtoms N (D * q) + 1 + 2) + 2))

theorem ldx_inv_lt {D q j : ℕ} (hj : j < D * q) : j % D * q + j / D < D * q := by
  have hD0 : 0 < D := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  have h1 : j / D < q := Nat.div_lt_of_lt_mul hj
  have h2 := Nat.mod_lt j hD0
  calc j % D * q + j / D < j % D * q + q := by omega
    _ = (j % D + 1) * q := by ring
    _ ≤ D * q := Nat.mul_le_mul_right q h2

theorem ldxInitMap_do (s : TblSt 40 A) {D q j : ℕ} (hD : s.val xD = D) (hq : s.val xq = q)
    (hc : s.val xc = j) (hj : j < D * q) (hW : D * q < 2 ^ W) :
    TblDo A W w ldxInitMapBlk s (fun s' => s'.val xy2 = j % D * q + j / D ∧
      ldwFr s s' [xy2, xtmp, xtmp2] ∧ s'.acc = s.acc) 4 := by
  have hb : j % D * q + j / D < D * q := ldx_inv_lt hj
  have h1 : j % D * q < 2 ^ W := lt_of_le_of_lt (Nat.le_add_right _ _) (hb.trans hW)
  have h2 : j % D * q + j / D < 2 ^ W := hb.trans hW
  show TblDo A W w (tblBlock 40 [.mod xc xD xtmp, .mul xtmp xq xtmp, .div xc xD xtmp2]
    (.add xtmp xtmp2 xy2)) s _ (3 + 1)
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, Function.update_apply, hc, hD, hq]
    exact ⟨h1, h2⟩
  · simp only [List.cons_append, List.nil_append, tblExactList, TblIns.exact]
    refine ⟨?_, fun x hx => ?_, by simp⟩
    · simp [Function.update_apply, hc, hD, hq]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [Function.update_apply, hx.1, hx.2.1, hx.2.2]

/-- **The writer of the chunk exchange stream.** From the inputs `N = es.sum`, `ℓ`, `K`,
`D = es.length` and `B` in the variables `0 … 4`, `ldxCode` emits the description stream
`ldlXcStream A w (layXcs es ℓ K B)` of the chunk exchanges of the layout, for every emission
width `w`, within `ldxAtoms N D q` atoms (`q = layQ ℓ K`), provided `(N + 1)^N < 2^W`,
`N + B + 4 ≤ W` and `ℓ < 2^W`. -/
theorem ldx_do {es : List ℕ} {ℓ K B : ℕ} (H : LayHyp es ℓ K) (st : TblSt 40 A)
    (hN : st.val 0 = es.sum) (hL : st.val 1 = ℓ) (hK : st.val 2 = K)
    (hD : st.val 3 = es.length) (hB : st.val 4 = B)
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hWB : es.sum + B + 4 ≤ W) (hℓW : ℓ < 2 ^ W) :
    TblDo A W w ldxCode st
      (fun s => s.acc = (ldlXcStream A w (layXcs es ℓ K B)).reverse ++ st.acc)
      (ldxAtoms es.sum es.length (layQ ℓ K)) := by
  have hℓ := H.ℓ_ge
  have hK1 := H.K_pos
  have hKm : K * (es.length * layQ ℓ K) ≤ es.sum := by have := lay_chunk_size H; omega
  have hmN : es.length * layQ ℓ K ≤ es.sum := le_trans (Nat.le_mul_of_pos_left _ hK1) hKm
  have h2N : 2 ^ es.sum < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hNW2 : es.sum + 1 < 2 ^ W := lt_of_le_of_lt (Nat.lt_two_pow_self (n := es.sum)) h2N
  have h3B : B + B + B < 2 ^ W := by
    have : 3 * B < 2 ^ (B + 4) := by
      have := Nat.lt_two_pow_self (n := B)
      rw [pow_add]; omega
    have h' : 2 ^ (B + 4) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmW : (es.length * layQ ℓ K + 1) ^ (es.length * layQ ℓ K) < 2 ^ W :=
    lt_of_le_of_lt ((Nat.pow_le_pow_left (by omega) (es.length * layQ ℓ K)).trans
      (Nat.pow_le_pow_right (by omega) hmN)) hW
  -- the constants
  set l : List (TblIns 40) := [.zero xZero, .zero xOne, .inc xOne, .zero xTwo, .inc xTwo,
    .inc xTwo, .sub xL xOne xLm1, .div xLm1 xK xq, .mul xD xq xm, .add xm xOne xR,
    .add xB xB xB3, .add xB3 xB xB3] with hl
  have hblk : TblDo A W w (tblBlock 40 l (.zero xV)) st
      (fun s => ldxCore s es.sum ℓ K es.length B (layQ ℓ K) ∧ s.val xV = 0 ∧ s.acc = st.acc)
      (l.length + 1) := by
    refine TblDo.block l (.zero xV) ?_ ?_
    · simp [hl, tblFitsList, TblIns.fits, TblIns.exact, Function.update_apply, hL, hN, hK, hD, hB]
      refine ⟨by omega, by omega, ⟨by omega, hℓW⟩, ?_, ?_, ?_⟩
      · show es.length * ((ℓ - 1) / K) < 2 ^ W
        have : es.length * layQ ℓ K ≤ es.sum := hmN
        rw [layQ] at this; omega
      · show es.length * ((ℓ - 1) / K) + 1 < 2 ^ W
        have : es.length * layQ ℓ K ≤ es.sum := hmN
        rw [layQ] at this; omega
      · omega
    · simp only [hl, List.cons_append, List.nil_append, tblExactList, TblIns.exact]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
        simp [Function.update_apply, hL, hN, hK, hD, hB, layQ]
  refine TblDo.mono (K := (l.length + 1) + ((es.length * layQ ℓ K * (4 + 8) + 7) +
    (1 + (es.length * layQ ℓ K * (ldxBodyAtoms es.sum (es.length * layQ ℓ K) + 1 + 2) + 2))))
    ?_ (fun _ h => h) (by unfold ldxAtoms; simp [hl]; omega)
  refine hblk.seq fun s1 ⟨c1, hV1, hacc1⟩ => ?_
  refine TblDo.seq (K₁ := es.length * layQ ℓ K * (4 + 8) + 7)
    (P₁ := fun s => ldxCore s es.sum ℓ K es.length B (layQ ℓ K) ∧
      s.val xV = ldwPack (es.length * layQ ℓ K + 1) (ldxTau (layTr es.length (layQ ℓ K)))
        (es.length * layQ ℓ K) ∧ s.acc = st.acc) ?_
    fun s ⟨cs, hVs, haccs⟩ => ?_
  · have hm := ldwMap_do (A := A) (W := W) (w := w) (V := xV) (V2 := xV2) (Rc := xRc) (R := xR)
      (c := xc) (M := xm) (t := xt) (y := xy) (y2 := xy2) (blk := ldxInitMapBlk) (by decide)
      s1 (f := fun _ => 0) (G := fun c _ => c % es.length * layQ ℓ K + c / es.length) c1.cm c1.cR
      (by omega) (by rw [hV1, ldwPack_zero]) (fun c _ => by omega)
      (fun c hc => by
        have : c % es.length * layQ ℓ K + c / es.length < es.length * layQ ℓ K := ldx_inv_lt hc
        omega)
      hmW (by omega) [xtmp, xtmp2] (by decide) 4
      (fun j hj s' hfr' hc' _ _ => by
        have hD' : s'.val xD = es.length := by rw [hfr' _ (by decide)]; exact c1.cD
        have hq' : s'.val xq = (layQ ℓ K) := by rw [hfr' _ (by decide)]; exact c1.cq
        refine (ldxInitMap_do (A := A) (W := W) (w := w) s' hD' hq' hc' hj (by omega)).mono
          (fun s'' ⟨h1, h2, h3⟩ => ⟨h1, h2.mono (by simp), h3⟩) le_rfl)
    refine hm.mono
      (fun s2 ⟨hV2, fr2, hacc2⟩ => ⟨c1.fr fr2 (by decide), ?_, by rw [hacc2, hacc1]⟩)
      le_rfl
    rw [hV2]
    refine ldwPack_congr fun c hc => ?_
    simp only [ldxTau, hc, ↓reduceDIte]
    rfl
  · -- the scan
    have hspec := (laySwaps_layTr_spec (es := es) (ℓ := ℓ) (K := K)).2.2
    have h3 : ∀ e ∈ laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K)),
        3 ≤ es.length * layQ ℓ K := laySwaps_layTr_three
    refine TblDo.for (es.length * layQ ℓ K) (ldxBodyAtoms es.sum (es.length * layQ ℓ K)) cs.cm
      (show es.length * layQ ℓ K < 2 ^ W by omega) (by decide)
      (fun k' t => ldxCore t es.sum ℓ K es.length B (layQ ℓ K) ∧
        ∃ (σ : Equiv.Perm (Fin (es.length * layQ ℓ K))) (em : List (ℕ × ℕ)),
        t.val xV = ldwPack (es.length * layQ ℓ K + 1) (ldxTau σ) (es.length * layQ ℓ K) ∧
        laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K)) =
          em ++ laySwaps (es.length * layQ ℓ K - k') σ ∧
        t.acc = (em.flatMap (ldxRecX A w es.sum K B)).reverse ++ st.acc)
      ⟨cs.fr (ldx_fr_upd s xkk 0) (by decide), layTr es.length (layQ ℓ K), [], ?_, by simp,
        ?_⟩ ?_ ?_
    · show Function.update s.val xkk 0 xV = _
      rw [Function.update_of_ne (by decide), hVs]
    · show s.acc = _
      simp [haccs]
    · intro k' hk' t ⟨ct, σ, em, hVt, hswt, hacct⟩ htk _
      refine (ldxBody_do (A := A) (W := W) (w := w) B t ct hk' htk σ em st.acc hVt hswt hacct
        hspec h3 hKm hmN hW (by omega) hWB).mono
        (fun t' ⟨c', hkk', σ', em', hV', hsw', hacc'⟩ => ⟨hkk', c'.cm, ?_⟩) le_rfl
      refine ⟨c'.fr (ldx_fr_upd t' xkk (k' + 1)) (by decide), σ', em', ?_, hsw', hacc'⟩
      show Function.update t'.val xkk (k' + 1) xV = _
      rw [Function.update_of_ne (by decide), hV']
    · intro t ⟨_, σ, em, _, hswt, hacct⟩ _ _
      rw [Nat.sub_self] at hswt
      have hem : em = laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K)) := by
        rw [hswt]; simp [laySwaps]
      rw [hacct, hem]
      simp [ldlXcStream, layXcs, List.flatMap_map]
      rfl

end IntegerMultBounds.MathlibTM2.Fast.TableVM
