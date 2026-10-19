module

public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutVM
public import IntegerMultBounds.MathlibTM2.Fast.LoadLayout

/-!
# The writer of the single-bit move stream

A table-machine program (`IntegerMultBounds.MathlibTM2.Fast.TableVM`) `ldw1Code` that emits the description stream
`ldlBitStream A w (layBits es ℓ K)` of the prefix moves of the layout `layPerm es ℓ K`
(`IntegerMultBounds.MathlibTM2.Fast.LayoutMath`), one word `tblPairs A w (2 ^ a) (2 ^ b)` per move `(a, b)`.

**Inputs** (variables): `N = es.sum`, `ℓ`, `K`, `D = es.length` and the word `E` of the long
axes, bit `i` of `E` set iff axis `i` has `ℓ` bits (`ax es i = ℓ - 1 + E / 2^i % 2`).

**Program.** The positions `layPos N pre j x` of all `N` address bits after `j` prefix moves
(`pre = layPre es ℓ K`) are kept as a packed array in radix `N + 1` (`ldwPack`), initially the
identity. The slots of `pre` are produced in their order: first the top slot
`off es i + ℓ - 1` of every long axis `i` (`ldwPart1`), then for `h' < b` the slots
`off es i + (b - 1 - h')` of every axis (`ldwPart2`); the offsets `off es i` are kept by
subtracting the axis widths. Each slot is one move (`ldwMoveCode`): read its position `a`, emit
`(2 ^ a, 2 ^ (N - 1 - j))`, apply `layMvFun a (N - 1 - j)` to every entry of the array.

**Result** (`ldw1_do`): the emitted symbols are `ldlBitStream A w (layBits es ℓ K)`, for every
emission width `w`, within `ldw1Atoms` atoms, provided `(N + 1)^N < 2^W` and `N < W`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.Rounds


local notation "vN" => (0 : Fin 40)
local notation "vL" => (1 : Fin 40)
local notation "vK" => (2 : Fin 40)
local notation "vD" => (3 : Fin 40)
local notation "vE" => (4 : Fin 40)
local notation "vR" => (5 : Fin 40)
local notation "vV" => (6 : Fin 40)
local notation "vV2" => (7 : Fin 40)
local notation "vRc" => (8 : Fin 40)
local notation "vc" => (9 : Fin 40)
local notation "vk" => (10 : Fin 40)
local notation "vj" => (11 : Fin 40)
local notation "vi" => (12 : Fin 40)
local notation "vh" => (13 : Fin 40)
local notation "vb" => (14 : Fin 40)
local notation "voff" => (15 : Fin 40)
local notation "vslot" => (16 : Fin 40)
local notation "va" => (17 : Fin 40)
local notation "vbb" => (18 : Fin 40)
local notation "vy" => (19 : Fin 40)
local notation "vy2" => (20 : Fin 40)
local notation "vt" => (21 : Fin 40)
local notation "vt1" => (22 : Fin 40)
local notation "vt2" => (23 : Fin 40)
local notation "vOne" => (24 : Fin 40)
local notation "vZero" => (25 : Fin 40)
local notation "vbit" => (26 : Fin 40)
local notation "vpw" => (27 : Fin 40)
local notation "vk2" => (28 : Fin 40)
local notation "vLm1" => (29 : Fin 40)
local notation "ves" => (30 : Fin 40)
local notation "vtmp" => (31 : Fin 40)
local notation "vTwo" => (32 : Fin 40)
local notation "vi1" => (33 : Fin 40)

/-! ### The code -/

/-- `y2 := layMvFun a bb y`. -/
def ldwMvf : TblCode 40 :=
  .ite vy va (.ite vy vbb (.ins (.copy vy vy2)) (.ins (.add vy vOne vy2)))
    (.ite va vy (.ite vbb vy (.ins (.copy vy vy2)) (.ins (.sub vy vOne vy2)))
      (.ins (.copy vbb vy2)))

/-- `bit := E / 2 ^ iv % 2`. -/
def ldwBitCode (iv : Fin 40) : TblCode 40 :=
  tblPow2 vpw iv vk2 ;; .ins (.div vE vpw vtmp) ;; .ins (.mod vtmp vTwo vbit)

/-- `es := (ℓ - 1) + E / 2 ^ iv % 2`, the width of axis `iv`. -/
def ldwEsCode (iv : Fin 40) : TblCode 40 := ldwBitCode iv ;; .ins (.add vLm1 vbit ves)

/-- One prefix move of the slot `slot`: read its position `a`, emit `(2 ^ a, 2 ^ bb)` with
`bb = N - 1 - j`, apply `layMvFun a bb` to the array of positions, `j := j + 1`. -/
def ldwMoveCode : TblCode 40 :=
  ldwPowR vRc vR vslot vk ;; ldwField vV vRc vR vt va ;;
    .ins (.sub vN vOne vbb) ;; .ins (.sub vbb vj vbb) ;;
    tblPow2 vt1 va vk2 ;; tblPow2 vt2 vbb vk2 ;; .ins (.emit vt1 vt2) ;;
    ldwMap vV vV2 vRc vR vc vN vt vy vy2 ldwMvf ;; .ins (.inc vj)

/-- The top slots of the long axes. -/
def ldwPart1 : TblCode 40 :=
  ldwEsCode vZero ;; .ins (.sub vN ves voff) ;;
    tblFor vi vD (ldwBitCode vi ;;
      .ite vZero vbit (.ins (.add voff vLm1 vslot) ;; ldwMoveCode) (.ins (.zero vtmp)) ;;
      .ins (.add vi vOne vi1) ;; ldwEsCode vi1 ;; .ins (.sub voff ves voff))

/-- The low slots `off es i + (b - 1 - h')`, `h' < b`, of every axis. -/
def ldwPart2 : TblCode 40 :=
  tblFor vh vb (ldwEsCode vZero ;; .ins (.sub vN ves voff) ;;
    tblFor vi vD (.ins (.sub vb vOne vtmp) ;; .ins (.sub vtmp vh vtmp) ;;
      .ins (.add voff vtmp vslot) ;; ldwMoveCode ;; .ins (.add vi vOne vi1) ;; ldwEsCode vi1 ;;
      .ins (.sub voff ves voff)))

/-- The constants and the identity array of positions. -/
def ldwInit : TblCode 40 :=
  tblBlock 40 [.zero vZero, .zero vOne, .inc vOne, .zero vTwo, .inc vTwo, .inc vTwo,
    .sub vL vOne vLm1, .mod vLm1 vK vb, .add vN vOne vR, .zero vV] (.zero vj) ;;
    ldwMap vV vV2 vRc vR vc vN vt vy vy2 (.ins (.copy vc vy2))

/-- **The writer of the single-bit move stream.** -/
def ldw1Code : TblCode 40 := ldwInit ;; ldwPart1 ;; ldwPart2

/-! ### Small blocks -/

variable {A W w : ℕ}

theorem ldwMvf_do (s : TblSt 40 A) (h1 : s.val vOne = 1) (hfit : s.val vy + 1 < 2 ^ W) :
    TblDo A W w ldwMvf s (fun s' => s'.val vy2 = layMvFun (s.val va) (s.val vbb) (s.val vy) ∧
      ldwFr s s' [vy2] ∧ s'.acc = s.acc) 4 := by
  have fr : ∀ v : ℕ, ldwFr s ⟨Function.update s.val vy2 v, s.acc⟩ [vy2] := by
    intro v x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [Function.update_of_ne hx]
  unfold ldwMvf
  by_cases h₁ : s.val vy < s.val va
  · refine TblDo.mono (K := (1 + 1) + 1) ?_ (fun _ h => h) (by norm_num)
    refine TblDo.iteT h₁ ?_
    by_cases h₂ : s.val vy < s.val vbb
    · refine TblDo.iteT h₂ (TblDo.ins _ ?_)
      refine ⟨?_, fr _, rfl⟩
      simp only [TblIns.run, Function.update_self, layMvFun]
      split_ifs <;> omega
    · refine TblDo.iteF h₂ (TblDo.ins _ ?_)
      refine ⟨?_, fr _, rfl⟩
      simp only [TblIns.run, Function.update_self, layMvFun, h1, Nat.mod_eq_of_lt hfit]
      split_ifs <;> omega
  · by_cases h₂ : s.val va < s.val vy
    · refine TblDo.iteF h₁ ?_
      refine TblDo.iteT h₂ ?_
      by_cases h₃ : s.val vbb < s.val vy
      · refine TblDo.iteT h₃ (TblDo.ins _ ?_)
        refine ⟨?_, fr _, rfl⟩
        simp only [TblIns.run, Function.update_self, layMvFun]
        split_ifs <;> omega
      · refine TblDo.iteF h₃ (TblDo.ins _ ?_)
        refine ⟨?_, fr _, rfl⟩
        simp only [TblIns.run, Function.update_self, layMvFun, h1]
        rw [show s.val vy + 2 ^ W - 1 = (s.val vy - 1) + 2 ^ W by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
        split_ifs <;> omega
    · refine TblDo.mono (K := (1 + 1) + 1) ?_ (fun _ h => h) (by norm_num)
      refine TblDo.iteF h₁ ?_
      refine TblDo.iteF h₂ (TblDo.ins _ ?_)
      refine ⟨?_, fr _, rfl⟩
      simp only [TblIns.run, Function.update_self, layMvFun]
      split_ifs <;> omega

theorem ldwBit_do (iv : Fin 40) (hiv : iv ∉ [vpw, vk2, vE, vtmp, vTwo, vbit]) (s : TblSt 40 A)
    (hiW : s.val iv < W) (h2 : s.val vTwo = 2) :
    TblDo A W w (ldwBitCode iv) s (fun s' => s'.val vbit = s.val vE / 2 ^ s.val iv % 2 ∧
      ldwFr s s' [vpw, vk2, vtmp, vbit] ∧ s'.acc = s.acc) (4 * s.val iv + 5 + (1 + 1)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hiv
  have hp := tblPow2_do (A := A) (W := W) (w := w) (c := vpw) (e := iv) (i := vk2)
    (fun h => hiv.1 h.symm) (by decide) (fun h => hiv.2.1 h) s hiW
  refine hp.seq fun s1 ⟨hc, hi, hx, ha⟩ => ?_
  have hE1 : s1.val vE = s.val vE := hx _ (by decide) (by decide)
  have hT1 : s1.val vTwo = 2 := by rw [hx _ (by decide) (by decide)]; exact h2
  refine (TblDo.ins (.div vE vpw vtmp) (P := fun s2 => s2 = TblIns.run A W w (.div vE vpw vtmp) s1)
    rfl).seq fun s2 hs2 => ?_
  subst hs2
  refine TblDo.ins _ ?_
  refine ⟨?_, ?_, ?_⟩
  · simp [TblIns.run, hc, hE1, hT1]
  · intro x hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    simp only [TblIns.run]
    rw [Function.update_of_ne hx'.2.2.2, Function.update_of_ne hx'.2.2.1,
      hx x hx'.1 hx'.2.1]
  · simp [TblIns.run, ha]

theorem ldwEs_do (iv : Fin 40) (hiv : iv ∉ [vpw, vk2, vE, vtmp, vTwo, vbit, vLm1, ves])
    (s : TblSt 40 A) (hiW : s.val iv < W) (h2 : s.val vTwo = 2)
    (hfit : s.val vLm1 + 1 < 2 ^ W) :
    TblDo A W w (ldwEsCode iv) s (fun s' => s'.val ves = s.val vLm1 + s.val vE / 2 ^ s.val iv % 2 ∧
      s'.val vbit = s.val vE / 2 ^ s.val iv % 2 ∧
      ldwFr s s' [vpw, vk2, vtmp, vbit, ves] ∧ s'.acc = s.acc) (4 * s.val iv + 8) := by
  have hiv' : iv ∉ [vpw, vk2, vE, vtmp, vTwo, vbit] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hiv ⊢
    exact ⟨hiv.1, hiv.2.1, hiv.2.2.1, hiv.2.2.2.1, hiv.2.2.2.2.1, hiv.2.2.2.2.2.1⟩
  refine TblDo.mono (K := (4 * s.val iv + 5 + (1 + 1)) + 1) ?_ (fun _ h => h) (by omega)
  refine (ldwBit_do iv hiv' s hiW h2).seq fun s1 ⟨hb, hfr, ha⟩ => ?_
  have hL1 : s1.val vLm1 = s.val vLm1 := hfr _ (by decide)
  have hb2 : s.val vE / 2 ^ s.val iv % 2 < 2 := Nat.mod_lt _ (by norm_num)
  refine TblDo.insX (.add vLm1 vbit ves) (by simp only [TblIns.fits, hL1, hb]; omega) ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [TblIns.exact, hL1, hb]
  · simp only [TblIns.exact]
    rw [Function.update_of_ne (by decide)]; exact hb
  · intro x hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    simp only [TblIns.exact]
    rw [Function.update_of_ne hx'.2.2.2.2]
    exact hfr x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
      ⟨hx'.1, hx'.2.1, hx'.2.2.1, hx'.2.2.2.1⟩)
  · simp [TblIns.exact, ha]

/-! ### The constants -/

/-- The constant variables of the writer. -/
structure ldwCore (s : TblSt 40 A) (N L K D E : ℕ) : Prop where
  cN : s.val vN = N
  cL : s.val vL = L
  cK : s.val vK = K
  cD : s.val vD = D
  cE : s.val vE = E
  cR : s.val vR = N + 1
  one : s.val vOne = 1
  zero : s.val vZero = 0
  two : s.val vTwo = 2
  lm1 : s.val vLm1 = L - 1
  cb : s.val vb = (L - 1) % K

theorem ldwCore.fr {s s' : TblSt 40 A} {N L K D E : ℕ} (h : ldwCore s N L K D E)
    {M : List (Fin 40)} (hfr : ldwFr s s' M)
    (hM : ∀ x ∈ M, x ∉ [vN, vL, vK, vD, vE, vR, vOne, vZero, vTwo, vLm1, vb]) :
    ldwCore s' N L K D E := by
  have e : ∀ x ∈ [vN, vL, vK, vD, vE, vR, vOne, vZero, vTwo, vLm1, vb], s'.val x = s.val x :=
    fun x hx => hfr x fun hm => hM x hm hx
  exact ⟨by rw [e _ (by decide)]; exact h.cN, by rw [e _ (by decide)]; exact h.cL,
    by rw [e _ (by decide)]; exact h.cK, by rw [e _ (by decide)]; exact h.cD,
    by rw [e _ (by decide)]; exact h.cE, by rw [e _ (by decide)]; exact h.cR,
    by rw [e _ (by decide)]; exact h.one, by rw [e _ (by decide)]; exact h.zero,
    by rw [e _ (by decide)]; exact h.two, by rw [e _ (by decide)]; exact h.lm1,
    by rw [e _ (by decide)]; exact h.cb⟩

/-! ### One move -/

/-- The variables changed by a move. -/
def ldwMoveMods : List (Fin 40) := [vRc, vk, vt, va, vbb, vt1, vk2, vt2, vV, vV2, vc, vy, vy2, vj]

/-- The atoms of one move. -/
def ldwMoveAtoms (N : ℕ) : ℕ := 24 * N + 28

/-- **One prefix move.** With the positions after `j` moves packed in `V` and the slot
`pre[j]` in `slot`, `ldwMoveCode` emits `(2 ^ a, 2 ^ (N - 1 - j))` for the position `a` of the
slot and packs the positions after `j + 1` moves. -/
theorem ldwMove_do {N L K D E : ℕ} {pre : List ℕ} (hnd : pre.Nodup) (hlt : ∀ x ∈ pre, x < N)
    (hP : pre.length ≤ N) {j : ℕ} (hj : j < pre.length) (s : TblSt 40 A)
    (hc : ldwCore s N L K D E) (hV : s.val vV = ldwPack (N + 1) (layPos N pre j) N)
    (hjv : s.val vj = j) (hslot : s.val vslot = pre.getD j 0) (hW : (N + 1) ^ N < 2 ^ W)
    (hNW : N < W) :
    TblDo A W w ldwMoveCode s (fun s' => ldwCore s' N L K D E ∧
      s'.val vV = ldwPack (N + 1) (layPos N pre (j + 1)) N ∧ s'.val vj = j + 1 ∧
      ldwFr s s' ldwMoveMods ∧
      s'.acc = (tblPairs A w (2 ^ layPos N pre j (pre.getD j 0)) (2 ^ (N - 1 - j))).reverse ++
        s.acc) (ldwMoveAtoms N) := by
  obtain ⟨sp1, sp2, sp3, sp4⟩ := layPos_spec hnd hlt hP j hj.le
  have hsN : pre.getD j 0 < N := by
    rw [List.getD_eq_getElem _ _ hj]; exact hlt _ (List.getElem_mem hj)
  set a := layPos N pre j (pre.getD j 0) with ha
  have haN : a < N := sp1 _ hsN
  set bb := N - 1 - j with hbb
  have hbbN : bb < N := by omega
  have hN1 : 1 ≤ N := by omega
  have h2W : 2 ^ N ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hNW.le
  have hNW2 : N + 1 < 2 ^ W := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right
    (by norm_num) hNW)
  have hRs : (N + 1) ^ (pre.getD j 0) < 2 ^ W :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hsN.le) hW
  refine TblDo.mono (K := (4 * (pre.getD j 0) + 5) + (2 + (1 + (1 + ((4 * a + 5) +
    ((4 * bb + 5) + (1 + ((N * (4 + 8) + 7) + 1)))))))) ?_ (fun _ h => h)
    (by unfold ldwMoveAtoms; omega)
  -- Rc := R ^ slot
  have hp := ldwPowR_do (A := A) (W := W) (w := w) (Rc := vRc) (R := vR) (e := vslot) (k := vk)
    (by decide) (by decide) (by decide) (by decide) (by decide) s (by rw [hc.cR]; omega)
    (by rw [hc.cR, hslot]; exact hRs) (by rw [hslot]; omega)
  rw [hslot] at hp
  refine hp.seq fun s1 ⟨hRc1, _, hfr1, hacc1⟩ => ?_
  have c1 := hc.fr hfr1 (by decide)
  -- a := V / Rc % R
  refine (ldwField_do (A := A) (W := W) (w := w) (V := vV) (Rc := vRc) (R := vR) (t := vt)
    (y := va) (by decide) s1).seq fun s2 ⟨ha2, hfr2, hacc2⟩ => ?_
  have c2 := c1.fr hfr2 (by decide)
  have hV1 : s1.val vV = s.val vV := hfr1 _ (by decide)
  have ha2' : s2.val va = a := by
    rw [ha2, hV1, hV, hRc1, hc.cR, c1.cR]
    exact ldwPack_field (by omega) (fun c hc' => by have := sp1 c hc'; omega) _ hsN
  -- bb := N - 1 - j
  refine (TblDo.insX (.sub vN vOne vbb)
    (P := fun s3 => s3 = ⟨Function.update s2.val vbb (N - 1), s2.acc⟩)
    (by simp only [TblIns.fits, c2.cN, c2.one]; omega)
    (by simp [TblIns.exact, c2.cN, c2.one])).seq fun s3 hs3 => ?_
  subst hs3
  have hj3 : (Function.update s2.val vbb (N - 1)) vj = j := by
    rw [Function.update_of_ne (by decide), hfr2 _ (by decide), hfr1 _ (by decide), hjv]
  refine (TblDo.insX (.sub vbb vj vbb)
    (P := fun s4 => s4 = ⟨Function.update s2.val vbb bb, s2.acc⟩)
    (by simp only [TblIns.fits, Function.update_self, hj3]; omega)
    (by simp only [TblIns.exact, Function.update_self, hj3, Function.update_idem]; rfl)).seq
    fun s4 hs4 => ?_
  subst hs4
  -- t1 := 2 ^ a, t2 := 2 ^ bb
  have hp1 := tblPow2_do (A := A) (W := W) (w := w) (c := vt1) (e := va) (i := vk2)
    (by decide) (by decide) (by decide) ⟨Function.update s2.val vbb bb, s2.acc⟩
    (by simp only; rw [Function.update_of_ne (by decide), ha2']; omega)
  simp only at hp1
  rw [Function.update_of_ne (by decide), ha2'] at hp1
  refine hp1.seq fun s5 ⟨ht15, _, hx5, hacc5⟩ => ?_
  have hbb5 : s5.val vbb = bb := by
    rw [hx5 _ (by decide) (by decide)]; simp
  have hp2 := tblPow2_do (A := A) (W := W) (w := w) (c := vt2) (e := vbb) (i := vk2)
    (by decide) (by decide) (by decide) s5 (by rw [hbb5]; omega)
  rw [hbb5] at hp2
  refine hp2.seq fun s6 ⟨ht26, _, hx6, hacc6⟩ => ?_
  have ht16 : s6.val vt1 = 2 ^ a := by rw [hx6 _ (by decide) (by decide), ht15]
  -- emit
  refine (TblDo.ins (.emit vt1 vt2) (P := fun s7 => s7 = TblIns.run A W w (.emit vt1 vt2) s6)
    rfl).seq fun s7 hs7 => ?_
  subst hs7
  -- the map
  set s7 := TblIns.run A W w (.emit vt1 vt2) s6 with hs7
  have hs7v : s7.val = s6.val := rfl
  have hs7a : s7.acc = (tblPairs A w (s6.val vt1) (s6.val vt2)).reverse ++ s6.acc := rfl
  have e65 : ∀ x, x ≠ vt2 → x ≠ vk2 → x ≠ vt1 → s7.val x = s2.val x ∨ x = vbb := by
    intro x h1 h2 h3
    by_cases hx : x = vbb
    · exact Or.inr hx
    · left
      rw [hs7v, hx6 x h1 h2, hx5 x h3 h2]
      exact Function.update_of_ne hx _ _
  have hfr7 : ldwFr s s7 ldwMoveMods := by
    intro x hx
    simp only [ldwMoveMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rcases e65 x hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.1 with e | e
    · rw [e, hfr2 x (by simp [hx.2.2.1, hx.2.2.2.1]), hfr1 x (by simp [hx.1, hx.2.1])]
    · exact absurd e hx.2.2.2.2.1
  have c7 : ldwCore s7 N L K D E := hc.fr hfr7 (by decide)
  have hV7 : s7.val vV = ldwPack (N + 1) (layPos N pre j) N := by
    rcases e65 vV (by decide) (by decide) (by decide) with e | e
    · rw [e, hfr2 _ (by decide), hV1, hV]
    · exact absurd e (by decide)
  have ha7 : s7.val va = a := by
    rcases e65 va (by decide) (by decide) (by decide) with e | e
    · rw [e, ha2']
    · exact absurd e (by decide)
  have hbb7 : s7.val vbb = bb := by
    rw [hs7v, hx6 _ (by decide) (by decide), hbb5]
  have hj7 : s7.val vj = j := by
    rcases e65 vj (by decide) (by decide) (by decide) with e | e
    · rw [e, hfr2 _ (by decide), hfr1 _ (by decide), hjv]
    · exact absurd e (by decide)
  have hacc7 : s7.acc = (tblPairs A w (2 ^ a) (2 ^ bb)).reverse ++ s.acc := by
    have ht16' : s6.val vt1 = 2 ^ a := ht16
    rw [hs7a, ht16', ht26, hacc6, hacc5]
    show _ ++ s2.acc = _
    rw [hacc2, hacc1]
  have hm := ldwMap_do (A := A) (W := W) (w := w) (V := vV) (V2 := vV2) (Rc := vRc) (R := vR)
    (c := vc) (M := vN) (t := vt) (y := vy) (y2 := vy2) (by decide) s7
    (f := layPos N pre j) (G := fun _ y => layMvFun a bb y) c7.cN c7.cR (by omega) hV7
    (fun c hc' => by have := sp1 c hc'; omega)
    (fun c hc' => by have := layMvFun_lt haN hbbN (sp1 c hc'); omega) hW
    (lt_of_lt_of_le Nat.lt_two_pow_self h2W |>.trans_le le_rfl |> fun h => by omega) [] (by simp) 4
    (fun j' _ s' hfr' _ hy' hacc' => by
      have hone : s'.val vOne = 1 := by rw [hfr' _ (by decide)]; exact c7.one
      have ha' : s'.val va = a := by rw [hfr' _ (by decide)]; exact ha7
      have hbb' : s'.val vbb = bb := by rw [hfr' _ (by decide)]; exact hbb7
      have := ldwMvf_do (A := A) (W := W) (w := w) s' hone (by omega)
      rw [ha', hbb'] at this
      exact this)
  refine hm.seq fun s8 ⟨hV8, hfr8, hacc8⟩ => ?_
  -- j := j + 1
  have hj8 : s8.val vj = j := by rw [hfr8 _ (by decide)]; exact hj7
  refine TblDo.insX (.inc vj) (by simp only [TblIns.fits, hj8]; omega) ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (c7.fr hfr8 (by decide)).fr (M := [vj]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [TblIns.exact, Function.update_of_ne hx]) (by decide)
  · simp only [TblIns.exact]
    rw [Function.update_of_ne (by decide), hV8]
    exact ldwPack_congr fun c _ => rfl
  · simp [TblIns.exact, hj8]
  · intro x hx
    simp only [TblIns.exact]
    have hx' : x ≠ vj := fun e => hx (by rw [e]; decide)
    rw [Function.update_of_ne hx']
    rw [hfr8 x (fun hm => hx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      simp only [ldwMoveMods, List.mem_cons, List.not_mem_nil, or_false]
      tauto))]
    exact hfr7 x hx
  · simp [TblIns.exact, hacc8, hacc7]

/-! ### The records -/

/-- The record of prefix move `m`: the word of `(2 ^ a, 2 ^ (N - 1 - m))`, `a` the position of
the slot `pre[m]` after `m` moves. -/
def ldwRec (A w N : ℕ) (pre : List ℕ) (m : ℕ) : List (Fin (A + 4)) :=
  tblPairs A w (2 ^ layPos N pre m (pre.getD m 0)) (2 ^ (N - 1 - m))

/-- The records of the first `j` prefix moves. -/
def ldwRecs (A w N : ℕ) (pre : List ℕ) (j : ℕ) : List (Fin (A + 4)) :=
  (List.range j).flatMap (ldwRec A w N pre)

theorem ldwRecs_succ (A w N : ℕ) (pre : List ℕ) (j : ℕ) :
    ldwRecs A w N pre (j + 1) = ldwRecs A w N pre j ++ ldwRec A w N pre j := by
  simp [ldwRecs, List.range_succ, List.flatMap_append]

theorem ldwRecs_layBits (A w : ℕ) (es : List ℕ) (ℓ K : ℕ) :
    ldwRecs A w es.sum (layPre es ℓ K) (layPre es ℓ K).length =
      ldlBitStream A w (layBits es ℓ K) := by
  simp only [ldwRecs, ldlBitStream, layBits, List.flatMap_map]
  rfl

/-! ### Axis widths and offsets -/

section Axes

variable {es : List ℕ} {ℓ K : ℕ}

theorem ldw_off_zero (h : 0 < es.length) : es.sum = ax es 0 + off es 0 := by
  obtain ⟨e, rest, rfl⟩ : ∃ e rest, es = e :: rest := ⟨es.head (by
    rintro rfl; simp at h), es.tail, by simp⟩
  simp [ax, off]

theorem ldw_off_succ {i : ℕ} (h : i + 1 < es.length) : off es i = ax es (i + 1) + off es (i + 1) := by
  simp only [off, ax]
  rw [List.drop_eq_getElem_cons h, List.sum_cons, List.getD_eq_getElem _ _ h]

theorem ldw_lrank_succ (i : ℕ) :
    layLrank es ℓ (i + 1) = layLrank es ℓ i + if ax es i = ℓ then 1 else 0 := by
  simp only [layLrank, List.range_succ, List.filter_append, List.length_append]
  split_ifs with h <;> simp [h]

theorem ldw_lrank_lt {i : ℕ} (hi : i < es.length) (hl : ax es i = ℓ) :
    layLrank es ℓ i < (layLongs es ℓ).length := by
  have h1 := layLongs_getElem? hi hl
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h1
  exact absurd h1 (by simp)

theorem ldw_length_le_sum (H : LayHyp es ℓ K) : es.length ≤ es.sum := by
  have := lay_sum H
  have := H.ℓ_ge
  have : es.length ≤ es.length * (ℓ - 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

end Axes

/-! ### The top slots of the long axes -/

/-- The atoms of one iteration of `ldwPart1`. -/
def ldwP1Atoms (N D : ℕ) : ℕ := (4 * D + 7) + ((ldwMoveAtoms N + 2) + (1 + ((4 * D + 8) + 1)))

theorem ldwP1body_do {es : List ℕ} {ℓ K E : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) {i : ℕ} (hi : i < es.length)
    (s : TblSt 40 A) (acc0 : List (Fin (A + 4)))
    (hc : ldwCore s es.sum ℓ K es.length E)
    (hV : s.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (layLrank es ℓ i)) es.sum)
    (hjv : s.val vj = layLrank es ℓ i) (hoff : s.val voff = off es i) (hvi : s.val vi = i)
    (hacc : s.acc = (ldwRecs A w es.sum (layPre es ℓ K) (layLrank es ℓ i)).reverse ++ acc0)
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) :
    TblDo A W w (ldwBitCode vi ;;
      .ite vZero vbit (.ins (.add voff vLm1 vslot) ;; ldwMoveCode) (.ins (.zero vtmp)) ;;
      .ins (.add vi vOne vi1) ;; ldwEsCode vi1 ;; .ins (.sub voff ves voff)) s
      (fun s' => ldwCore s' es.sum ℓ K es.length E ∧
        s'.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (layLrank es ℓ (i + 1)))
          es.sum ∧ s'.val vj = layLrank es ℓ (i + 1) ∧
        (i + 1 < es.length → s'.val voff = off es (i + 1)) ∧ s'.val vi = i ∧
        s'.acc = (ldwRecs A w es.sum (layPre es ℓ K) (layLrank es ℓ (i + 1))).reverse ++ acc0)
      (ldwP1Atoms es.sum es.length) := by
  set N := es.sum with hN
  set D := es.length with hD
  set pre := layPre es ℓ K with hpre
  have hDN : D ≤ N := ldw_length_le_sum H
  have hℓ := H.ℓ_ge
  have hnd := layPre_nodup H
  have hlt := layPre_lt H
  have hPl := layPre_length_le H
  have hiW : i < W := by omega
  have hW2 : ∀ x ≤ N + 1, x < 2 ^ W := fun x hx =>
    lt_of_le_of_lt hx (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hNW))
  refine TblDo.mono (K := (4 * i + 5 + (1 + 1)) + ((ldwMoveAtoms N + 2) +
    (1 + ((4 * (i + 1) + 8) + 1)))) ?_ (fun _ h => h) (by unfold ldwP1Atoms; omega)
  -- the bit of axis i
  have hb := ldwBit_do (A := A) (W := W) (w := w) vi (by decide) s (by rw [hvi]; exact hiW) hc.two
  rw [hvi, hc.cE] at hb
  refine hb.seq fun s1 ⟨hbit1, hfr1, hacc1⟩ => ?_
  have c1 := hc.fr hfr1 (by decide)
  have hb2 : E / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hlong : ax es i = ℓ ↔ 0 < E / 2 ^ i % 2 := by rw [hE i hi]; omega
  have hV1 : s1.val vV = s.val vV := hfr1 _ (by decide)
  have hj1 : s1.val vj = s.val vj := hfr1 _ (by decide)
  have hoff1 : s1.val voff = s.val voff := hfr1 _ (by decide)
  have hvi1 : s1.val vi = i := by rw [hfr1 _ (by decide)]; exact hvi
  -- the move of a long axis
  have hite : TblDo A W w
      (.ite vZero vbit (.ins (.add voff vLm1 vslot) ;; ldwMoveCode) (.ins (.zero vtmp))) s1
      (fun s' => ldwCore s' N ℓ K D E ∧
        s'.val vV = ldwPack (N + 1) (layPos N pre (layLrank es ℓ (i + 1))) N ∧
        s'.val vj = layLrank es ℓ (i + 1) ∧ s'.val voff = off es i ∧ s'.val vi = i ∧
        s'.acc = (ldwRecs A w N pre (layLrank es ℓ (i + 1))).reverse ++ acc0)
      (ldwMoveAtoms N + 2) := by
    by_cases hl : ax es i = ℓ
    · have hlt' : 0 < E / 2 ^ i % 2 := hlong.1 hl
      refine TblDo.mono (K := (1 + ldwMoveAtoms N) + 1) ?_ (fun _ h => h) (by omega)
      refine TblDo.iteT (by rw [c1.zero, hbit1]; exact hlt') ?_
      have hsl : s1.val voff + s1.val vLm1 = pre.getD (layLrank es ℓ i) 0 := by
        rw [hoff1, hoff, c1.lm1, hpre, layPre_getD_long hi hl]
      have hjl : layLrank es ℓ i < pre.length := by
        have := ldw_lrank_lt hi hl
        rw [hpre, layPre_length]; omega
      have hslN : pre.getD (layLrank es ℓ i) 0 < N := by
        rw [List.getD_eq_getElem _ _ hjl]; exact hlt _ (List.getElem_mem hjl)
      refine (TblDo.insX (.add voff vLm1 vslot)
        (P := fun s2 => s2 = ⟨Function.update s1.val vslot (pre.getD (layLrank es ℓ i) 0), s1.acc⟩)
        (by simp only [TblIns.fits, hsl]; exact hW2 _ (by omega))
        (by simp [TblIns.exact, hsl])).seq fun s2 hs2 => ?_
      subst hs2
      have hm := ldwMove_do (A := A) (W := W) (w := w) (L := ℓ) (K := K) (D := D) (E := E) hnd hlt
        hPl hjl ⟨Function.update s1.val vslot (pre.getD (layLrank es ℓ i) 0), s1.acc⟩
        (c1.fr (M := [vslot]) (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          simp [Function.update_of_ne hx]) (by decide))
        (by simp only; rw [Function.update_of_ne (by decide), hV1, hV])
        (by simp only; rw [Function.update_of_ne (by decide), hj1, hjv])
        (by simp only; rw [Function.update_self]) hW hNW
      refine hm.mono (fun s' ⟨c', hV', hj', hfr', hacc'⟩ => ⟨c', ?_, ?_, ?_, ?_, ?_⟩) le_rfl
      · rw [hV', ldw_lrank_succ, ite_eq_left hl]
      · rw [hj', ldw_lrank_succ, ite_eq_left hl]
      · rw [hfr' _ (by decide)]; simp only; rw [Function.update_of_ne (by decide), hoff1, hoff]
      · rw [hfr' _ (by decide)]; simp only; rw [Function.update_of_ne (by decide), hvi1]
      · rw [hacc', ldw_lrank_succ, ite_eq_left hl, ldwRecs_succ, List.reverse_append, List.append_assoc]
        simp only
        rw [hacc1, hacc]
        rfl
    · have hlt' : ¬ 0 < E / 2 ^ i % 2 := fun h => hl (hlong.2 h)
      refine TblDo.mono (K := 1 + 1) ?_ (fun _ h => h) (by omega)
      refine TblDo.iteF (by rw [c1.zero, hbit1]; exact hlt') ?_
      refine TblDo.ins _ ?_
      have fr : ldwFr s1 (TblIns.run A W w (.zero vtmp) s1) [vtmp] := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp [TblIns.run, Function.update_of_ne hx]
      have hr : layLrank es ℓ (i + 1) = layLrank es ℓ i := by rw [ldw_lrank_succ, ite_eq_right hl]; rfl
      refine ⟨c1.fr fr (by decide), ?_, ?_, ?_, ?_, ?_⟩
      · rw [fr _ (by decide), hV1, hV, hr]
      · rw [fr _ (by decide), hj1, hjv, hr]
      · rw [fr _ (by decide), hoff1, hoff]
      · rw [fr _ (by decide), hvi1]
      · simp only [TblIns.run]
        rw [hacc1, hacc, hr]
  refine hite.seq fun s2 ⟨c2, hV2, hj2, hoff2, hvi2, hacc2⟩ => ?_
  -- i1 := i + 1, es := width of axis i + 1, off := off - es
  refine (TblDo.insX (.add vi vOne vi1)
    (P := fun s3 => s3 = ⟨Function.update s2.val vi1 (i + 1), s2.acc⟩)
    (by simp only [TblIns.fits, hvi2, c2.one]; exact hW2 _ (by omega))
    (by simp [TblIns.exact, hvi2, c2.one])).seq fun s3 hs3 => ?_
  subst hs3
  have c3 : ldwCore ⟨Function.update s2.val vi1 (i + 1), s2.acc⟩ N ℓ K D E :=
    c2.fr (M := [vi1]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]) (by decide)
  have hℓN : ℓ - 1 ≤ N := by
    have := off_add_ax_le es i
    have := hE i hi
    omega
  have he := ldwEs_do (A := A) (W := W) (w := w) vi1 (by decide)
    ⟨Function.update s2.val vi1 (i + 1), s2.acc⟩ (by simp; omega) c3.two
    (by rw [c3.lm1]; exact hW2 _ (by omega))
  rw [c3.lm1, c3.cE] at he
  have hvi1' : (⟨Function.update s2.val vi1 (i + 1), s2.acc⟩ : TblSt 40 A).val vi1 = i + 1 :=
    Function.update_self (f := s2.val) vi1 (i + 1)
  rw [hvi1'] at he
  refine he.seq fun s4 ⟨hes4, _, hfr4, hacc4⟩ => ?_
  have c4 := c3.fr hfr4 (by decide)
  have hoff4 : s4.val voff = off es i := by
    rw [hfr4 _ (by decide)]; simp only; rw [Function.update_of_ne (by decide), hoff2]
  refine TblDo.ins _ ?_
  have fr5 : ldwFr s4 (TblIns.run A W w (.sub voff ves voff) s4) [voff] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [TblIns.run, Function.update_of_ne hx]
  have hall : ∀ x, x ∉ [vpw, vk2, vtmp, vbit, ves, voff] →
      (TblIns.run A W w (.sub voff ves voff) s4).val x = s2.val x ∨ x = vi1 := by
    intro x hx
    by_cases hx1 : x = vi1
    · exact Or.inr hx1
    · left
      rw [fr5 x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro h; exact hx (by
        simp [h])), hfr4 x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)]
      exact Function.update_of_ne hx1 _ _
  refine ⟨c4.fr fr5 (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rcases hall vV (by decide) with e | e
    · rw [e, hV2]
    · exact absurd e (by decide)
  · rcases hall vj (by decide) with e | e
    · rw [e, hj2]
    · exact absurd e (by decide)
  · intro hi1
    simp only [TblIns.run, Function.update_self, hoff4, hes4]
    rw [hE (i + 1) hi1 |>.symm, ldw_off_succ hi1]
    rw [show ax es (i + 1) + off es (i + 1) + 2 ^ W - ax es (i + 1) = off es (i + 1) + 2 ^ W by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (hW2 _ (by have := off_add_ax_le es (i + 1); omega))]
  · rcases hall vi (by decide) with e | e
    · rw [e, hvi2]
    · exact absurd e (by decide)
  · simp only [TblIns.run]
    rw [hacc4]
    simp only
    rw [hacc2]

/-! ### The low slots -/

/-- The atoms of one iteration of the inner loop of `ldwPart2`. -/
def ldwP2Atoms (N D : ℕ) : ℕ := 1 + (1 + (1 + (ldwMoveAtoms N + (1 + ((4 * D + 8) + 1)))))

theorem ldwP2body_do {es : List ℕ} {ℓ K E : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) {h' i : ℕ} (hh : h' < layB ℓ K)
    (hi : i < es.length) (s : TblSt 40 A) (acc0 : List (Fin (A + 4)))
    (hc : ldwCore s es.sum ℓ K es.length E)
    (hV : s.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K)
      ((layLongs es ℓ).length + h' * es.length + i)) es.sum)
    (hjv : s.val vj = (layLongs es ℓ).length + h' * es.length + i) (hoff : s.val voff = off es i)
    (hvi : s.val vi = i) (hvh : s.val vh = h')
    (hacc : s.acc = (ldwRecs A w es.sum (layPre es ℓ K)
      ((layLongs es ℓ).length + h' * es.length + i)).reverse ++ acc0)
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) :
    TblDo A W w (.ins (.sub vb vOne vtmp) ;; .ins (.sub vtmp vh vtmp) ;;
      .ins (.add voff vtmp vslot) ;; ldwMoveCode ;; .ins (.add vi vOne vi1) ;; ldwEsCode vi1 ;;
      .ins (.sub voff ves voff)) s
      (fun s' => ldwCore s' es.sum ℓ K es.length E ∧
        s'.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K)
          ((layLongs es ℓ).length + h' * es.length + (i + 1))) es.sum ∧
        s'.val vj = (layLongs es ℓ).length + h' * es.length + (i + 1) ∧
        (i + 1 < es.length → s'.val voff = off es (i + 1)) ∧ s'.val vi = i ∧ s'.val vh = h' ∧
        s'.acc = (ldwRecs A w es.sum (layPre es ℓ K)
          ((layLongs es ℓ).length + h' * es.length + (i + 1))).reverse ++ acc0)
      (ldwP2Atoms es.sum es.length) := by
  set N := es.sum with hN
  set D := es.length with hD
  set pre := layPre es ℓ K with hpre
  set b := layB ℓ K with hb
  set j := (layLongs es ℓ).length + h' * D + i with hj
  have hDN : D ≤ N := ldw_length_le_sum H
  have hnd := layPre_nodup H
  have hlt := layPre_lt H
  have hPl := layPre_length_le H
  have hW2 : ∀ x ≤ N + 1, x < 2 ^ W := fun x hx =>
    lt_of_le_of_lt hx (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hNW))
  have hjl : j < pre.length := by
    have e1 : pre.length = (layLongs es ℓ).length + b * D := layPre_length
    rw [e1, hj]
    have : (h' + 1) * D ≤ b * D := Nat.mul_le_mul_right D (by omega)
    rw [Nat.add_mul] at this
    omega
  have hslot : off es i + (b - 1 - h') = pre.getD j 0 := by
    have e := layPre_getD_low (K := K) hi (show b - 1 - h' < layB ℓ K by omega)
    rw [show layB ℓ K - 1 - (b - 1 - h') = h' by omega] at e
    rw [hj, Nat.add_assoc, ← e]
  have hslN : pre.getD j 0 < N := by
    rw [List.getD_eq_getElem _ _ hjl]; exact hlt _ (List.getElem_mem hjl)
  refine TblDo.mono (K := 1 + (1 + (1 + (ldwMoveAtoms N + (1 + ((4 * (i + 1) + 8) + 1))))))
    ?_ (fun _ h => h) (by unfold ldwP2Atoms; omega)
  -- tmp := b - 1 - h', slot := off + tmp
  have hbv : s.val vb = b := by rw [hc.cb, hb]; rfl
  have hbN : b ≤ N := by
    have := H.b_lt; have := H.K_le; have := off_add_ax_le es i; have := hE i hi
    rw [hb]; omega
  refine (TblDo.insX (.sub vb vOne vtmp)
    (P := fun s1 => s1 = ⟨Function.update s.val vtmp (b - 1), s.acc⟩)
    (by simp only [TblIns.fits, hbv, hc.one]; exact ⟨by omega, hW2 _ (by omega)⟩)
    (by simp [TblIns.exact, hbv, hc.one])).seq fun s1 hs1 => ?_
  subst hs1
  refine (TblDo.insX (.sub vtmp vh vtmp)
    (P := fun s2 => s2 = ⟨Function.update s.val vtmp (b - 1 - h'), s.acc⟩)
    (by
      simp only [TblIns.fits, Function.update_self]
      rw [Function.update_of_ne (by decide), hvh]
      exact ⟨by omega, hW2 _ (by omega)⟩)
    (by
      simp only [TblIns.exact, Function.update_self]
      rw [Function.update_of_ne (by decide), hvh, Function.update_idem])).seq fun s2 hs2 => ?_
  subst hs2
  refine (TblDo.insX (.add voff vtmp vslot)
    (P := fun s3 => s3 = ⟨Function.update (Function.update s.val vtmp (b - 1 - h')) vslot
      (pre.getD j 0), s.acc⟩)
    (by
      simp only [TblIns.fits, Function.update_self]
      rw [Function.update_of_ne (by decide), hoff, hslot]; exact hW2 _ (by omega))
    (by
      simp only [TblIns.exact, Function.update_self]
      rw [Function.update_of_ne (by decide), hoff, hslot])).seq fun s3 hs3 => ?_
  subst hs3
  set s3 : TblSt 40 A := ⟨Function.update (Function.update s.val vtmp (b - 1 - h')) vslot
      (pre.getD j 0), s.acc⟩ with hs3
  have fr3 : ldwFr s s3 [vtmp, vslot] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hs3, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
  have c3 := hc.fr fr3 (by decide)
  have hm := ldwMove_do (A := A) (W := W) (w := w) (L := ℓ) (K := K) (D := D) (E := E) hnd hlt hPl
    hjl s3 c3 (by rw [fr3 _ (by decide), hV]) (by rw [fr3 _ (by decide), hjv])
    (Function.update_self (f := Function.update s.val vtmp (b - 1 - h')) vslot (pre.getD j 0))
    hW hNW
  refine hm.seq fun s4 ⟨c4, hV4, hj4, hfr4, hacc4⟩ => ?_
  have hvi4 : s4.val vi = i := by rw [hfr4 _ (by decide), fr3 _ (by decide), hvi]
  have hvh4 : s4.val vh = h' := by rw [hfr4 _ (by decide), fr3 _ (by decide), hvh]
  have hoff4 : s4.val voff = off es i := by rw [hfr4 _ (by decide), fr3 _ (by decide), hoff]
  refine (TblDo.insX (.add vi vOne vi1)
    (P := fun s5 => s5 = ⟨Function.update s4.val vi1 (i + 1), s4.acc⟩)
    (by simp only [TblIns.fits, hvi4, c4.one]; exact hW2 _ (by omega))
    (by simp [TblIns.exact, hvi4, c4.one])).seq fun s5 hs5 => ?_
  subst hs5
  have c5 : ldwCore ⟨Function.update s4.val vi1 (i + 1), s4.acc⟩ N ℓ K D E :=
    c4.fr (M := [vi1]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]) (by decide)
  have hℓN : ℓ - 1 ≤ N := by
    have := off_add_ax_le es i
    have := hE i hi
    omega
  have he := ldwEs_do (A := A) (W := W) (w := w) vi1 (by decide)
    ⟨Function.update s4.val vi1 (i + 1), s4.acc⟩ (by simp; omega) c5.two
    (by rw [c5.lm1]; exact hW2 _ (by omega))
  rw [c5.lm1, c5.cE] at he
  have hvi1' : (⟨Function.update s4.val vi1 (i + 1), s4.acc⟩ : TblSt 40 A).val vi1 = i + 1 :=
    Function.update_self (f := s4.val) vi1 (i + 1)
  rw [hvi1'] at he
  refine he.seq fun s6 ⟨hes6, _, hfr6, hacc6⟩ => ?_
  have c6 := c5.fr hfr6 (by decide)
  refine TblDo.ins _ ?_
  have fr7 : ldwFr s6 (TblIns.run A W w (.sub voff ves voff) s6) [voff] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [TblIns.run, Function.update_of_ne hx]
  have hall : ∀ x, x ∉ [vpw, vk2, vtmp, vbit, ves, voff, vi1] →
      (TblIns.run A W w (.sub voff ves voff) s6).val x = s4.val x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [fr7 x (by simp [hx.2.2.2.2.2.1]), hfr6 x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
      hx.2.2.2.2.1])]
    exact Function.update_of_ne hx.2.2.2.2.2.2 _ _
  have hoff6 : s6.val voff = off es i := by
    rw [hfr6 _ (by decide)]; simp only; rw [Function.update_of_ne (by decide), hoff4]
  refine ⟨c6.fr fr7 (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hall _ (by decide), hV4]; rfl
  · rw [hall _ (by decide), hj4]; rfl
  · intro hi1
    simp only [TblIns.run, Function.update_self, hoff6, hes6]
    rw [hE (i + 1) hi1 |>.symm, ldw_off_succ hi1]
    rw [show ax es (i + 1) + off es (i + 1) + 2 ^ W - ax es (i + 1) = off es (i + 1) + 2 ^ W by
      omega, Nat.add_mod_right, Nat.mod_eq_of_lt (hW2 _ (by have := off_add_ax_le es (i + 1); omega))]
  · rw [hall _ (by decide), hvi4]
  · rw [hall _ (by decide), hvh4]
  · simp only [TblIns.run]
    rw [hacc6]
    show s4.acc = _
    rw [hacc4, hacc, show (layLongs es ℓ).length + h' * D + (i + 1) = j + 1 by omega, ldwRecs_succ,
      List.reverse_append, List.append_assoc]
    rfl

/-! ### The loops -/

/-- The atoms of `ldwPart1`. -/
def ldwPart1Atoms (N D : ℕ) : ℕ := 8 + (1 + (1 + (D * (ldwP1Atoms N D + 1 + 2) + 2)))

theorem ldwPart1_do {es : List ℕ} {ℓ K E : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (s : TblSt 40 A)
    (hc : ldwCore s es.sum ℓ K es.length E)
    (hV : s.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) 0) es.sum)
    (hjv : s.val vj = 0) (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W)
    (hℓW : ℓ < 2 ^ W) :
    TblDo A W w ldwPart1 s (fun s' => ldwCore s' es.sum ℓ K es.length E ∧
      s'.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (layLongs es ℓ).length)
        es.sum ∧ s'.val vj = (layLongs es ℓ).length ∧
      s'.acc = (ldwRecs A w es.sum (layPre es ℓ K) (layLongs es ℓ).length).reverse ++ s.acc)
      (ldwPart1Atoms es.sum es.length) := by
  have hDN : es.length ≤ es.sum := ldw_length_le_sum H
  have hℓ := H.ℓ_ge
  have hW2 : ∀ x ≤ es.sum + 1, x < 2 ^ W := fun x hx =>
    lt_of_le_of_lt hx (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hNW))
  -- the width of axis 0, off := N - es
  have he := ldwEs_do (A := A) (W := W) (w := w) vZero (by decide) s (by rw [hc.zero]; omega)
    hc.two (by rw [hc.lm1]; omega)
  rw [hc.zero, hc.lm1, hc.cE] at he
  refine he.seq fun s1 ⟨hes1, _, hfr1, hacc1⟩ => ?_
  have c1 := hc.fr hfr1 (by decide)
  refine (TblDo.ins (.sub vN ves voff)
    (P := fun s2 => s2 = TblIns.run A W w (.sub vN ves voff) s1) rfl).seq fun s2 hs2 => ?_
  subst hs2
  set s2 := TblIns.run A W w (.sub vN ves voff) s1 with hs2
  have fr2 : ldwFr s1 s2 [voff] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [hs2, TblIns.run, Function.update_of_ne hx]
  have c2 := c1.fr fr2 (by decide)
  have hoff2 : 0 < es.length → s2.val voff = off es 0 := by
    intro hD0
    simp only [hs2, TblIns.run, Function.update_self, c1.cN, hes1]
    have e0 := ldw_off_zero hD0
    have e1 := hE 0 hD0
    rw [← e1, e0, show ax es 0 + off es 0 + 2 ^ W - ax es 0 = off es 0 + 2 ^ W by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (hW2 _ (by omega))]
  have hfr12 : ∀ x, x ∉ [vpw, vk2, vtmp, vbit, ves, voff] → s2.val x = s.val x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [fr2 x (by simp [hx.2.2.2.2.2]), hfr1 x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
      hx.2.2.2.2.1])]
  -- the loop over the axes
  refine TblDo.for es.length (ldwP1Atoms es.sum es.length) c2.cD
    (lt_of_le_of_lt hDN (hW2 _ (by omega)) |>.trans_le le_rfl) (by decide)
    (fun i t => ldwCore t es.sum ℓ K es.length E ∧
      t.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (layLrank es ℓ i)) es.sum ∧
      t.val vj = layLrank es ℓ i ∧ (i < es.length → t.val voff = off es i) ∧
      t.acc = (ldwRecs A w es.sum (layPre es ℓ K) (layLrank es ℓ i)).reverse ++ s.acc)
    ⟨c2.fr (M := [vi]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]) (by decide), ?_, ?_, ?_, ?_⟩ ?_ ?_
  · simp only; rw [Function.update_of_ne (by decide), hfr12 _ (by decide), hV]; rfl
  · simp only; rw [Function.update_of_ne (by decide), hfr12 _ (by decide), hjv]; rfl
  · intro hD0; simp only; rw [Function.update_of_ne (by decide)]; exact hoff2 hD0
  · show s2.acc = _
    rw [show s2.acc = s1.acc from rfl, hacc1]
    simp [ldwRecs, layLrank]
  · intro i hi t ⟨ct, hVt, hjt, hofft, hacct⟩ hti hD
    refine (ldwP1body_do (A := A) (W := W) (w := w) H hE hi t s.acc ct hVt hjt (hofft hi) hti
      hacct hW hNW).mono (fun t' ⟨c', hV', hj', hoff', hvi', hacc'⟩ =>
        ⟨hvi', c'.cD, ?_⟩) le_rfl
    refine ⟨c'.fr (M := [vi]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]) (by decide), ?_, ?_, ?_, ?_⟩
    · simp only; rw [Function.update_of_ne (by decide), hV']
    · simp only; rw [Function.update_of_ne (by decide), hj']
    · intro hi1; simp only; rw [Function.update_of_ne (by decide)]; exact hoff' hi1
    · exact hacc'
  · intro t ⟨ct, hVt, hjt, _, hacct⟩ _ _
    exact ⟨ct, hVt, hjt, hacct⟩

/-- The atoms of one iteration of the outer loop of `ldwPart2`. -/
def ldwP2OAtoms (N D : ℕ) : ℕ := 8 + (1 + (1 + (D * (ldwP2Atoms N D + 1 + 2) + 2)))

/-- The atoms of `ldwPart2`. -/
def ldwPart2Atoms (N D b : ℕ) : ℕ := 1 + (b * (ldwP2OAtoms N D + 1 + 2) + 2)

theorem ldwPart2_do {es : List ℕ} {ℓ K E : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (s : TblSt 40 A)
    (acc0 : List (Fin (A + 4))) (hc : ldwCore s es.sum ℓ K es.length E)
    (hV : s.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (layLongs es ℓ).length)
      es.sum)
    (hjv : s.val vj = (layLongs es ℓ).length)
    (hacc : s.acc = (ldwRecs A w es.sum (layPre es ℓ K) (layLongs es ℓ).length).reverse ++ acc0)
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) (hℓW : ℓ < 2 ^ W) :
    TblDo A W w ldwPart2 s (fun s' => ldwCore s' es.sum ℓ K es.length E ∧
      s'.acc = (ldwRecs A w es.sum (layPre es ℓ K) (layPre es ℓ K).length).reverse ++ acc0)
      (ldwPart2Atoms es.sum es.length (layB ℓ K)) := by
  have hDN : es.length ≤ es.sum := ldw_length_le_sum H
  have hℓ := H.ℓ_ge
  have hW2 : ∀ x ≤ es.sum + 1, x < 2 ^ W := fun x hx =>
    lt_of_le_of_lt hx (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hNW))
  set L := (layLongs es ℓ).length with hL
  set D := es.length with hD
  have hbW : layB ℓ K < 2 ^ W := by
    have := H.b_lt; have := H.K_le
    exact lt_of_le_of_lt (by omega) hℓW
  refine TblDo.for (layB ℓ K) (ldwP2OAtoms es.sum D) (by rw [hc.cb]; rfl) hbW (by decide)
    (fun h' t => ldwCore t es.sum ℓ K D E ∧
      t.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (L + h' * D)) es.sum ∧
      t.val vj = L + h' * D ∧
      t.acc = (ldwRecs A w es.sum (layPre es ℓ K) (L + h' * D)).reverse ++ acc0)
    ⟨hc.fr (M := [vh]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]) (by decide), ?_, ?_, ?_⟩ ?_ ?_
  · simp only; rw [Function.update_of_ne (by decide), hV]; simp
  · simp only; rw [Function.update_of_ne (by decide), hjv]; simp
  · show s.acc = _
    rw [hacc]; simp
  · intro h' hh t ⟨ct, hVt, hjt, hacct⟩ hth _
    -- the width of axis 0, off := N - es
    refine TblDo.mono (K := 8 + (1 + (1 + (D * (ldwP2Atoms es.sum D + 1 + 2) + 2)))) ?_
      (fun _ h => h) (by unfold ldwP2OAtoms; omega)
    have he := ldwEs_do (A := A) (W := W) (w := w) vZero (by decide) t (by rw [ct.zero]; omega)
      ct.two (by rw [ct.lm1]; omega)
    rw [ct.zero, ct.lm1, ct.cE] at he
    refine he.seq fun t1 ⟨hes1, _, hfr1, hacc1⟩ => ?_
    have c1 := ct.fr hfr1 (by decide)
    refine (TblDo.ins (.sub vN ves voff)
      (P := fun t2 => t2 = TblIns.run A W w (.sub vN ves voff) t1) rfl).seq fun t2 ht2 => ?_
    subst ht2
    set t2 := TblIns.run A W w (.sub vN ves voff) t1 with ht2
    have fr2 : ldwFr t1 t2 [voff] := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [ht2, TblIns.run, Function.update_of_ne hx]
    have c2 := c1.fr fr2 (by decide)
    have hoff2 : 0 < D → t2.val voff = off es 0 := by
      intro hD0
      simp only [ht2, TblIns.run, Function.update_self, c1.cN, hes1]
      have e0 := ldw_off_zero hD0
      have e1 := hE 0 hD0
      rw [← e1, e0, show ax es 0 + off es 0 + 2 ^ W - ax es 0 = off es 0 + 2 ^ W by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (hW2 _ (by omega))]
    have hfr12 : ∀ x, x ∉ [vpw, vk2, vtmp, vbit, ves, voff] → t2.val x = t.val x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [fr2 x (by simp [hx.2.2.2.2.2]), hfr1 x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
        hx.2.2.2.2.1])]
    refine (TblDo.for D (ldwP2Atoms es.sum D) c2.cD
      (lt_of_le_of_lt hDN (hW2 _ (by omega))) (by decide)
      (fun i u => ldwCore u es.sum ℓ K D E ∧
        u.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (L + h' * D + i)) es.sum ∧
        u.val vj = L + h' * D + i ∧ (i < D → u.val voff = off es i) ∧ u.val vh = h' ∧
        u.acc = (ldwRecs A w es.sum (layPre es ℓ K) (L + h' * D + i)).reverse ++ acc0)
      ⟨c2.fr (M := [vi]) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp [Function.update_of_ne hx]) (by decide), ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_)
    · simp only; rw [Function.update_of_ne (by decide), hfr12 _ (by decide), hVt]; rfl
    · simp only; rw [Function.update_of_ne (by decide), hfr12 _ (by decide), hjt]; rfl
    · intro hD0; simp only; rw [Function.update_of_ne (by decide)]; exact hoff2 hD0
    · simp only; rw [Function.update_of_ne (by decide), hfr12 _ (by decide), hth]
    · show t2.acc = _
      rw [show t2.acc = t1.acc from rfl, hacc1, hacct]; rfl
    · intro i hi u ⟨cu, hVu, hju, hoffu, hhu, haccu⟩ hui _
      refine (ldwP2body_do (A := A) (W := W) (w := w) H hE hh hi u acc0 cu hVu hju (hoffu hi) hui
        hhu haccu hW hNW).mono (fun u' ⟨c', hV', hj', hoff', hvi', hvh', hacc'⟩ =>
          ⟨hvi', c'.cD, ?_⟩) le_rfl
      refine ⟨c'.fr (M := [vi]) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp [Function.update_of_ne hx]) (by decide), ?_, ?_, ?_, ?_, ?_⟩
      · simp only; rw [Function.update_of_ne (by decide), hV']
      · simp only; rw [Function.update_of_ne (by decide), hj']
      · intro hi1; simp only; rw [Function.update_of_ne (by decide)]; exact hoff' hi1
      · simp only; rw [Function.update_of_ne (by decide), hvh']
      · exact hacc'
    · intro u ⟨cu, hVu, hju, _, hhu, haccu⟩ _ _
      refine ⟨hhu, cu.cb.trans rfl, ?_⟩
      have e : L + h' * D + D = L + (h' + 1) * D := by ring
      refine ⟨cu.fr (M := [vh]) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp [Function.update_of_ne hx]) (by decide), ?_, ?_, ?_⟩
      · simp only; rw [Function.update_of_ne (by decide), hVu, e]
      · simp only; rw [Function.update_of_ne (by decide), hju, e]
      · rw [haccu, e]
  · intro t ⟨ct, _, _, hacct⟩ _ _
    refine ⟨ct, ?_⟩
    rw [hacct, layPre_length]

/-! ### The whole writer -/

theorem ldwPack_zero (R : ℕ) : ∀ M, ldwPack R (fun _ => 0) M = 0
  | 0 => rfl
  | M + 1 => by rw [ldwPack, ldwPack_zero R M]; simp

/-- The atoms of `ldw1Code`. -/
def ldw1Atoms (N D b : ℕ) : ℕ :=
  (10 + 1 + (N * (1 + 8) + 7)) + (ldwPart1Atoms N D + ldwPart2Atoms N D b)

/-- **The writer of the single-bit move stream.** From the inputs `N = es.sum`, `ℓ`, `K`,
`D = es.length` and the word `E` of the long axes in the variables `0 … 4`, `ldw1Code` emits the
description stream `ldlBitStream A w (layBits es ℓ K)` of the prefix moves of the layout, for
every emission width `w`, within `ldw1Atoms N D b` atoms (`b = layB ℓ K`), provided the words
are wide enough: `(N + 1)^N < 2^W`, `N < W`, `2 ≤ W`, `ℓ < 2^W`. -/
theorem ldw1_do {es : List ℕ} {ℓ K E : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (st : TblSt 40 A)
    (hN : st.val vN = es.sum) (hL : st.val vL = ℓ) (hK : st.val vK = K)
    (hD : st.val vD = es.length) (hEv : st.val vE = E) (hW : (es.sum + 1) ^ es.sum < 2 ^ W)
    (hNW : es.sum < W) (h2W : 2 ≤ W) (hℓW : ℓ < 2 ^ W) :
    TblDo A W w ldw1Code st
      (fun s => s.acc = (ldlBitStream A w (layBits es ℓ K)).reverse ++ st.acc)
      (ldw1Atoms es.sum es.length (layB ℓ K)) := by
  have hℓ := H.ℓ_ge
  have hW2 : ∀ x ≤ es.sum + 1, x < 2 ^ W := fun x hx =>
    lt_of_le_of_lt hx (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hNW))
  have h4 : 4 ≤ 2 ^ W := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h2W
  -- the constants
  set l : List (TblIns 40) := [.zero vZero, .zero vOne, .inc vOne, .zero vTwo, .inc vTwo, .inc vTwo,
    .sub vL vOne vLm1, .mod vLm1 vK vb, .add vN vOne vR, .zero vV] with hl
  have hblk : TblDo A W w (tblBlock 40 l (.zero vj)) st
      (fun s => ldwCore s es.sum ℓ K es.length E ∧ s.val vV = 0 ∧ s.val vj = 0 ∧
        s.acc = st.acc) (l.length + 1) := by
    refine TblDo.block l (.zero vj) ?_ ?_
    · simp [hl, tblFitsList, TblIns.fits, TblIns.exact, hL, hN]
      exact ⟨by omega, by omega, ⟨by omega, hℓW⟩, hW2 _ le_rfl⟩
    · simp only [hl, List.cons_append, List.nil_append, tblExactList, TblIns.exact]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
        simp [hL, hN, hK, hD, hEv]
  refine TblDo.mono (K := (10 + 1 + (es.sum * (1 + 8) + 7)) + (ldwPart1Atoms es.sum es.length +
    ldwPart2Atoms es.sum es.length (layB ℓ K))) ?_ (fun _ h => h) (by unfold ldw1Atoms; omega)
  refine TblDo.seq (K₁ := 10 + 1 + (es.sum * (1 + 8) + 7))
    (P₁ := fun s => ldwCore s es.sum ℓ K es.length E ∧
      s.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) 0) es.sum ∧ s.val vj = 0 ∧
      s.acc = st.acc) ?_ fun s ⟨cs, hVs, hjs, haccs⟩ => ?_
  · refine hblk.seq fun s1 ⟨c1, hV1, hj1, hacc1⟩ => ?_
    have hm := ldwMap_do (A := A) (W := W) (w := w) (V := vV) (V2 := vV2) (Rc := vRc) (R := vR)
      (c := vc) (M := vN) (t := vt) (y := vy) (y2 := vy2) (blk := .ins (.copy vc vy2)) (by decide)
      s1 (f := fun _ => 0) (G := fun c _ => c) c1.cN c1.cR (by omega)
      (by rw [hV1, ldwPack_zero]) (fun c _ => by omega) (fun c hc => by omega) hW
      (hW2 _ (by omega)) [] (by simp) 1
      (fun j' _ s' _ hc' _ _ => TblDo.ins _ ⟨by simp [TblIns.run, hc'], fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp [TblIns.run, Function.update_of_ne hx], rfl⟩)
    refine hm.mono (fun s2 ⟨hV2, hfr2, hacc2⟩ => ⟨c1.fr hfr2 (by decide), ?_, ?_, ?_⟩) le_rfl
    · rw [hV2]; exact ldwPack_congr fun c _ => rfl
    · rw [hfr2 _ (by decide), hj1]
    · rw [hacc2, hacc1]
  · refine (ldwPart1_do (A := A) (W := W) (w := w) H hE s cs hVs hjs hW hNW hℓW).seq
      fun s1 ⟨c1, hV1, hj1, hacc1⟩ => ?_
    refine (ldwPart2_do (A := A) (W := W) (w := w) H hE s1 st.acc c1 hV1 hj1
      (by rw [hacc1, haccs]) hW hNW hℓW).mono (fun s2 ⟨_, hacc2⟩ => ?_) le_rfl
    rw [hacc2, ldwRecs_layBits]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
