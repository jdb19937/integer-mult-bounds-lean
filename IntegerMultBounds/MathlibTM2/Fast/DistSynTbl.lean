module

public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGenM
public import IntegerMultBounds.MathlibTM2.Fast.TwiddleL
public import IntegerMultBounds.MathlibTM2.Node.TopRec

/-!
# The parameter wires of the synthetic transforms: the table program

The table-machine programs (`IntegerMultBounds.MathlibTM2.Fast.TableVM`, emission width `1`) that compute the wires
of the synthetic transforms from the distributed parameters `N = es.sum`, `ℓ`, `K`,
`D = es.length` and the long-axis word `E` (bit `i` of `E` set iff axis `i` has `ℓ` bits):

* `ldw1Code` (`Fast/LoadLayoutGenM.lean`) is reused for the prefix moves of the layout:
  `dsyLay_do` strengthens `ldw1_do` with the packed positions
  `layPos N (layPre es ℓ K) |layPre es ℓ K|` left on `vV`.
* Every wire is emitted as pair symbols of width `1`: `dsyT A = pairSym A true false` stands for
  a tick and `dsyF A = pairSym A false false` for `bitSymbol false` (`dsyEnc`); the host maps them
  back (`Fast/DistSynHost.lean`).
* `dsyCodeB`: `(ℓ - 1) mod K` ticks; `dsyCodeLg`: `N - D (ℓ - 1)` ticks (the number of long axes,
  `lay_sum`); `dsyCodeL`: `ℓ` ticks; `dsyCodeNr`: `ℓ` ticks if some axis is long, `ℓ - 1`
  otherwise (`dsyNr`); `dsyCodeRec`: the record `topRec es` of the axis widths;
  `dsyCodePos`: the position table `twPosReg A N (dsyPos es ℓ K)` of the layout, where
  `dsyPos es ℓ K k = layChunkFun K (layTr D q) (layPos N pre |pre| k)` is `layPerm es ℓ K k`
  (`layRun_moves`, `layPerm_apply`).
* `DsyInv`: the invariant between the phases (the constants `ldwCore` and the positions on `vV`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Host


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
local notation "vLg" => (34 : Fin 40)
local notation "vNr" => (35 : Fin 40)
local notation "vq" => (36 : Fin 40)
local notation "vm" => (37 : Fin 40)
local notation "vKm" => (38 : Fin 40)
local notation "vp" => (39 : Fin 40)

/-! ### Symbols -/

/-- The pair symbol standing for a tick. -/
def dsyT (A : ℕ) : Fin (A + 4) := pairSym A true false

/-- The pair symbol standing for `bitSymbol false`. -/
def dsyF (A : ℕ) : Fin (A + 4) := pairSym A false false

/-- The encoding of a tick / any other symbol as a pair symbol. -/
def dsyEnc (A : ℕ) (x : Fin (A + 4)) : Fin (A + 4) := pairSym A (decide (x = tick)) false

@[simp] lemma dsyEnc_tick (A : ℕ) : dsyEnc A tick = dsyT A := by simp [dsyEnc, dsyT]

@[simp] lemma dsyEnc_false (A : ℕ) : dsyEnc A (bitSymbol false) = dsyF A := by
  simp [dsyEnc, dsyF, tick, bitSymbol, Fin.ext_iff]

lemma dsyEnc_topSep (A : ℕ) : dsyEnc A topSep = dsyF A := dsyEnc_false A

theorem dsyPairs_one (A x y : ℕ) :
    tblPairs A 1 x y = [pairSym A (x.testBit 0) (y.testBit 0)] := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i = 0 := by simp at h1; omega
  subst hi
  rw [tbl_pairs_getElem A 1 x y 0 (by norm_num)]
  rfl

variable {A W : ℕ}

/-- One emission of width `1`. -/
theorem dsyEmit_do (a b : Fin 40) (s : TblSt 40 A) :
    TblDo A W 1 (.ins (.emit a b)) s
      (fun s' => s' = ⟨s.val, pairSym A ((s.val a).testBit 0) ((s.val b).testBit 0) :: s.acc⟩)
      1 :=
  TblDo.ins _ (by simp [TblIns.run, dsyPairs_one])

/-! ### Tick loops -/

/-- `c` ticks (as `dsyT`), counting on `i`. -/
def dsyTicks (i c : Fin 40) : TblCode 40 := tblFor i c (.ins (.emit vOne vZero))

/-- `c` zeros (as `dsyF`), counting on `i`. -/
def dsyZeros (i c : Fin 40) : TblCode 40 := tblFor i c (.ins (.emit vZero vZero))

/-- The atoms of a loop of `c` emissions. -/
def dsyLoopAtoms (c : ℕ) : ℕ := 1 + (c * (1 + 1 + 2) + 2)

theorem dsyLoop_do {i c a b : Fin 40} (hic : i ≠ c) (hia : i ≠ a) (hib : i ≠ b)
    (s : TblSt 40 A) (hcW : s.val c < 2 ^ W) :
    TblDo A W 1 (tblFor i c (.ins (.emit a b))) s
      (fun s' => s'.acc = List.replicate (s.val c)
          (pairSym A ((s.val a).testBit 0) ((s.val b).testBit 0)) ++ s.acc ∧
        ldwFr s s' [i] ∧ s'.val i = s.val c) (dsyLoopAtoms (s.val c)) := by
  set X := pairSym A ((s.val a).testBit 0) ((s.val b).testBit 0) with hX
  refine TblDo.for (s.val c) 1 rfl hcW hic
    (fun j t => t.acc = List.replicate j X ++ s.acc ∧ ldwFr s t [i])
    ⟨by simp, fun x hx => by simp [Function.update_of_ne (by simpa using hx)]⟩ ?_ ?_
  · intro j hj t ⟨hacc, hfr⟩ hti htc
    refine (dsyEmit_do a b t).mono (fun t' ht' => ?_) le_rfl
    subst ht'
    have ea : t.val a = s.val a := hfr a (by rw [List.mem_singleton]; exact hia.symm)
    have eb : t.val b = s.val b := hfr b (by rw [List.mem_singleton]; exact hib.symm)
    refine ⟨hti, htc, ?_, fun x hx => ?_⟩
    · show pairSym A ((t.val a).testBit 0) ((t.val b).testBit 0) :: t.acc = _
      rw [hacc, List.replicate_succ, ea, eb]
      rfl
    · show Function.update t.val i (j + 1) x = s.val x
      rw [Function.update_of_ne (by simpa using hx), hfr x hx]
  · intro t ⟨hacc, hfr⟩ hti _
    exact ⟨hacc, hfr, hti⟩

theorem dsyTicks_do {i c : Fin 40} (hic : i ≠ c) (hi1 : i ≠ vOne) (hi0 : i ≠ vZero)
    (s : TblSt 40 A) (h1 : s.val vOne = 1) (h0 : s.val vZero = 0) (hcW : s.val c < 2 ^ W) :
    TblDo A W 1 (dsyTicks i c) s
      (fun s' => s'.acc = List.replicate (s.val c) (dsyT A) ++ s.acc ∧ ldwFr s s' [i] ∧
        s'.val i = s.val c) (dsyLoopAtoms (s.val c)) := by
  have h := dsyLoop_do (W := W) hic hi1 hi0 s hcW
  rw [h1, h0] at h
  exact h

theorem dsyZeros_do {i c : Fin 40} (hic : i ≠ c) (hi0 : i ≠ vZero)
    (s : TblSt 40 A) (h0 : s.val vZero = 0) (hcW : s.val c < 2 ^ W) :
    TblDo A W 1 (dsyZeros i c) s
      (fun s' => s'.acc = List.replicate (s.val c) (dsyF A) ++ s.acc ∧ ldwFr s s' [i] ∧
        s'.val i = s.val c) (dsyLoopAtoms (s.val c)) := by
  have h := dsyLoop_do (W := W) hic hi0 hi0 s hcW
  rw [h0] at h
  exact h

/-! ### The prefix moves, with the positions -/

/-- `ldwPart2` leaves the positions after all prefix moves on `vV`. -/
theorem dsyPart2_do {es : List ℕ} {ℓ K E : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (s : TblSt 40 A)
    (acc0 : List (Fin (A + 4))) (hc : ldwCore s es.sum ℓ K es.length E)
    (hV : s.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (layLongs es ℓ).length)
      es.sum)
    (hjv : s.val vj = (layLongs es ℓ).length)
    (hacc : s.acc = (ldwRecs A 1 es.sum (layPre es ℓ K) (layLongs es ℓ).length).reverse ++ acc0)
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) (hℓW : ℓ < 2 ^ W) :
    TblDo A W 1 ldwPart2 s (fun s' => ldwCore s' es.sum ℓ K es.length E ∧
      s'.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (layPre es ℓ K).length)
        es.sum ∧
      s'.acc = (ldwRecs A 1 es.sum (layPre es ℓ K) (layPre es ℓ K).length).reverse ++ acc0)
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
      t.acc = (ldwRecs A 1 es.sum (layPre es ℓ K) (L + h' * D)).reverse ++ acc0)
    ⟨hc.fr (M := [vh]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]) (by decide), ?_, ?_, ?_⟩ ?_ ?_
  · simp only; rw [Function.update_of_ne (by decide), hV]; simp
  · simp only; rw [Function.update_of_ne (by decide), hjv]; simp
  · show s.acc = _
    rw [hacc]; simp
  · intro h' hh t ⟨ct, hVt, hjt, hacct⟩ hth _
    refine TblDo.mono (K := 8 + (1 + (1 + (D * (ldwP2Atoms es.sum D + 1 + 2) + 2)))) ?_
      (fun _ h => h) (by unfold ldwP2OAtoms; omega)
    have he := ldwEs_do (A := A) (W := W) (w := 1) vZero (by decide) t (by rw [ct.zero]; omega)
      ct.two (by rw [ct.lm1]; omega)
    rw [ct.zero, ct.lm1, ct.cE] at he
    refine he.seq fun t1 ⟨hes1, _, hfr1, hacc1⟩ => ?_
    have c1 := ct.fr hfr1 (by decide)
    refine (TblDo.ins (.sub vN ves voff)
      (P := fun t2 => t2 = TblIns.run A W 1 (.sub vN ves voff) t1) rfl).seq fun t2 ht2 => ?_
    subst ht2
    set t2 := TblIns.run A W 1 (.sub vN ves voff) t1 with ht2
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
        u.acc = (ldwRecs A 1 es.sum (layPre es ℓ K) (L + h' * D + i)).reverse ++ acc0)
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
      refine (ldwP2body_do (A := A) (W := W) (w := 1) H hE hh hi u acc0 cu hVu hju (hoffu hi) hui
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
  · intro t ⟨ct, hVt, _, hacct⟩ _ _
    refine ⟨ct, ?_, ?_⟩
    · rw [hVt, layPre_length]
    · rw [hacct, layPre_length]

theorem dsyRecs_length (N : ℕ) (pre : List ℕ) (j : ℕ) :
    (ldwRecs A 1 N pre j).length = j := by
  rw [ldwRecs, tw_length_flatMap_const _ _ 1 (fun m _ => by simp [ldwRec]), List.length_range,
    Nat.mul_one]

/-- The invariant between the phases: the constants and the positions after the prefix
moves on `vV`. -/
structure DsyInv (s : TblSt 40 A) (es : List ℕ) (ℓ K E : ℕ) : Prop where
  core : ldwCore s es.sum ℓ K es.length E
  pos : s.val vV = ldwPack (es.sum + 1) (layPos es.sum (layPre es ℓ K) (layPre es ℓ K).length)
    es.sum

theorem DsyInv.fr {s s' : TblSt 40 A} {es : List ℕ} {ℓ K E : ℕ} (h : DsyInv s es ℓ K E)
    {M : List (Fin 40)} (hfr : ldwFr s s' M)
    (hM : ∀ x ∈ M, x ∉ [vN, vL, vK, vD, vE, vR, vOne, vZero, vTwo, vLm1, vb, vV]) :
    DsyInv s' es ℓ K E where
  core := h.core.fr hfr fun x hx => by
    have := hM x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1,
      this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1,
      this.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.1⟩
  pos := by
    rw [hfr vV fun hm => ?_]
    · exact h.pos
    · have := hM vV hm
      simp at this

theorem DsyInv.reacc {s : TblSt 40 A} {es : List ℕ} {ℓ K E : ℕ} (h : DsyInv s es ℓ K E)
    (acc : List (Fin (A + 4))) : DsyInv ⟨s.val, acc⟩ es ℓ K E :=
  ⟨⟨h.core.cN, h.core.cL, h.core.cK, h.core.cD, h.core.cE, h.core.cR, h.core.one, h.core.zero,
    h.core.two, h.core.lm1, h.core.cb⟩, h.pos⟩

/-- **The prefix moves.** `ldw1Code` from the inputs leaves the constants and the packed
positions after all prefix moves (its emissions are discarded by the host). -/
theorem dsyLay_do {es : List ℕ} {ℓ K E : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (st : TblSt 40 A)
    (hN : st.val vN = es.sum) (hL : st.val vL = ℓ) (hK : st.val vK = K)
    (hD : st.val vD = es.length) (hEv : st.val vE = E) (hW : (es.sum + 1) ^ es.sum < 2 ^ W)
    (hNW : es.sum < W) (h2W : 2 ≤ W) (hℓW : ℓ < 2 ^ W) :
    TblDo A W 1 ldw1Code st
      (fun s => DsyInv s es ℓ K E ∧ s.acc.length = (layPre es ℓ K).length + st.acc.length)
      (ldw1Atoms es.sum es.length (layB ℓ K)) := by
  have hℓ := H.ℓ_ge
  have hW2 : ∀ x ≤ es.sum + 1, x < 2 ^ W := fun x hx =>
    lt_of_le_of_lt hx (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hNW))
  have h4 : 4 ≤ 2 ^ W := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h2W
  set l : List (TblIns 40) := [.zero vZero, .zero vOne, .inc vOne, .zero vTwo, .inc vTwo, .inc vTwo,
    .sub vL vOne vLm1, .mod vLm1 vK vb, .add vN vOne vR, .zero vV] with hl
  have hblk : TblDo A W 1 (tblBlock 40 l (.zero vj)) st
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
    have hm := ldwMap_do (A := A) (W := W) (w := 1) (V := vV) (V2 := vV2) (Rc := vRc) (R := vR)
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
  · refine (ldwPart1_do (A := A) (W := W) (w := 1) H hE s cs hVs hjs hW hNW hℓW).seq
      fun s1 ⟨c1, hV1, hj1, hacc1⟩ => ?_
    refine (dsyPart2_do (A := A) (W := W) H hE s1 st.acc c1 hV1 hj1
      (by rw [hacc1, haccs]) hW hNW hℓW).mono (fun s2 ⟨c2, hV2, hacc2⟩ => ⟨⟨c2, hV2⟩, ?_⟩) le_rfl
    rw [hacc2, List.length_append, List.length_reverse, dsyRecs_length]

/-! ### The unary wires -/

/-- `(ℓ - 1) mod K` ticks. -/
def dsyCodeB : TblCode 40 := dsyTicks vi vb

/-- `N - D (ℓ - 1)` ticks: the number of long axes. -/
def dsyCodeLg : TblCode 40 :=
  .ins (.mul vD vLm1 vtmp) ;; .ins (.sub vN vtmp vLg) ;; dsyTicks vi vLg

/-- `ℓ` ticks. -/
def dsyCodeL : TblCode 40 := dsyTicks vi vL

/-- `ℓ` ticks if some axis is long, `ℓ - 1` ticks otherwise: the number of rounds. -/
def dsyCodeNr : TblCode 40 :=
  .ins (.mul vD vLm1 vtmp) ;; .ins (.sub vN vtmp vLg) ;;
    .ite vZero vLg (.ins (.copy vL vNr)) (.ins (.copy vLm1 vNr)) ;; dsyTicks vi vNr

/-- The number of rounds: `ℓ` if some axis is long (`N > D (ℓ - 1)`), `ℓ - 1` otherwise. -/
def dsyNr (N D ℓ : ℕ) : ℕ := if 0 < N - D * (ℓ - 1) then ℓ else ℓ - 1

theorem dsyNr_eq (N D ℓ : ℕ) : dsyNr N D ℓ = if 0 < N - D * (ℓ - 1) then ℓ else ℓ - 1 := rfl

variable {es : List ℕ} {ℓ K E : ℕ}

theorem dsyCodeB_do (s : TblSt 40 A) (hc : DsyInv s es ℓ K E) (hℓW : ℓ < 2 ^ W) (hℓ : 1 ≤ ℓ) :
    TblDo A W 1 dsyCodeB s
      (fun s' => DsyInv s' es ℓ K E ∧ s'.acc = List.replicate (layB ℓ K) (dsyT A) ++ s.acc)
      (dsyLoopAtoms (layB ℓ K)) := by
  have hb : s.val vb = layB ℓ K := hc.core.cb
  have h := dsyTicks_do (W := W) (i := vi) (c := vb) (by decide) (by decide) (by decide) s
    hc.core.one hc.core.zero (by rw [hb]; unfold layB; have := Nat.mod_le (ℓ - 1) K; omega)
  rw [hb] at h
  exact h.mono (fun s' ⟨hacc, hfr, _⟩ => ⟨hc.fr hfr (by decide), hacc⟩) le_rfl

/-- The atoms of `dsyCodeLg`. -/
def dsyLgAtoms (N : ℕ) : ℕ := 1 + (1 + dsyLoopAtoms N)

theorem dsyCodeLg_do (s : TblSt 40 A) (hc : DsyInv s es ℓ K E) (hNW : es.sum < 2 ^ W)
    (hDL : es.length * (ℓ - 1) ≤ es.sum) :
    TblDo A W 1 dsyCodeLg s
      (fun s' => DsyInv s' es ℓ K E ∧
        s'.acc = List.replicate (es.sum - es.length * (ℓ - 1)) (dsyT A) ++ s.acc)
      (dsyLgAtoms es.sum) := by
  have c := hc.core
  refine (TblDo.insX (.mul vD vLm1 vtmp)
    (P := fun s1 => s1 = ⟨Function.update s.val vtmp (es.length * (ℓ - 1)), s.acc⟩)
    (by simp only [TblIns.fits, c.cD, c.lm1]; omega)
    (by simp [TblIns.exact, c.cD, c.lm1])).seq fun s1 hs1 => ?_
  subst hs1
  refine (TblDo.insX (.sub vN vtmp vLg)
    (P := fun s2 => s2 = ⟨Function.update (Function.update s.val vtmp (es.length * (ℓ - 1))) vLg
      (es.sum - es.length * (ℓ - 1)), s.acc⟩)
    (by simp only [TblIns.fits, Function.update_apply]; simp [c.cN]; omega)
    (by simp [TblIns.exact, c.cN])).seq fun s2 hs2 => ?_
  subst hs2
  have h := dsyTicks_do (W := W) (i := vi) (c := vLg) (by decide) (by decide) (by decide)
    ⟨Function.update (Function.update s.val vtmp (es.length * (ℓ - 1))) vLg
      (es.sum - es.length * (ℓ - 1)), s.acc⟩ (by simp [c.one]) (by simp [c.zero])
    (by simp; omega)
  simp only [Function.update_self] at h
  refine (h.mono (fun s' ⟨hacc, hfr, _⟩ => ⟨?_, hacc⟩) (by unfold dsyLoopAtoms; omega))
  refine hc.fr (M := [vtmp, vLg, vi]) (fun x hx => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  rw [hfr x (by simp [hx.2.2])]
  simp [Function.update_of_ne hx.1, Function.update_of_ne hx.2.1]

theorem dsyCodeL_do (s : TblSt 40 A) (hc : DsyInv s es ℓ K E) (hℓW : ℓ < 2 ^ W) :
    TblDo A W 1 dsyCodeL s
      (fun s' => DsyInv s' es ℓ K E ∧ s'.acc = List.replicate ℓ (dsyT A) ++ s.acc)
      (dsyLoopAtoms ℓ) := by
  have hL : s.val vL = ℓ := hc.core.cL
  have h := dsyTicks_do (W := W) (i := vi) (c := vL) (by decide) (by decide) (by decide) s
    hc.core.one hc.core.zero (by rw [hL]; exact hℓW)
  rw [hL] at h
  exact h.mono (fun s' ⟨hacc, hfr, _⟩ => ⟨hc.fr hfr (by decide), hacc⟩) le_rfl

/-- The atoms of `dsyCodeNr`. -/
def dsyNrAtoms (ℓ : ℕ) : ℕ := 1 + (1 + ((1 + 1) + dsyLoopAtoms ℓ))

theorem dsyCodeNr_do (s : TblSt 40 A) (hc : DsyInv s es ℓ K E) (hNW : es.sum < 2 ^ W)
    (hℓW : ℓ < 2 ^ W) (hDL : es.length * (ℓ - 1) ≤ es.sum) :
    TblDo A W 1 dsyCodeNr s
      (fun s' => DsyInv s' es ℓ K E ∧
        s'.acc = List.replicate (dsyNr es.sum es.length ℓ) (dsyT A) ++ s.acc)
      (dsyNrAtoms ℓ) := by
  have c := hc.core
  refine (TblDo.insX (.mul vD vLm1 vtmp)
    (P := fun s1 => s1 = ⟨Function.update s.val vtmp (es.length * (ℓ - 1)), s.acc⟩)
    (by simp only [TblIns.fits, c.cD, c.lm1]; omega)
    (by simp [TblIns.exact, c.cD, c.lm1])).seq fun s1 hs1 => ?_
  subst hs1
  set σ₂ : Fin 40 → ℕ := Function.update (Function.update s.val vtmp (es.length * (ℓ - 1))) vLg
    (es.sum - es.length * (ℓ - 1)) with hσ₂
  refine (TblDo.insX (.sub vN vtmp vLg) (P := fun s2 => s2 = ⟨σ₂, s.acc⟩)
    (by simp only [TblIns.fits, Function.update_apply]; simp [c.cN]; omega)
    (by simp [TblIns.exact, c.cN, hσ₂])).seq fun s2 hs2 => ?_
  subst hs2
  have hσ₂Lg : σ₂ vLg = es.sum - es.length * (ℓ - 1) := by simp [hσ₂]
  have hσ₂0 : σ₂ vZero = 0 := by simp [hσ₂, c.zero]
  have hσ₂L : σ₂ vL = ℓ := by simp [hσ₂, c.cL]
  have hσ₂L1 : σ₂ vLm1 = ℓ - 1 := by simp [hσ₂, c.lm1]
  set σ₃ : Fin 40 → ℕ := Function.update σ₂ vNr (dsyNr es.sum es.length ℓ) with hσ₃
  have hite : TblDo A W 1 (.ite vZero vLg (.ins (.copy vL vNr)) (.ins (.copy vLm1 vNr)))
      ⟨σ₂, s.acc⟩ (fun s3 => s3 = ⟨σ₃, s.acc⟩) (1 + 1) := by
    by_cases hlt : 0 < es.sum - es.length * (ℓ - 1)
    · refine TblDo.iteT (by simp only [hσ₂0, hσ₂Lg]; exact hlt) (TblDo.ins _ ?_)
      simp [TblIns.run, hσ₃, dsyNr, hlt, hσ₂L]
    · refine TblDo.iteF (by simp only [hσ₂0, hσ₂Lg]; exact hlt) (TblDo.ins _ ?_)
      simp [TblIns.run, hσ₃, dsyNr, hlt, hσ₂L1]
  refine hite.seq fun s3 hs3 => ?_
  subst hs3
  have hnr : dsyNr es.sum es.length ℓ < 2 ^ W := by
    unfold dsyNr; split_ifs <;> omega
  have h := dsyTicks_do (W := W) (i := vi) (c := vNr) (by decide) (by decide) (by decide)
    ⟨σ₃, s.acc⟩ (by simp [hσ₃, hσ₂, c.one]) (by simp [hσ₃, hσ₂, c.zero]) (by simp [hσ₃]; exact hnr)
  simp only [hσ₃, Function.update_self] at h
  refine (h.mono (fun s' ⟨hacc, hfr, _⟩ => ⟨?_, hacc⟩)
    (by unfold dsyLoopAtoms dsyNr; split_ifs <;> omega))
  refine hc.fr (M := [vtmp, vLg, vNr, vi]) (fun x hx => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  rw [hfr x (by simp [hx.2.2.2])]
  simp [hσ₂, Function.update_of_ne hx.1, Function.update_of_ne hx.2.1,
    Function.update_of_ne hx.2.2.1]

/-! ### The axis record -/

/-- The record of the axis widths: `ax es i` ticks and a separator per axis. -/
def dsyCodeRec : TblCode 40 :=
  tblFor vi vD (ldwEsCode vi ;; dsyTicks vk ves ;; .ins (.emit vZero vZero))

/-- The pair-symbol field of an axis. -/
def dsyField (A : ℕ) (a : ℕ) : List (Fin (A + 4)) := List.replicate a (dsyT A) ++ [dsyF A]

theorem dsy_flatMap_congr {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem dsy_map_range_ax (es : List ℕ) : (List.range es.length).map (ax es) = es := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem _ _ h2

/-- `topRec es` as pair symbols. -/
theorem dsyTopRec_map (es : List ℕ) :
    (topRec es : List (Fin (A + 4))).map (dsyEnc A) =
      (List.range es.length).flatMap fun i => dsyField A (ax es i) := by
  conv_lhs => rw [← dsy_map_range_ax es]
  rw [topRec, List.flatMap_map, List.map_flatMap]
  refine dsy_flatMap_congr _ _ _ fun i _ => ?_
  simp [dsyField, dsyEnc_topSep]

/-- The atoms of one iteration of `dsyCodeRec`. -/
def dsyRecBodyAtoms (D ℓ : ℕ) : ℕ := (4 * D + 8) + (dsyLoopAtoms ℓ + 1)

/-- The atoms of `dsyCodeRec`. -/
def dsyRecAtoms (D ℓ : ℕ) : ℕ := 1 + (D * (dsyRecBodyAtoms D ℓ + 1 + 2) + 2)

theorem dsyCodeRec_do (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (s : TblSt 40 A)
    (hc : DsyInv s es ℓ K E) (hNW : es.sum < W) (hℓW : ℓ < 2 ^ W) :
    TblDo A W 1 dsyCodeRec s
      (fun s' => DsyInv s' es ℓ K E ∧ s'.acc = ((topRec es).map (dsyEnc A)).reverse ++ s.acc)
      (dsyRecAtoms es.length ℓ) := by
  have c := hc.core
  have hDN : es.length ≤ es.sum := ldw_length_le_sum H
  have hℓ := H.ℓ_ge
  have hWp : es.sum < 2 ^ W := lt_trans hNW Nat.lt_two_pow_self
  set D := es.length with hD
  refine TblDo.for D (dsyRecBodyAtoms D ℓ) c.cD (by omega) (by decide)
    (fun j t => DsyInv t es ℓ K E ∧
      t.acc = ((List.range j).flatMap fun i => dsyField A (ax es i)).reverse ++ s.acc)
    ⟨hc.fr (M := [vi]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]) (by decide), by simp⟩ ?_ ?_
  · intro j hj t ⟨ct, hacct⟩ hti _
    have ct' := ct.core
    have he := ldwEs_do (A := A) (W := W) (w := 1) vi (by decide) t (by rw [hti]; omega)
      ct'.two (by rw [ct'.lm1]; omega)
    rw [hti, ct'.lm1, ct'.cE, ← hE j hj] at he
    refine TblDo.mono (K := (4 * j + 8) + (dsyLoopAtoms (ax es j) + 1)) ?_ (fun _ h => h) ?_
    · refine he.seq fun t1 ⟨hes1, _, hfr1, hacc1⟩ => ?_
      have c1 := ct.fr hfr1 (by decide)
      have hax : ax es j < 2 ^ W := by
        rcases H.ax_of_lt hj with h | h <;> omega
      have ht := dsyTicks_do (W := W) (i := vk) (c := ves) (by decide) (by decide) (by decide) t1
        c1.core.one c1.core.zero (by rw [hes1]; exact hax)
      rw [hes1] at ht
      refine ht.seq fun t2 ⟨hacc2, hfr2, _⟩ => ?_
      have c2 := c1.fr hfr2 (by decide)
      refine (dsyEmit_do vZero vZero t2).mono (fun t3 ht3 => ?_) le_rfl
      subst ht3
      have hi2 : t2.val vi = j := by
        rw [hfr2 _ (by decide), hfr1 _ (by decide), hti]
      have hD2 : t2.val vD = D := c2.core.cD
      refine ⟨hi2, hD2, ?_, ?_⟩
      · refine c2.fr (M := [vi]) (fun x hx => ?_) (by decide)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp [Function.update_of_ne hx]
      · show pairSym A ((t2.val vZero).testBit 0) ((t2.val vZero).testBit 0) :: t2.acc = _
        rw [c2.core.zero, hacc2, hacc1, hacct, List.range_succ, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append]
        simp [dsyField, dsyF]
    · have : ax es j ≤ ℓ := by rcases H.ax_of_lt hj with h | h <;> omega
      unfold dsyRecBodyAtoms dsyLoopAtoms
      nlinarith
  · intro t ⟨ct, hacct⟩ _ _
    refine ⟨ct, ?_⟩
    rw [hacct, dsyTopRec_map]

/-! ### The position table -/

/-- The chunk map `vp := layChunkFun K (layTr D q) vp`. -/
def dsyChunkBlk : TblCode 40 :=
  tblBlock 40 [.div vp vK vc, .mod vp vK vt, .mod vc vq vt1, .mul vt1 vD vt1, .div vc vq vt2,
    .add vt1 vt2 vt1, .mul vt1 vK vt1] (.add vt1 vt vp)

/-- The chunk map on positions below `K m`; the identity above. -/
def dsyChunk : TblCode 40 := .ite vp vKm dsyChunkBlk (.ins (.zero vtmp))

/-- One position `k = N - 1 - i`: read it, apply the chunk map, emit its block. -/
def dsyPosBody : TblCode 40 :=
  .ins (.sub vN vOne vk) ;; .ins (.sub vk vi vk) ;; ldwPowR vRc vR vk vk2 ;;
    ldwField vV vRc vR vt vp ;; dsyChunk ;; dsyTicks vh vp ;; .ins (.sub vN vp vtmp) ;;
    dsyZeros vh vtmp

/-- **The position table**: `q`, `m = D q`, `K m`, then the blocks of the positions
`N - 1, …, 0`. -/
def dsyCodePos : TblCode 40 :=
  .ins (.div vLm1 vK vq) ;; .ins (.mul vD vq vm) ;; .ins (.mul vK vm vKm) ;;
    tblFor vi vN dsyPosBody

/-- The physical position of logical bit `k` under the layout: the prefix moves, then the
chunk transposition (`layRun_moves`). -/
def dsyPos (es : List ℕ) (ℓ K : ℕ) (k : ℕ) : ℕ :=
  layChunkFun K (layTr es.length (layQ ℓ K))
    (layPos es.sum (layPre es ℓ K) (layPre es ℓ K).length k)

theorem dsyPos_eq (H : LayHyp es ℓ K) {k : ℕ} (hk : k < es.sum) :
    dsyPos es ℓ K k = twPosL (layPerm es ℓ K) k := by
  simp only [twPosL, hk, ↓reduceDIte]
  rw [layPerm_apply H, layRun_moves]
  rfl

/-- The block of a position as pair symbols. -/
def dsyBlock (A N : ℕ) (P : ℕ → ℕ) (k : ℕ) : List (Fin (A + 4)) :=
  List.replicate (P k) (dsyT A) ++ List.replicate (N - P k) (dsyF A)

/-- `twPosReg` as pair symbols. -/
theorem dsyPosReg_map (N : ℕ) (P : ℕ → ℕ) :
    (twPosReg A N P).map (dsyEnc A) = (List.range N).reverse.flatMap (dsyBlock A N P) := by
  rw [twPosReg, List.map_flatMap]
  refine dsy_flatMap_congr _ _ _ fun k _ => ?_
  simp [twBlock, dsyBlock]

theorem dsyPosReg_congr (N : ℕ) (P P' : ℕ → ℕ) (h : ∀ k < N, P k = P' k) :
    twPosReg A N P = twPosReg A N P' := by
  unfold twPosReg
  refine dsy_flatMap_congr _ _ _ fun k hk => ?_
  rw [h k (by simpa using hk)]

theorem dsyChunk_do {K D q N : ℕ} (s : TblSt 40 A) (hK : s.val vK = K) (hD : s.val vD = D)
    (hq : s.val vq = q) (hKm : s.val vKm = K * (D * q))
    (hmN : K * (D * q) ≤ N) (hNW : N < 2 ^ W) :
    TblDo A W 1 dsyChunk s (fun s' => s'.val vp = layChunkFun K (layTr D q) (s.val vp) ∧
      ldwFr s s' [vp, vc, vt, vt1, vt2, vtmp] ∧ s'.acc = s.acc) 9 := by
  obtain ⟨y, hydef⟩ : ∃ y, s.val vp = y := ⟨_, rfl⟩
  rw [hydef]
  by_cases h : y < K * (D * q)
  · refine TblDo.iteT (by rw [hKm, hydef]; exact h) ?_
    have hK0 : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · rw [h0, Nat.zero_mul] at h; omega
      · exact h0
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, Nat.mul_zero, Nat.mul_zero] at h; omega
      · exact h0
    have hc : y / K < D * q := Nat.div_lt_of_lt_mul h
    have hcq : y / K / q < D := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
    have hcm : y / K % q < q := Nat.mod_lt _ hq0
    have hc' : y / K % q * D + y / K / q < D * q := by
      have h1 : (y / K % q + 1) * D ≤ q * D := Nat.mul_le_mul_right D hcm
      rw [Nat.add_mul] at h1
      rw [Nat.mul_comm D q]; omega
    have hres : (y / K % q * D + y / K / q) * K + y % K < K * (D * q) :=
      lay_chunk_lt K hc' (Nat.mod_lt _ hK0)
    have hle : D * q ≤ K * (D * q) := Nat.le_mul_of_pos_left _ hK0
    have hle2 : (y / K % q * D + y / K / q) * K ≤ (y / K % q * D + y / K / q) * K + y % K :=
      Nat.le_add_right _ _
    have e : layChunkFun K (layTr D q) y = (y / K % q * D + y / K / q) * K + y % K := by
      simp only [layChunkFun, h, ↓reduceDIte]
      rfl
    unfold dsyChunkBlk
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hK, hD, hq, hydef]
      have hg : K * (D * q) < 2 ^ W := lt_of_le_of_lt hmN hNW
      refine ⟨lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hc'.le) (lt_of_le_of_lt hle hg),
        lt_of_lt_of_le hc' (hle.trans hg.le), lt_of_le_of_lt hle2 (lt_trans hres hg),
        lt_trans hres hg⟩
    · simp only [List.cons_append, List.nil_append, tblExactList, TblIns.exact]
      refine ⟨?_, fun x hx => ?_, by simp⟩
      · simp [hK, hD, hq, hydef, e]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        dsimp only
        simp only [Function.update_apply, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1,
          ite_false]
  · refine TblDo.mono (K := 1 + 1) ?_ (fun _ h => h) (by norm_num)
    refine TblDo.iteF (by rw [hKm, hydef]; exact h) (TblDo.ins _ ⟨?_, fun x hx => ?_, rfl⟩)
    · show Function.update s.val vtmp 0 vp = _
      rw [Function.update_of_ne (by decide), hydef, layChunkFun_of_ge K _ (by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      show Function.update s.val vtmp 0 x = s.val x
      exact Function.update_of_ne hx.2.2.2.2.2 _ _

/-- The atoms of one iteration of `dsyCodePos`. -/
def dsyPosBodyAtoms (N : ℕ) : ℕ := 8 * N + 25

/-- The variables changed by `dsyPosBody`. -/
def dsyPosMods : List (Fin 40) := [vk, vRc, vk2, vt, vp, vc, vt1, vt2, vtmp, vh]

theorem dsyPosBody_do (H : LayHyp es ℓ K) (s : TblSt 40 A) (hc : DsyInv s es ℓ K E)
    (hq : s.val vq = layQ ℓ K) (_hm : s.val vm = es.length * layQ ℓ K)
    (hKm : s.val vKm = K * (es.length * layQ ℓ K)) {j : ℕ} (hj : j < es.sum)
    (hvi : s.val vi = j) (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) :
    TblDo A W 1 dsyPosBody s (fun s' => DsyInv s' es ℓ K E ∧ ldwFr s s' dsyPosMods ∧
      s'.acc = (dsyBlock A es.sum (dsyPos es ℓ K) (es.sum - 1 - j)).reverse ++ s.acc)
      (dsyPosBodyAtoms es.sum) := by
  have c := hc.core
  obtain ⟨k, hk⟩ : ∃ k, k = es.sum - 1 - j := ⟨_, rfl⟩
  rw [← hk]
  have hkN : k < es.sum := by omega
  obtain ⟨sp1, -, -, -⟩ := layPos_spec (layPre_nodup H) (layPre_lt H) (layPre_length_le H)
    (layPre es ℓ K).length le_rfl
  have hmN : K * (es.length * layQ ℓ K) ≤ es.sum := by have := lay_chunk_size H; omega
  have hNW2 : es.sum < 2 ^ W := lt_trans hNW Nat.lt_two_pow_self
  have hRk : (es.sum + 1) ^ k < 2 ^ W :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hkN.le) hW
  have hpos : layPos es.sum (layPre es ℓ K) (layPre es ℓ K).length k < es.sum := sp1 k hkN
  have hP : dsyPos es ℓ K k < es.sum := by
    unfold dsyPos
    by_cases hlt : layPos es.sum (layPre es ℓ K) (layPre es ℓ K).length k <
      K * (es.length * layQ ℓ K)
    · exact lt_of_lt_of_le (layChunkFun_lt K _ hlt) hmN
    · rw [layChunkFun_of_ge K _ (by omega)]; exact hpos
  refine TblDo.mono (K := 1 + (1 + ((4 * k + 5) + (2 + (9 + (dsyLoopAtoms (dsyPos es ℓ K k) +
    (1 + dsyLoopAtoms (es.sum - dsyPos es ℓ K k)))))))) ?_ (fun _ h => h) ?_
  · -- k := N - 1 - j
    refine (TblDo.insX (.sub vN vOne vk)
      (P := fun s1 => s1 = ⟨Function.update s.val vk (es.sum - 1), s.acc⟩)
      (by simp only [TblIns.fits, c.cN, c.one]; omega)
      (by simp [TblIns.exact, c.cN, c.one])).seq fun s1 hs1 => ?_
    subst hs1
    refine (TblDo.insX (.sub vk vi vk)
      (P := fun s2 => s2 = ⟨Function.update s.val vk k, s.acc⟩)
      (by simp only [TblIns.fits, Function.update_apply]; simp [hvi]; omega)
      (by simp [TblIns.exact, hvi, hk])).seq fun s2 hs2 => ?_
    subst hs2
    have fr2 : ldwFr s ⟨Function.update s.val vk k, s.acc⟩ [vk] := fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]
    have c2 := hc.fr fr2 (by decide)
    have hk2 : (⟨Function.update s.val vk k, s.acc⟩ : TblSt 40 A).val vk = k := by simp
    -- Rc := R ^ k
    have hp := ldwPowR_do (A := A) (W := W) (w := 1) (Rc := vRc) (R := vR) (e := vk) (k := vk2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      ⟨Function.update s.val vk k, s.acc⟩ (by rw [c2.core.cR]; omega)
      (by rw [c2.core.cR, hk2]; exact hRk) (by rw [hk2]; omega)
    rw [hk2, c2.core.cR] at hp
    refine hp.seq fun s3 ⟨hRc3, _, hfr3, hacc3⟩ => ?_
    have c3 := c2.fr hfr3 (by decide)
    -- p := V / Rc % R
    refine (ldwField_do (A := A) (W := W) (w := 1) (V := vV) (Rc := vRc) (R := vR) (t := vt)
      (y := vp) (by decide) s3).seq fun s4 ⟨hp4, hfr4, hacc4⟩ => ?_
    have c4 := c3.fr hfr4 (by decide)
    have hp4' : s4.val vp = layPos es.sum (layPre es ℓ K) (layPre es ℓ K).length k := by
      rw [hp4, hRc3, c3.pos, c3.core.cR]
      exact ldwPack_field (by omega) (fun c hc' => by have := sp1 c hc'; omega) _ hkN
    -- the chunk map
    refine (dsyChunk_do (W := W) (N := es.sum) s4 c4.core.cK c4.core.cD
      (by rw [hfr4 _ (by decide), hfr3 _ (by decide), fr2 _ (by decide), hq])
      (by rw [hfr4 _ (by decide), hfr3 _ (by decide), fr2 _ (by decide), hKm])
      hmN hNW2).seq fun s5 ⟨hp5, hfr5, hacc5⟩ => ?_
    have c5 := c4.fr hfr5 (by decide)
    have hp5' : s5.val vp = dsyPos es ℓ K k := by rw [hp5, hp4']; rfl
    -- the ticks
    have ht := dsyTicks_do (W := W) (i := vh) (c := vp) (by decide) (by decide) (by decide) s5
      c5.core.one c5.core.zero (by rw [hp5']; exact lt_trans hP hNW2)
    rw [hp5'] at ht
    refine ht.seq fun s6 ⟨hacc6, hfr6, _⟩ => ?_
    have c6 := c5.fr hfr6 (by decide)
    have hp6 : s6.val vp = dsyPos es ℓ K k := by rw [hfr6 _ (by decide), hp5']
    -- tmp := N - p
    refine (TblDo.insX (.sub vN vp vtmp)
      (P := fun s7 => s7 = ⟨Function.update s6.val vtmp (es.sum - dsyPos es ℓ K k), s6.acc⟩)
      (by simp only [TblIns.fits, c6.core.cN, hp6]; omega)
      (by simp [TblIns.exact, c6.core.cN, hp6])).seq fun s7 hs7 => ?_
    subst hs7
    have fr7 : ldwFr s6 ⟨Function.update s6.val vtmp (es.sum - dsyPos es ℓ K k), s6.acc⟩
        [vtmp] := fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]
    have c7 := c6.fr fr7 (by decide)
    have hz := dsyZeros_do (W := W) (i := vh) (c := vtmp) (by decide) (by decide)
      ⟨Function.update s6.val vtmp (es.sum - dsyPos es ℓ K k), s6.acc⟩
      c7.core.zero (by simp; omega)
    simp only [Function.update_self] at hz
    refine hz.mono (fun s8 ⟨hacc8, hfr8, _⟩ => ⟨c7.fr hfr8 (by decide), ?_, ?_⟩) le_rfl
    · intro x hx
      simp only [dsyPosMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [hfr8 x (by simp [hx.2.2.2.2.2.2.2.2.2]), fr7 x (by simp [hx.2.2.2.2.2.2.2.2.1]),
        hfr6 x (by simp [hx.2.2.2.2.2.2.2.2.2]),
        hfr5 x (by simp [hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.1, hx.2.2.2.2.2.2.1,
          hx.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.1]),
        hfr4 x (by simp [hx.2.2.2.1, hx.2.2.2.2.1]), hfr3 x (by simp [hx.2.1, hx.2.2.1]),
        fr2 x (by simp [hx.1])]
    · rw [hacc8]
      show _ = _ ++ s.acc
      rw [hacc6, hacc5, hacc4, hacc3, dsyBlock,
        List.reverse_append, List.reverse_replicate, List.reverse_replicate, List.append_assoc]
  · unfold dsyPosBodyAtoms dsyLoopAtoms
    have : dsyPos es ℓ K k ≤ es.sum := hP.le
    omega

/-- The atoms of `dsyCodePos`. -/
def dsyPosAtoms (N : ℕ) : ℕ := 1 + (1 + (1 + (1 + (N * (dsyPosBodyAtoms N + 1 + 2) + 2))))

theorem dsyCodePos_do (H : LayHyp es ℓ K) (s : TblSt 40 A) (hc : DsyInv s es ℓ K E)
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) :
    TblDo A W 1 dsyCodePos s
      (fun s' => DsyInv s' es ℓ K E ∧
        s'.acc = ((twPosReg A es.sum (dsyPos es ℓ K)).map (dsyEnc A)).reverse ++ s.acc)
      (dsyPosAtoms es.sum) := by
  have c := hc.core
  have hK1 := H.K_pos
  have hmN : K * (es.length * layQ ℓ K) ≤ es.sum := by have := lay_chunk_size H; omega
  have hmN' : es.length * layQ ℓ K ≤ es.sum := le_trans (Nat.le_mul_of_pos_left _ hK1) hmN
  have hNW2 : es.sum < 2 ^ W := lt_trans hNW Nat.lt_two_pow_self
  refine (TblDo.insX (.div vLm1 vK vq)
    (P := fun s1 => s1 = ⟨Function.update s.val vq (layQ ℓ K), s.acc⟩)
    trivial (by simp [TblIns.exact, c.lm1, c.cK, layQ])).seq fun s1 hs1 => ?_
  subst hs1
  refine (TblDo.insX (.mul vD vq vm)
    (P := fun s2 => s2 = ⟨Function.update (Function.update s.val vq (layQ ℓ K)) vm
      (es.length * layQ ℓ K), s.acc⟩)
    (by simp only [TblIns.fits, Function.update_apply]; simp [c.cD]; omega)
    (by simp [TblIns.exact, c.cD])).seq fun s2 hs2 => ?_
  subst hs2
  refine (TblDo.insX (.mul vK vm vKm)
    (P := fun s3 => s3 = ⟨Function.update (Function.update (Function.update s.val vq (layQ ℓ K))
      vm (es.length * layQ ℓ K)) vKm (K * (es.length * layQ ℓ K)), s.acc⟩)
    (by simp only [TblIns.fits, Function.update_apply]; simp [c.cK]; omega)
    (by simp [TblIns.exact, c.cK])).seq fun s3 hs3 => ?_
  subst hs3
  have fr3 : ldwFr s ⟨Function.update (Function.update (Function.update s.val vq (layQ ℓ K))
      vm (es.length * layQ ℓ K)) vKm (K * (es.length * layQ ℓ K)), s.acc⟩ [vq, vm, vKm] :=
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [Function.update_of_ne hx.1, Function.update_of_ne hx.2.1,
        Function.update_of_ne hx.2.2]
  have c3 := hc.fr fr3 (by decide)
  refine TblDo.for es.sum (dsyPosBodyAtoms es.sum) c3.core.cN hNW2 (by decide)
    (fun j t => DsyInv t es ℓ K E ∧ t.val vq = layQ ℓ K ∧ t.val vm = es.length * layQ ℓ K ∧
      t.val vKm = K * (es.length * layQ ℓ K) ∧
      t.acc = ((List.range' (es.sum - j) j).reverse.flatMap
        (dsyBlock A es.sum (dsyPos es ℓ K))).reverse ++ s.acc)
    ⟨c3.fr (M := [vi]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]) (by decide), by simp, by simp, by simp, by simp⟩ ?_ ?_
  · intro j hj t ⟨ct, hqt, hmt, hKmt, hacct⟩ hti _
    refine (dsyPosBody_do (W := W) H t ct hqt hmt hKmt hj hti hW hNW).mono
      (fun t' ⟨c', hfr', hacc'⟩ => ?_) le_rfl
    have hi' : t'.val vi = j := by rw [hfr' _ (by decide), hti]
    refine ⟨hi', c'.core.cN, ?_, ?_, ?_, ?_, ?_⟩
    · refine c'.fr (M := [vi]) (fun x hx => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp [Function.update_of_ne hx]
    · show Function.update t'.val vi (j + 1) vq = _
      rw [Function.update_of_ne (by decide), hfr' _ (by decide), hqt]
    · show Function.update t'.val vi (j + 1) vm = _
      rw [Function.update_of_ne (by decide), hfr' _ (by decide), hmt]
    · show Function.update t'.val vi (j + 1) vKm = _
      rw [Function.update_of_ne (by decide), hfr' _ (by decide), hKmt]
    · show t'.acc = _
      rw [hacc', hacct, show es.sum - (j + 1) = es.sum - 1 - j by omega, List.range'_succ,
        show es.sum - 1 - j + 1 = es.sum - j by omega, List.reverse_cons, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append,
        List.append_assoc]
  · intro t ⟨ct, _, _, _, hacct⟩ _ _
    refine ⟨ct, ?_⟩
    rw [hacct, dsyPosReg_map, Nat.sub_self, ← List.range_eq_range']

end IntegerMultBounds.MathlibTM2.Fast.TableVM
