module

public import IntegerMultBounds.Schoenhage.FixedMulProgram

/-! The quasi-linear fixed-point multiply with the twelve-tape interface of
`FixedMul`, plus a block of 91 tapes that is blank before and after. The
operands and rulers are copied onto the block, `fmProg` runs there, the result
is copied onto the output tape, and the block is erased (`fastMul_hoare`).
Every head ends where it started. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Spec.SignedRingProduct

/-! ### Machines on chosen tapes of a bank -/

variable {t : ℕ}

/-- A one-tape machine on tape `i`. -/
noncomputable def at1 (i : Fin t) {q : ℕ} (M : Program 1 q 0) : Program t q 0 :=
  Placement.placed M (InjectivePlacement.placement (fun _ : Fin 1 => i) (slot_const_inj i) (one_size i))

theorem at1_hoare (i : Fin t) {q : ℕ} {M : Program 1 q 0} {f g : ℤ → Fin 4} {h h' : ℤ} {b : ℕ}
    (hM : HoareTime M (· = ⟨fun _ => h, fun _ => f⟩) (· = ⟨fun _ => h', fun _ => g⟩) b) (v : Tapes t 0)
    (hh : v.head i = h) (hf : v.tape i = f) :
    HoareTime (at1 i M) (· = v) (· = ⟨Function.update v.head i h', Function.update v.tape i g⟩) b := by
  refine InjectivePlacement.hoare_exact hM _ (slot_const_inj i) (one_size i) v _ ?_ ?_
  · rw [InjectivePlacement.active_bank]
    simp only [hh, hf]
  · refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · by_cases hx : x = i
      · subst hx
        have := InjectivePlacement.replace_head_slot (fun _ : Fin 1 => x) (slot_const_inj x) (one_size x) v
          ⟨fun _ => h', fun _ => g⟩ 0
        simpa using this
      · rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ (fun _ e => hx e.symm)]
        exact (Function.update_of_ne hx _ _).symm
    · by_cases hx : x = i
      · subst hx
        have := InjectivePlacement.replace_tape_slot (fun _ : Fin 1 => x) (slot_const_inj x) (one_size x) v
          ⟨fun _ => h', fun _ => g⟩ 0
        simpa using this
      · rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ (fun _ e => hx e.symm)]
        exact (Function.update_of_ne hx _ _).symm

/-- The slots of a two-tape machine. -/
def pair2 (i j : Fin t) : Fin 2 → Fin t := fun k => if k = 0 then i else j

theorem pair2_inj {i j : Fin t} (h : i ≠ j) : Function.Injective (pair2 i j) := by
  intro x y e
  fin_cases x <;> fin_cases y <;> simp only [pair2] at e <;>
    first | rfl | (exfalso; exact h (by simpa using e)) | (exfalso; exact h (by simpa using e.symm))

theorem two_size {i j : Fin t} (h : i ≠ j) : 2 + (t - 2) = t := by
  have := i.isLt; have := j.isLt
  have : i.val ≠ j.val := fun e => h (Fin.ext e)
  omega

/-- A two-tape machine on tapes `i`, `j`. -/
noncomputable def at2 (i j : Fin t) (h : i ≠ j) {q : ℕ} (M : Program 2 q 0) : Program t q 0 :=
  Placement.placed M (InjectivePlacement.placement (pair2 i j) (pair2_inj h) (two_size h))

theorem at2_hoare {i j : Fin t} (h : i ≠ j) {q : ℕ} {M : Program 2 q 0} {f g f' g' : ℤ → Fin 4}
    {p r p' r' : ℤ} {b : ℕ}
    (hM : HoareTime M (· = ⟨fun k => if k = 0 then p else r, fun k => if k = 0 then f else g⟩)
      (· = ⟨fun k => if k = 0 then p' else r', fun k => if k = 0 then f' else g'⟩) b) (v : Tapes t 0)
    (hpi : v.head i = p) (hfi : v.tape i = f) (hpj : v.head j = r) (hfj : v.tape j = g) :
    HoareTime (at2 i j h M) (· = v) (· = ⟨Function.update (Function.update v.head i p') j r',
      Function.update (Function.update v.tape i f') j g'⟩) b := by
  refine InjectivePlacement.hoare_exact hM _ (pair2_inj h) (two_size h) v _ ?_ ?_
  · rw [InjectivePlacement.active_bank]
    congr 1 <;> funext k <;> fin_cases k <;> simp [pair2, hpi, hfi, hpj, hfj]
  · have s0 : pair2 i j 0 = i := rfl
    have s1 : pair2 i j 1 = j := rfl
    refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · by_cases hx : x = j
      · subst hx
        have := InjectivePlacement.replace_head_slot (pair2 i x) (pair2_inj h) (two_size h) v
          ⟨fun k => if k = 0 then p' else r', fun k => if k = 0 then f' else g'⟩ 1
        rw [s1] at this; simpa using this
      · by_cases hi : x = i
        · subst hi
          have := InjectivePlacement.replace_head_slot (pair2 x j) (pair2_inj h) (two_size h) v
            ⟨fun k => if k = 0 then p' else r', fun k => if k = 0 then f' else g'⟩ 0
          rw [s0] at this; simpa [Function.update_of_ne hx] using this
        · rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ (fun k e => by
            fin_cases k
            · exact hi e.symm
            · exact hx e.symm)]
          simp [Function.update_of_ne hx, Function.update_of_ne hi]
    · by_cases hx : x = j
      · subst hx
        have := InjectivePlacement.replace_tape_slot (pair2 i x) (pair2_inj h) (two_size h) v
          ⟨fun k => if k = 0 then p' else r', fun k => if k = 0 then f' else g'⟩ 1
        rw [s1] at this; simpa using this
      · by_cases hi : x = i
        · subst hi
          have := InjectivePlacement.replace_tape_slot (pair2 x j) (pair2_inj h) (two_size h) v
            ⟨fun k => if k = 0 then p' else r', fun k => if k = 0 then f' else g'⟩ 0
          rw [s0] at this; simpa [Function.update_of_ne hx] using this
        · rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ (fun k e => by
            fin_cases k
            · exact hi e.symm
            · exact hx e.symm)]
          simp [Function.update_of_ne hx, Function.update_of_ne hi]

/-! ### Copying and erasing words -/

/-- Copy the word under `i` onto the blank tape `j`, then return both heads. -/
noncomputable def copyAt (i j : Fin t) (h : i ≠ j) :=
  Machine.seq (at2 i j h (CopyWord.program (a := 0))) <|
  Machine.seq (at1 i (ReturnOrigin.program (a := 0))) (at1 j (ReturnOrigin.program (a := 0)))

theorem copyAt_hoare {i j : Fin t} (h : i ≠ j) (v : Tapes t 0) {f : ℤ → Fin 4} {p r : ℤ}
    {xs : List (Fin 4)} (hx : ∀ x ∈ xs, x ≠ blank) (hpi : v.head i = p) (hfi : v.tape i = putWord f p xs)
    (hl : f (p - 1) = blank) (hr : f (p + xs.length) = blank) (hpj : v.head j = r)
    (hfj : v.tape j = fun _ => blank) :
    HoareTime (copyAt i j h) (· = v) (· = ⟨v.head, Function.update v.tape j (putWord (fun _ => blank) r xs)⟩)
      (3 * xs.length + 6) := by
  have h1 := at2_hoare h (p' := p + xs.length) (r' := r + xs.length) (f' := putWord f p xs)
    (g' := putWord (fun _ => blank) r xs) (CopyWord.copy_hoare f (fun _ => blank) p r xs hx hr) v hpi hfi hpj hfj
  set v1 : Tapes t 0 := ⟨Function.update (Function.update v.head i (p + xs.length)) j (r + xs.length),
    Function.update (Function.update v.tape i (putWord f p xs)) j (putWord (fun _ => blank) r xs)⟩
  have h2 := at1_hoare i (h := p + xs.length) (h' := p) (f := putWord f p xs) (g := putWord f p xs)
    (ReturnOrigin.return_hoare_at f p xs hx hl) v1
    (by simp only [v1, Function.update_of_ne h, Function.update_self]) (by simp only [v1, Function.update_of_ne h, Function.update_self])
  set v2 : Tapes t 0 := ⟨Function.update v1.head i p, Function.update v1.tape i (putWord f p xs)⟩
  have h3 := at1_hoare j (h := r + xs.length) (h' := r) (f := putWord (fun _ => blank) r xs)
    (g := putWord (fun _ => blank) r xs) (ReturnOrigin.return_hoare_at (fun _ => blank) r xs hx rfl) v2
    (by simp only [v2, v1, Function.update_of_ne h.symm, Function.update_self]) (by simp only [v2, v1, Function.update_of_ne h.symm, Function.update_self])
  refine (h1.seq (h2.seq h3)).consequence (fun _ e => e) (fun w e => e.trans ?_) (by omega)
  simp only [v2, v1]
  congr 1
  · funext x
    by_cases hx1 : x = j
    · subst hx1; simp [hpj]
    · by_cases hx2 : x = i
      · subst hx2; simp [Function.update_of_ne hx1, hpi]
      · simp [Function.update_of_ne hx1, Function.update_of_ne hx2]
  · funext x
    by_cases hx1 : x = j
    · subst hx1; simp
    · by_cases hx2 : x = i
      · subst hx2; simp [Function.update_of_ne hx1, hfi]
      · simp [Function.update_of_ne hx1, Function.update_of_ne hx2]

/-- Erase the word under `i`, leaving the head at its origin. -/
noncomputable def eraseAt (i : Fin t) :=
  Machine.seq (at1 i (ScanEnd.program (a := 0))) (at1 i (EraseBack.program (a := 0)))

theorem eraseAt_hoare (i : Fin t) (v : Tapes t 0) {p : ℤ} {xs : List (Fin 4)} (hx : ∀ x ∈ xs, x ≠ blank)
    (hp : v.head i = p) (hf : v.tape i = putWord (fun _ => blank) p xs) :
    HoareTime (eraseAt i) (· = v) (· = ⟨v.head, Function.update v.tape i (fun _ => blank)⟩)
      (2 * xs.length + 3) := by
  have h1 := at1_hoare i (h' := p + xs.length) (g := putWord (fun _ => blank) p xs)
    (ScanEnd.scan_hoare (fun _ => blank) p xs hx rfl) v hp hf
  have h2 := at1_hoare i (h := p + xs.length) (h' := p) (f := putWord (fun _ => blank) p xs) (g := fun _ => blank)
    (EraseBack.erase_hoare (fun _ => blank) p xs hx rfl (fun _ _ => rfl))
    ⟨Function.update v.head i (p + xs.length), Function.update v.tape i (putWord (fun _ => blank) p xs)⟩
    (by simp only [Function.update_self]) (by simp only [Function.update_self])
  refine (h1.seq h2).consequence (fun _ e => e) (fun w e => e.trans ?_) (by omega)
  congr 1
  · funext x; by_cases hx1 : x = i
    · subst hx1; simp [hp]
    · simp [Function.update_of_ne hx1]
  · funext x; by_cases hx1 : x = i
    · subst hx1; simp
    · simp [Function.update_of_ne hx1]

/-! ### A program on the appended block -/

theorem blockSize : 𝕌 + 12 = 12 + 𝕌 := by omega

/-- `M` on the last 91 tapes of a `12 + 91` bank. -/
noncomputable def onBlock {q : ℕ} (M : Program 𝕌 q 0) : Program (12 + 𝕌) q 0 :=
  Placement.placed M (InjectivePlacement.placement (Fin.natAdd 12) (Fin.natAdd_injective 𝕌 12) blockSize)

theorem natAdd_ne_castAdd (b : Fin 𝕌) (j : Fin 12) : Fin.natAdd 12 b ≠ Fin.castAdd 𝕌 j := by
  intro e; have := congrArg Fin.val e; simp at this; omega

theorem onBlock_hoare {q : ℕ} {M : Program 𝕌 q 0} {X X' : Tapes 𝕌 0} {c : ℕ}
    (hM : HoareTime M (· = X) (· = X') c) (L : Tapes 12 0) :
    HoareTime (onBlock M) (· = L.append X) (· = L.append X') c := by
  refine InjectivePlacement.hoare_exact hM (Fin.natAdd 12) (Fin.natAdd_injective 𝕌 12) blockSize _ _ ?_ ?_
  · rw [InjectivePlacement.active_bank]
    simp [Tapes.append]
  · refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · refine Fin.addCases (fun j => ?_) (fun b => ?_) x
      · rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ (fun b => natAdd_ne_castAdd b j)]
        simp [Tapes.append]
      · rw [InjectivePlacement.replace_head_slot]; simp [Tapes.append]
    · refine Fin.addCases (fun j => ?_) (fun b => ?_) x
      · rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ (fun b => natAdd_ne_castAdd b j)]
        simp [Tapes.append]
      · rw [InjectivePlacement.replace_tape_slot]; simp [Tapes.append]

/-! ### The multiply with the `FixedMul` interface -/

/-- The block's tapes and the multiply's tapes in the `12 + 91` bank. -/
abbrev bF : Fin (12 + 𝕌) := Fin.natAdd 12 zF
abbrev bG : Fin (12 + 𝕌) := Fin.natAdd 12 zG
abbrev bP : Fin (12 + 𝕌) := Fin.natAdd 12 iP
abbrev bW : Fin (12 + 𝕌) := Fin.natAdd 12 iW
abbrev bO : Fin (12 + 𝕌) := Fin.natAdd 12 zO
abbrev mX : Fin (12 + 𝕌) := Fin.castAdd 𝕌 0
abbrev mY : Fin (12 + 𝕌) := Fin.castAdd 𝕌 1
abbrev mO : Fin (12 + 𝕌) := Fin.castAdd 𝕌 6
abbrev mRp : Fin (12 + 𝕌) := Fin.castAdd 𝕌 7
abbrev mRw : Fin (12 + 𝕌) := Fin.castAdd 𝕌 8

/-- The blank block. -/
def blk : Tapes 𝕌 0 := ⟨fun _ => 0, fun _ => fun _ => blank⟩

/-- A bank with the blank block appended. -/
def blkAppend {n : ℕ} (v : Tapes n 0) : Tapes (n + 𝕌) 0 := v.append blk

theorem blkAppend_reads {n : ℕ} (v : Tapes n 0) (i : Fin n) :
    (blkAppend v).reads (Fin.castAdd 𝕌 i) = v.reads i := by
  simp [blkAppend, Tapes.reads, Tapes.append]

/-- Copy in, multiply on the block, copy out, erase the block. -/
noncomputable def fastMul :=
  Machine.seq (copyAt mX bF (by decide)) <| Machine.seq (copyAt mY bG (by decide)) <|
  Machine.seq (copyAt mRp bP (by decide)) <| Machine.seq (copyAt mRw bW (by decide)) <|
  Machine.seq (onBlock fmProg) <| Machine.seq (copyAt bO mO (by decide)) <|
  Machine.seq (eraseAt bO) <| Machine.seq (eraseAt bF) <| Machine.seq (eraseAt bG) <|
  Machine.seq (eraseAt bP) (eraseAt bW)

theorem wordAt_eq (bs : List Bool) : wordAt (a := 0) bs = putWord (fun _ => blank) 0 (bs.map bitSymbol) := by
  funext j; rw [putWord_blank, sub_zero]; rfl

theorem ruler_ones (n : ℕ) : FixedMul.ruler (a := 0) n = (ones n).map bitSymbol := by
  simp [FixedMul.ruler, ones, List.map_replicate]

theorem bits_nonblank' (bs : List Bool) : ∀ x ∈ bs.map (bitSymbol (a := 0)), x ≠ blank := by
  intro x hx; simp only [List.mem_map] at hx; obtain ⟨b, -, rfl⟩ := hx; exact bitSymbol_ne_blank b

theorem result_length' (x y : List Bool) (p w : ℕ) : (FixedMul.result x y p w).length = w := by
  unfold FixedMul.result; split_ifs <;> simp [TwosComplement.negWord_length, Gather.field]

set_option maxHeartbeats 8000000 in
/-- `FixedMul.mul_hoare` for the quasi-linear multiply, with a blank block appended. -/
theorem fastMul_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin 4)
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    HoareTime fastMul
      (· = (FixedMul.bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (fun _ => blank)
        (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank)
        (putWord (fun _ => blank) pRp (FixedMul.ruler p)) (putWord (fun _ => blank) pRw (FixedMul.ruler w))
        (putWord (fun _ => blank) pR2 (FixedMul.ruler (2 * w))) (fun _ => blank) (fun _ => blank)
        pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2).append blk)
      (· = (FixedMul.bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (fun _ => blank)
        (fun _ => blank) (fun _ => blank) (fun _ => blank)
        (putWord (fun _ => blank) pO ((FixedMul.result x y p w).map bitSymbol))
        (putWord (fun _ => blank) pRp (FixedMul.ruler p)) (putWord (fun _ => blank) pRw (FixedMul.ruler w))
        (putWord (fun _ => blank) pR2 (FixedMul.ruler (2 * w))) (fun _ => blank) (fun _ => blank)
        pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2).append blk)
      (fmTime w + 30 * w + 100) := by
  set res := FixedMul.result x y p w
  have hres : res.length = w := result_length' x y p w
  set L0 := FixedMul.bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (fun _ => blank)
    (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank)
    (putWord (fun _ => blank) pRp (FixedMul.ruler (a := 0) p)) (putWord (fun _ => blank) pRw (FixedMul.ruler w))
    (putWord (fun _ => blank) pR2 (FixedMul.ruler (2 * w))) (fun _ => blank) (fun _ => blank)
    pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 with hL0
  set v0 := L0.append blk
  have hLh : ∀ j, (v0.head (Fin.castAdd 𝕌 j)) = L0.head j := fun j => by simp [v0, Tapes.append]
  have hLt : ∀ j, (v0.tape (Fin.castAdd 𝕌 j)) = L0.tape j := fun j => by simp [v0, Tapes.append]
  have hBh : ∀ b, (v0.head (Fin.natAdd 12 b)) = 0 := fun b => by simp [v0, Tapes.append, blk]
  have hBt : ∀ b, (v0.tape (Fin.natAdd 12 b)) = fun _ => blank := fun b => by simp [v0, Tapes.append, blk]
  have h1 := copyAt_hoare (i := mX) (j := bF) (by decide) v0 (f := f) (p := pX) (r := 0)
    (xs := x.map bitSymbol) (bits_nonblank' x) (by rw [hLh]; simp [hL0, FixedMul.bank])
    (by rw [hLt]; simp [hL0, FixedMul.bank]) hfl (by rw [List.length_map, hx]; exact hfr) (hBh _) (hBt _)
  set T1 := Function.update v0.tape bF (putWord (fun _ => blank) 0 (x.map bitSymbol))
  have h2 := copyAt_hoare (i := mY) (j := bG) (by decide) ⟨v0.head, T1⟩ (f := g) (p := pY) (r := 0)
    (xs := y.map bitSymbol) (bits_nonblank' y) (by simp only; rw [hLh]; simp [hL0, FixedMul.bank])
    (by simp only [T1]; rw [Function.update_of_ne (by decide), hLt]; simp [hL0, FixedMul.bank]) hgl
    (by rw [List.length_map, hy]; exact hgr) (hBh zG)
    (by simp only [T1]; rw [Function.update_of_ne (by decide), hBt])
  set T2 := Function.update T1 bG (putWord (fun _ => blank) 0 (y.map bitSymbol))
  have h3 := copyAt_hoare (i := mRp) (j := bP) (by decide) ⟨v0.head, T2⟩ (f := fun _ => blank) (p := pRp)
    (r := 0) (xs := (ones p).map bitSymbol) (bits_nonblank' _) (by simp only; rw [hLh]; simp [hL0, FixedMul.bank])
    (by simp only [T2, T1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hLt]
        simp [hL0, FixedMul.bank, ruler_ones]) rfl rfl (hBh iP)
    (by simp only [T2, T1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hBt])
  set T3 := Function.update T2 bP (putWord (fun _ => blank) 0 ((ones p).map bitSymbol))
  have h4 := copyAt_hoare (i := mRw) (j := bW) (by decide) ⟨v0.head, T3⟩ (f := fun _ => blank) (p := pRw)
    (r := 0) (xs := (ones w).map bitSymbol) (bits_nonblank' _) (by simp only; rw [hLh]; simp [hL0, FixedMul.bank])
    (by simp only [T3, T2, T1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hLt]
        simp [hL0, FixedMul.bank, ruler_ones]) rfl rfl (hBh iW)
    (by simp only [T3, T2, T1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hBt])
  set T4 := Function.update T3 bW (putWord (fun _ => blank) 0 ((ones w).map bitSymbol))
  have e4 : (⟨v0.head, T4⟩ : Tapes (12 + 𝕌) 0) = L0.append (rawFM x y p w []) := by
    refine Placement.Tapes.ext' (fun z => ?_) (fun z => ?_)
    · refine Fin.addCases (fun j => ?_) (fun b => ?_) z
      · simp [v0, Tapes.append]
      · simp [v0, Tapes.append, blk, rawFM]
    · refine Fin.addCases (fun j => ?_) (fun b => ?_) z
      · simp only [T4, T3, T2, T1]
        rw [Function.update_of_ne (natAdd_ne_castAdd _ _).symm, Function.update_of_ne (natAdd_ne_castAdd _ _).symm,
          Function.update_of_ne (natAdd_ne_castAdd _ _).symm, Function.update_of_ne (natAdd_ne_castAdd _ _).symm]
        simp [v0, Tapes.append]
      · simp only [T4, T3, T2, T1, Function.update_apply, (Fin.natAdd_injective 𝕌 12).eq_iff]
        simp only [Tapes.append, Fin.addCases_right, rawFM]
        by_cases e1 : b = zF
        · subst e1; tsimp [wordAt_eq]
        by_cases e2 : b = zG
        · subst e2; tsimp [wordAt_eq]
        by_cases e3 : b = iP
        · subst e3; tsimp [wordAt_eq]
        by_cases e4 : b = iW
        · subst e4; tsimp [wordAt_eq]
        by_cases e5 : b = zO
        · subst e5; tsimp [hBt, putWord, wordAt_nil]
        tsimp [e1, e2, e3, e4, e5, hBt]
  have h5 := onBlock_hoare (fmProg_time hx hy hw hpw) L0
  set v5 := L0.append (rawFM x y p w res)
  have h5h : ∀ b, v5.head (Fin.natAdd 12 b) = 0 := fun b => by simp [v5, Tapes.append, rawFM]
  have h6 := copyAt_hoare (i := bO) (j := mO) (by decide) v5 (f := fun _ => blank) (p := 0) (r := pO)
    (xs := res.map bitSymbol) (bits_nonblank' _) (h5h zO) (by tsimp [v5, Tapes.append, rawFM, wordAt_eq]) rfl rfl
    (by simp [v5, Tapes.append, hL0, FixedMul.bank]) (by simp [v5, Tapes.append, hL0, FixedMul.bank])
  set U6 := Function.update v5.tape mO (putWord (fun _ => blank) pO (res.map bitSymbol))
  have h7 := eraseAt_hoare bO ⟨v5.head, U6⟩ (xs := res.map bitSymbol) (bits_nonblank' _) (h5h zO)
    (by simp only [U6]; rw [Function.update_of_ne (by decide)]; tsimp [v5, Tapes.append, rawFM, wordAt_eq])
  set U7 := Function.update U6 bO (fun _ => blank)
  have h8 := eraseAt_hoare bF ⟨v5.head, U7⟩ (xs := x.map bitSymbol) (bits_nonblank' _) (h5h zF)
    (by simp only [U7, U6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        tsimp [v5, Tapes.append, rawFM, wordAt_eq])
  set U8 := Function.update U7 bF (fun _ => blank)
  have h9 := eraseAt_hoare bG ⟨v5.head, U8⟩ (xs := y.map bitSymbol) (bits_nonblank' _) (h5h zG)
    (by simp only [U8, U7, U6]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        tsimp [v5, Tapes.append, rawFM, wordAt_eq])
  set U9 := Function.update U8 bG (fun _ => blank)
  have h10 := eraseAt_hoare bP ⟨v5.head, U9⟩ (xs := (ones p).map bitSymbol) (bits_nonblank' _) (h5h iP)
    (by simp only [U9, U8, U7, U6]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]
        tsimp [v5, Tapes.append, rawFM, wordAt_eq])
  set U10 := Function.update U9 bP (fun _ => blank)
  have h11 := eraseAt_hoare bW ⟨v5.head, U10⟩ (xs := (ones w).map bitSymbol) (bits_nonblank' _) (h5h iW)
    (by simp only [U10, U9, U8, U7, U6]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        tsimp [v5, Tapes.append, rawFM, wordAt_eq])
  have e11 : (⟨v5.head, Function.update U10 bW (fun _ => blank)⟩ : Tapes (12 + 𝕌) 0) =
      (FixedMul.bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (fun _ => blank)
        (fun _ => blank) (fun _ => blank) (fun _ => blank) (putWord (fun _ => blank) pO (res.map bitSymbol))
        (putWord (fun _ => blank) pRp (FixedMul.ruler p)) (putWord (fun _ => blank) pRw (FixedMul.ruler w))
        (putWord (fun _ => blank) pR2 (FixedMul.ruler (2 * w))) (fun _ => blank) (fun _ => blank)
        pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2).append blk := by
    refine Placement.Tapes.ext' (fun z => ?_) (fun z => ?_)
    · refine Fin.addCases (fun j => ?_) (fun b => ?_) z
      · simp [v5, Tapes.append, hL0, FixedMul.bank]
      · simp [v5, Tapes.append, blk, rawFM]
    · refine Fin.addCases (fun j => ?_) (fun b => ?_) z
      · simp only [U10, U9, U8, U7, U6]
        rw [Function.update_of_ne (natAdd_ne_castAdd _ _).symm, Function.update_of_ne (natAdd_ne_castAdd _ _).symm,
          Function.update_of_ne (natAdd_ne_castAdd _ _).symm, Function.update_of_ne (natAdd_ne_castAdd _ _).symm,
          Function.update_of_ne (natAdd_ne_castAdd _ _).symm]
        simp only [Function.update_apply, (Fin.castAdd_injective 12 𝕌).eq_iff]
        simp only [v5, Tapes.append, Fin.addCases_left, hL0]
        fin_cases j <;> simp [FixedMul.bank]
      · simp only [U10, U9, U8, U7, U6, Function.update_apply, (Fin.natAdd_injective 𝕌 12).eq_iff,
          show ∀ b : Fin 𝕌, Fin.natAdd 12 b = mO ↔ False from fun b => ⟨natAdd_ne_castAdd b 6, False.elim⟩]
        simp only [v5, Tapes.append, Fin.addCases_right, rawFM, blk]
        by_cases e1 : b = zF
        · subst e1; tsimp
        by_cases e2 : b = zG
        · subst e2; tsimp
        by_cases e3 : b = iP
        · subst e3; tsimp
        by_cases e4 : b = iW
        · subst e4; tsimp
        by_cases e5 : b = zO
        · subst e5; tsimp
        tsimp [e1, e2, e3, e4, e5]
  refine (h1.seq (h2.seq (h3.seq (h4.seq ((h5.consequence (fun v e => e.trans e4) (fun v e => e) le_rfl).seq
    (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq h11)))))))))).consequence (fun v e => e)
    (fun v e => e.trans e11) ?_
  simp only [List.length_map, length_ones, hx, hy, hres]
  omega

/-! ### Placing a machine with a block in a larger bank -/

/-- A machine's own `k` tapes at `S`, its block on the appended block. -/
def mulSlot {k n : ℕ} (S : Fin k → Fin n) : Fin (k + 𝕌) → Fin (n + 𝕌) :=
  Fin.addCases (fun j => Fin.castAdd 𝕌 (S j)) (fun b => Fin.natAdd n b)

theorem mulSlot_inj {k n : ℕ} {S : Fin k → Fin n} (hS : Function.Injective S) : Function.Injective (mulSlot S) := by
  intro x y
  refine Fin.addCases (fun j => ?_) (fun b => ?_) x <;> refine Fin.addCases (fun j' => ?_) (fun b' => ?_) y <;>
    intro e <;> simp only [mulSlot, Fin.addCases_left, Fin.addCases_right] at e ⊢
  · exact congrArg _ (hS (Fin.castAdd_injective _ _ e))
  · exfalso; have := congrArg Fin.val e; simp at this; have := (S j).isLt; omega
  · exfalso; have := congrArg Fin.val e; simp at this; have := (S j').isLt; omega
  · exact congrArg _ (Fin.natAdd_injective _ _ e)

theorem mulSize {k n : ℕ} (hn : k ≤ n) : k + 𝕌 + (n - k) = n + 𝕌 := by omega

/-- `M` with its own tapes at `S` and its block on the appended block. -/
noncomputable def placeMul {k n : ℕ} (S : Fin k → Fin n) (hS : Function.Injective S) (hn : k ≤ n) {q : ℕ}
    (M : Program (k + 𝕌) q 0) : Program (n + 𝕌) q 0 :=
  Placement.placed M (InjectivePlacement.placement (mulSlot S) (mulSlot_inj hS) (mulSize hn))

theorem placeMul_hoare {k n : ℕ} {S : Fin k → Fin n} (hS : Function.Injective S) (hn : k ≤ n) {q : ℕ}
    {M : Program (k + 𝕌) q 0} {A A' : Tapes k 0} {c : ℕ}
    (hM : HoareTime M (· = A.append blk) (· = A'.append blk) c) (V V' : Tapes n 0)
    (hA : ∀ j, V.head (S j) = A.head j ∧ V.tape (S j) = A.tape j)
    (hA' : ∀ j, V'.head (S j) = A'.head j ∧ V'.tape (S j) = A'.tape j)
    (hr : ∀ i, (∀ j, S j ≠ i) → V'.head i = V.head i ∧ V'.tape i = V.tape i) :
    HoareTime (placeMul S hS hn M) (· = V.append blk) (· = V'.append blk) c := by
  refine InjectivePlacement.hoare_exact hM (mulSlot S) (mulSlot_inj hS) (mulSize hn) _ _ ?_ ?_
  · rw [InjectivePlacement.active_bank]
    congr 1 <;> funext x <;> refine Fin.addCases (fun j => ?_) (fun b => ?_) x <;>
      simp [mulSlot, Tapes.append, hA]
  · refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun b => ?_) x
    · by_cases hi : ∃ j, S j = i
      · obtain ⟨j, rfl⟩ := hi
        have := InjectivePlacement.replace_head_slot (mulSlot S) (mulSlot_inj hS) (mulSize hn) (V.append blk)
          (A'.append blk) (Fin.castAdd 𝕌 j)
        simp only [mulSlot, Fin.addCases_left] at this
        rw [this]; simp [Tapes.append, hA']
      · push Not at hi
        rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ (fun k => by
          refine Fin.addCases (fun j => ?_) (fun b => ?_) k
          · simp only [mulSlot, Fin.addCases_left]; exact fun e => hi j (Fin.castAdd_injective _ _ e)
          · simp only [mulSlot, Fin.addCases_right]
            intro e; have := congrArg Fin.val e; simp at this; have := i.isLt; omega)]
        simp [Tapes.append, (hr i hi).1]
    · have := InjectivePlacement.replace_head_slot (mulSlot S) (mulSlot_inj hS) (mulSize hn) (V.append blk)
        (A'.append blk) (Fin.natAdd k b)
      simp only [mulSlot, Fin.addCases_right] at this
      rw [this]; simp [Tapes.append]
    · by_cases hi : ∃ j, S j = i
      · obtain ⟨j, rfl⟩ := hi
        have := InjectivePlacement.replace_tape_slot (mulSlot S) (mulSlot_inj hS) (mulSize hn) (V.append blk)
          (A'.append blk) (Fin.castAdd 𝕌 j)
        simp only [mulSlot, Fin.addCases_left] at this
        rw [this]; simp [Tapes.append, hA']
      · push Not at hi
        rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ (fun k => by
          refine Fin.addCases (fun j => ?_) (fun b => ?_) k
          · simp only [mulSlot, Fin.addCases_left]; exact fun e => hi j (Fin.castAdd_injective _ _ e)
          · simp only [mulSlot, Fin.addCases_right]
            intro e; have := congrArg Fin.val e; simp at this; have := i.isLt; omega)]
        simp [Tapes.append, (hr i hi).2]
    · have := InjectivePlacement.replace_tape_slot (mulSlot S) (mulSlot_inj hS) (mulSize hn) (V.append blk)
        (A'.append blk) (Fin.natAdd k b)
      simp only [mulSlot, Fin.addCases_right] at this
      rw [this]; simp [Tapes.append]

end IntegerMultBounds.Schoenhage
