module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-!
# Packed arrays on the table machine

Subroutines of the table machine (`IntegerMultBounds.MathlibTM2.Fast.TableVM`) used by the writers of the layout
description streams. An array `f : ℕ → ℕ` of `M` entries below a radix `R` is packed into the
number `ldwPack R f M = ∑_{c < M} f c R^c` (`ldwPack_field`: entry `c` is
`ldwPack R f M / R^c % R`).

* `ldwPowR Rc R e k`: `Rc := R ^ e` by `e` multiplications (`ldwPowR_do`).
* `ldwField V Rc R t y`: `y := V / Rc % R` (`ldwField_do`).
* `ldwMap … blk`: rebuild the packed array `V` entry by entry, entry `c` replaced by `G (f c)`,
  where the block `blk` computes `y2 := G y` (`ldwMap_do`).

Frames: `ldwFr s s' M` says that `s'` agrees with `s` on every variable outside the list `M`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- Close goals `a ≠ b`, `¬ a = b`, `x ∉ [a, b, …]` and their conjunctions from distinctness
hypotheses in either direction. -/
macro "ldw_dist" : tactic => `(tactic| (
  try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, ne_eq]
  repeat' constructor
  all_goals first | assumption | exact Ne.symm ‹_› | skip))

/-! ### Packed arrays -/

/-- The packed array of the first `M` entries of `f` in radix `R`. -/
def ldwPack (R : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | M + 1 => ldwPack R f M + f M * R ^ M

theorem ldwPack_lt {R : ℕ} {f : ℕ → ℕ} : ∀ {M : ℕ}, (∀ c < M, f c < R) → ldwPack R f M < R ^ M
  | 0, _ => by simp [ldwPack]
  | M + 1, hf => by
      have h1 := ldwPack_lt (M := M) (fun c hc => hf c (by omega))
      have h2 : f M + 1 ≤ R := hf M (by omega)
      rw [ldwPack, pow_succ]
      nlinarith

theorem ldwPack_congr {R : ℕ} {f g : ℕ → ℕ} : ∀ {M : ℕ}, (∀ c < M, f c = g c) →
    ldwPack R f M = ldwPack R g M
  | 0, _ => rfl
  | M + 1, h => by
      rw [ldwPack, ldwPack, ldwPack_congr (fun c hc => h c (by omega)), h M (by omega)]

/-- Entry `i` of a packed array. -/
theorem ldwPack_field {R : ℕ} (hR : 0 < R) {f : ℕ → ℕ} :
    ∀ {M : ℕ}, (∀ c < M, f c < R) → ∀ i < M, ldwPack R f M / R ^ i % R = f i
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | M + 1, hf, i, hi => by
      have hlo := ldwPack_lt (R := R) (f := f) (M := M) (fun c hc => hf c (by omega))
      rcases Nat.lt_or_ge i M with him | him
      · -- the top entry does not affect the entries below
        have e : ldwPack R f (M + 1) / R ^ i =
            ldwPack R f M / R ^ i + f M * R ^ (M - i) := by
          rw [ldwPack, show R ^ M = R ^ i * R ^ (M - i) by rw [← pow_add]; congr 1; omega,
            ← mul_assoc, mul_comm (f M) (R ^ i), mul_assoc, Nat.add_mul_div_left _ _ (by positivity)]
        rw [e, show M - i = (M - i - 1) + 1 by omega, pow_succ, ← mul_assoc, Nat.add_mul_mod_self_right]
        exact ldwPack_field hR (fun c hc => hf c (by omega)) i him
      · have hiM : i = M := by omega
        subst hiM
        rw [ldwPack, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add,
          Nat.mod_eq_of_lt (hf i (by omega))]

theorem ldwPack_le {R : ℕ} {f : ℕ → ℕ} {M M' : ℕ} (hM : M ≤ M') :
    ldwPack R f M ≤ ldwPack R f M' := by
  induction hM with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (by rw [ldwPack]; omega)

/-! ### Frames -/

variable {n A W w : ℕ}

/-- `s'` agrees with `s` outside the variables `M`. -/
def ldwFr (s s' : TblSt n A) (M : List (Fin n)) : Prop := ∀ x, x ∉ M → s'.val x = s.val x

theorem ldwFr.refl (s : TblSt n A) (M : List (Fin n)) : ldwFr s s M := fun _ _ => rfl

theorem ldwFr.trans {s₁ s₂ s₃ : TblSt n A} {M₁ M₂ M : List (Fin n)} (h₁ : ldwFr s₁ s₂ M₁)
    (h₂ : ldwFr s₂ s₃ M₂) (hs₁ : ∀ x ∈ M₁, x ∈ M) (hs₂ : ∀ x ∈ M₂, x ∈ M) : ldwFr s₁ s₃ M :=
  fun x hx => (h₂ x fun h => hx (hs₂ x h)).trans (h₁ x fun h => hx (hs₁ x h))

theorem ldwFr.mono {s s' : TblSt n A} {M M' : List (Fin n)} (h : ldwFr s s' M)
    (hs : ∀ x ∈ M, x ∈ M') : ldwFr s s' M' := fun x hx => h x fun h' => hx (hs x h')

/-! ### Powers -/

/-- `Rc := R ^ e`, counting on `k`. -/
def ldwPowR (Rc R e k : Fin n) : TblCode n :=
  .seq (.ins (.zero Rc)) (.seq (.ins (.inc Rc)) (tblFor k e (.ins (.mul Rc R Rc))))

/-- `ldwPowR`: `Rc := R ^ e`, `k := e`; `4 e + 5` atoms. -/
theorem ldwPowR_do {Rc R e k : Fin n} (h1 : Rc ≠ R) (h2 : Rc ≠ e) (h3 : Rc ≠ k) (h4 : R ≠ k)
    (h5 : e ≠ k) (st : TblSt n A) (hR : 1 ≤ st.val R) (hW : st.val R ^ st.val e < 2 ^ W)
    (heW : st.val e < 2 ^ W) :
    TblDo A W w (ldwPowR Rc R e k) st (fun s => s.val Rc = st.val R ^ st.val e ∧
      s.val k = st.val e ∧ ldwFr st s [Rc, k] ∧ s.acc = st.acc) (4 * st.val e + 5) := by
  have h1W : 1 < 2 ^ W := by
    have := Nat.one_le_pow (st.val e) (st.val R) hR
    omega
  have hpow : ∀ j ≤ st.val e, st.val R ^ j < 2 ^ W := fun j hj =>
    lt_of_le_of_lt (Nat.pow_le_pow_right hR hj) hW
  have hz := TblDo.ins (A := A) (W := W) (w := w) (.zero Rc) (st := st)
    (P := fun s => s = ⟨Function.update st.val Rc 0, st.acc⟩) (by simp [TblIns.run])
  have hi : ∀ s : TblSt n A, s = ⟨Function.update st.val Rc 0, st.acc⟩ →
      TblDo A W w (.ins (.inc Rc)) s (fun s' => s' = ⟨Function.update st.val Rc 1, st.acc⟩) 1 := by
    intro s hs
    subst hs
    exact TblDo.ins _ (by simp [TblIns.run, Nat.mod_eq_of_lt h1W])
  have hf : TblDo A W w (tblFor k e (.ins (.mul Rc R Rc))) ⟨Function.update st.val Rc 1, st.acc⟩
      (fun s => s.val Rc = st.val R ^ st.val e ∧ s.val k = st.val e ∧ ldwFr st s [Rc, k] ∧
        s.acc = st.acc) (1 + (st.val e * (1 + 1 + 2) + 2)) := by
    refine TblDo.for (st.val e) 1 (by simp [Function.update_of_ne (Ne.symm h2)]) heW h5.symm
      (fun j s => s.val Rc = st.val R ^ j ∧ ldwFr st s [Rc, k] ∧ s.acc = st.acc)
      ⟨by simp [Function.update_of_ne h3], fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [Function.update_of_ne hx.1, Function.update_of_ne hx.2], rfl⟩ ?_ ?_
    · intro j hj s ⟨hc, hfr, hacc⟩ hsi hsn
      have hRv : s.val R = st.val R := hfr R (by simp [Ne.symm h1, h4])
      refine TblDo.ins _ ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [TblIns.run, Function.update_of_ne (Ne.symm h3), hsi]
      · simp [TblIns.run, Function.update_of_ne (Ne.symm h2), hsn]
      · simp only [TblIns.run, Function.update_of_ne h3, Function.update_self, hc, hRv]
        rw [← pow_succ, Nat.mod_eq_of_lt (hpow _ (by omega))]
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [TblIns.run, Function.update_of_ne hx.1, Function.update_of_ne hx.2,
          hfr x (by simp [hx.1, hx.2])]
      · simp [TblIns.run, hacc]
    · intro s ⟨hc, hfr, hacc⟩ hsi _
      exact ⟨hc, hsi, hfr, hacc⟩
  exact (hz.seq fun s hs => (hi s hs).seq fun s' hs' => hs' ▸ hf).mono (fun _ h => h) (by omega)

/-! ### Reading an entry -/

/-- `t := V / Rc`, `y := t % R`. -/
def ldwField (V Rc R t y : Fin n) : TblCode n := .seq (.ins (.div V Rc t)) (.ins (.mod t R y))

theorem ldwField_do {V Rc R t y : Fin n} (h1 : t ≠ R) (st : TblSt n A) :
    TblDo A W w (ldwField V Rc R t y) st (fun s => s.val y = st.val V / st.val Rc % st.val R ∧
      ldwFr st s [t, y] ∧ s.acc = st.acc) 2 := by
  have h2' : ∀ s : TblSt n A, s = TblIns.run A W w (.div V Rc t) st →
      TblDo A W w (.ins (.mod t R y)) s (fun s => s.val y = st.val V / st.val Rc % st.val R ∧
        ldwFr st s [t, y] ∧ s.acc = st.acc) 1 := by
    intro s hs
    subst hs
    refine TblDo.ins _ ⟨?_, ?_, ?_⟩
    · simp [TblIns.run, Function.update_of_ne (Ne.symm h1)]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [TblIns.run, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
    · simp [TblIns.run]
  exact (TblDo.ins (.div V Rc t) (P := fun s => s = TblIns.run A W w (.div V Rc t) st) rfl).seq h2'

/-! ### Mapping over a packed array -/

/-- One entry of the map: read entry `c` into `y` (`Rc = R ^ c`), run `blk` (computing `y2`),
add `y2 Rc` to the new array `V2`, and multiply `Rc` by `R`. -/
def ldwMapBody (V V2 Rc R t y y2 : Fin n) (blk : TblCode n) : TblCode n :=
  ldwField V Rc R t y ;; blk ;; .ins (.mul y2 Rc t) ;; .ins (.add V2 t V2) ;; .ins (.mul Rc R Rc)

/-- Map the block `blk` over the `M` entries of the packed array `V` (radix `R`), counting on
`c`; the result replaces `V`. -/
def ldwMap (V V2 Rc R c M t y y2 : Fin n) (blk : TblCode n) : TblCode n :=
  .ins (.zero V2) ;; .ins (.zero Rc) ;; .ins (.inc Rc) ;;
    tblFor c M (ldwMapBody V V2 Rc R t y y2 blk) ;; .ins (.copy V2 V)

/-- **Mapping over a packed array.** If `V` holds `ldwPack R f M` and the block computes
`y2 := G c y` for the entry `y` at index `c` (changing only `y2` and the variables `Mb`), then
`ldwMap` leaves `ldwPack R (fun c => G c (f c)) M` on `V`; `M (Kb + 8) + 7` atoms. -/
theorem ldwMap_do {V V2 Rc R c M t y y2 : Fin n} (hnd : [V, V2, Rc, R, c, M, t, y, y2].Nodup)
    {blk : TblCode n} (st : TblSt n A) {f : ℕ → ℕ} {G : ℕ → ℕ → ℕ} {Mlen Rv : ℕ}
    (hM : st.val M = Mlen)
    (hRv : st.val R = Rv) (hR1 : 1 ≤ Rv) (hV : st.val V = ldwPack Rv f Mlen)
    (hf : ∀ c < Mlen, f c < Rv) (hG : ∀ c < Mlen, G c (f c) < Rv) (hW : Rv ^ Mlen < 2 ^ W)
    (hMW : Mlen < 2 ^ W) (Mb : List (Fin n)) (hMb : ∀ x ∈ Mb, x ∉ [V, V2, Rc, R, c, M, t, y])
    (Kb : ℕ)
    (hblk : ∀ j < Mlen, ∀ s : TblSt n A, ldwFr st s (V2 :: Rc :: c :: t :: y :: y2 :: Mb) →
      s.val c = j → s.val y < Rv → s.acc = st.acc → TblDo A W w blk s (fun s' =>
        s'.val y2 = G j (s.val y) ∧ ldwFr s s' (y2 :: Mb) ∧ s'.acc = s.acc) Kb) :
    TblDo A W w (ldwMap V V2 Rc R c M t y y2 blk) st
      (fun s => s.val V = ldwPack Rv (fun c => G c (f c)) Mlen ∧
        ldwFr st s (V :: V2 :: Rc :: c :: t :: y :: y2 :: Mb) ∧ s.acc = st.acc)
      (Mlen * (Kb + 8) + 7) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3, b4, b5, b6, b7⟩, ⟨c1, c2, c3, c4, c5, c6⟩,
    ⟨d1, d2, d3, d4, d5⟩, ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3⟩, ⟨g1, g2⟩, g3⟩ := hnd
  have nMb : ∀ z, z ∈ [V, V2, Rc, R, c, M, t, y] → z ∉ Mb := fun z hz hzM => hMb z hzM hz
  have hpowle : ∀ j ≤ Mlen, Rv ^ j ≤ Rv ^ Mlen := fun j hj => Nat.pow_le_pow_right hR1 hj
  have h1W : 1 < 2 ^ W := by have := Nat.one_le_pow Mlen Rv hR1; omega
  -- the counting loop
  have hloop : ∀ s0 : TblSt n A, s0.val V2 = 0 → s0.val Rc = 1 → ldwFr st s0 [V2, Rc] →
      s0.acc = st.acc →
      TblDo A W w (tblFor c M (ldwMapBody V V2 Rc R t y y2 blk)) s0
        (fun s => s.val V2 = ldwPack Rv (fun c => G c (f c)) Mlen ∧
          ldwFr st s (V2 :: Rc :: c :: t :: y :: y2 :: Mb) ∧ s.acc = st.acc)
        (1 + (Mlen * ((Kb + 5) + 1 + 2) + 2)) := by
    intro s0 hv2 hrc hfr0 hacc0
    have hM0 : s0.val M = Mlen := by rw [hfr0 M (by ldw_dist)]; exact hM
    refine TblDo.for Mlen (Kb + 5) hM0 hMW e1
      (fun j s => s.val V2 = ldwPack Rv (fun c => G c (f c)) j ∧ s.val Rc = Rv ^ j ∧
        ldwFr st s (V2 :: Rc :: c :: t :: y :: y2 :: Mb) ∧ s.acc = st.acc) ⟨?_, ?_, ?_, hacc0⟩ ?_ ?_
    · show Function.update s0.val c 0 V2 = _
      rw [Function.update_of_ne (by ldw_dist), hv2]; rfl
    · show Function.update s0.val c 0 Rc = _
      rw [Function.update_of_ne (by ldw_dist), hrc]; rfl
    · intro x hx
      simp only [List.mem_cons, not_or] at hx
      simp only
      rw [Function.update_of_ne hx.2.2.1]
      exact hfr0 x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hx.1, hx.2.1⟩)
    · intro j hj s ⟨hv2s, hrcs, hfrs, haccs⟩ hsi hsn
      have hVs : s.val V = ldwPack Rv f Mlen := by
        rw [hfrs V (by ldw_dist; exact nMb V (by simp))]; exact hV
      have hRs : s.val R = Rv := by
        rw [hfrs R (by ldw_dist; exact nMb R (by simp))]; exact hRv
      -- read the entry
      have hF := ldwField_do (A := A) (W := W) (w := w) (V := V) (Rc := Rc) (R := R) (t := t) (y := y) (by ldw_dist : t ≠ R) s
      refine TblDo.mono (K := 2 + (Kb + (1 + (1 + 1)))) ?_ (fun _ h => h) (by omega)
      refine hF.seq fun s1 ⟨hy1, hfr1, hacc1⟩ => ?_
      have hy1' : s1.val y = f j := by
        rw [hy1, hVs, hrcs, hRs]
        exact ldwPack_field (by omega) hf j hj
      have hfr1' : ldwFr st s1 (V2 :: Rc :: c :: t :: y :: y2 :: Mb) :=
        hfrs.trans hfr1 (fun x hx => hx) (by simp)
      -- the block
      have hc1 : s1.val c = j := by rw [hfr1 c (by ldw_dist)]; exact hsi
      refine ((hblk j hj s1 hfr1' hc1 (by rw [hy1']; exact hf j hj) (by rw [hacc1, haccs])).seq
        fun s2 ⟨hy2, hfr2, hacc2⟩ => ?_)
      have hfr2' : ldwFr st s2 (V2 :: Rc :: c :: t :: y :: y2 :: Mb) :=
        hfr1'.trans hfr2 (fun x hx => hx) (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
      have g21 : ∀ x, x ≠ y2 → x ∉ Mb → x ≠ t → x ≠ y → s2.val x = s.val x := by
        intro x h1 h2 h3 h4
        rw [hfr2 x (by simp only [List.mem_cons, not_or]; exact ⟨h1, h2⟩),
          hfr1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h3, h4⟩)]
      have hRc2 : s2.val Rc = Rv ^ j := by
        rw [g21 Rc (by ldw_dist) (nMb Rc (by simp)) (by ldw_dist) (by ldw_dist)]; exact hrcs
      have hV22 : s2.val V2 = ldwPack Rv (fun c => G c (f c)) j := by
        rw [g21 V2 (by ldw_dist) (nMb V2 (by simp)) (by ldw_dist) (by ldw_dist)]; exact hv2s
      have hR2 : s2.val R = Rv := by
        rw [g21 R (by ldw_dist) (nMb R (by simp)) (by ldw_dist) (by ldw_dist)]; exact hRs
      have hc2 : s2.val c = j := by
        rw [g21 c (by ldw_dist) (nMb c (by simp)) (by ldw_dist) (by ldw_dist)]; exact hsi
      have hM2 : s2.val M = Mlen := by
        rw [g21 M (by ldw_dist) (nMb M (by simp)) (by ldw_dist) (by ldw_dist)]; exact hsn
      have hGj : G j (f j) < Rv := hG j hj
      have hy22 : s2.val y2 = G j (f j) := by rw [hy2, hy1']
      have hpos : 0 < Rv ^ j := Nat.pos_of_ne_zero (by positivity)
      have hlt1 : G j (f j) * Rv ^ j < Rv ^ (j + 1) := by
        rw [pow_succ]; nlinarith
      have hlt2 : ldwPack Rv (fun c => G c (f c)) (j + 1) < Rv ^ (j + 1) :=
        ldwPack_lt (fun c hc => hG c (by omega))
      have hW1 : Rv ^ (j + 1) < 2 ^ W := lt_of_le_of_lt (hpowle _ (by omega)) hW
      -- t := y2 * Rc
      refine (TblDo.insX (.mul y2 Rc t)
        (P := fun s3 => s3 = ⟨Function.update s2.val t (G j (f j) * Rv ^ j), s2.acc⟩)
        (by simp only [TblIns.fits, hy22, hRc2]; omega)
        (by simp [TblIns.exact, hy22, hRc2])).seq fun s3 hs3 => ?_
      subst hs3
      -- V2 := V2 + t
      have hfitA : TblIns.fits A W (.add V2 t V2)
          (⟨Function.update s2.val t (G j (f j) * Rv ^ j), s2.acc⟩ : TblSt n A) := by
        show (Function.update s2.val t (G j (f j) * Rv ^ j)) V2 +
          (Function.update s2.val t (G j (f j) * Rv ^ j)) t < 2 ^ W
        rw [Function.update_of_ne (by ldw_dist), Function.update_self, hV22]
        have : ldwPack Rv (fun c => G c (f c)) j + G j (f j) * Rv ^ j =
            ldwPack Rv (fun c => G c (f c)) (j + 1) := rfl
        omega
      refine (TblDo.insX (.add V2 t V2)
        (P := fun s4 => s4 = ⟨Function.update (Function.update s2.val t (G j (f j) * Rv ^ j)) V2
          (ldwPack Rv (fun c => G c (f c)) (j + 1)), s2.acc⟩) hfitA
        (by
          simp only [TblIns.exact]
          rw [Function.update_of_ne (by ldw_dist), Function.update_self, hV22]
          rfl)).seq fun s4 hs4 => ?_
      subst hs4
      -- Rc := Rc * R
      have hRcv : (Function.update (Function.update s2.val t (G j (f j) * Rv ^ j)) V2
          (ldwPack Rv (fun c => G c (f c)) (j + 1))) Rc = Rv ^ j := by
        rw [Function.update_of_ne (by ldw_dist), Function.update_of_ne (by ldw_dist), hRc2]
      have hRv' : (Function.update (Function.update s2.val t (G j (f j) * Rv ^ j)) V2
          (ldwPack Rv (fun c => G c (f c)) (j + 1))) R = Rv := by
        rw [Function.update_of_ne (by ldw_dist), Function.update_of_ne (by ldw_dist), hR2]
      refine TblDo.insX (.mul Rc R Rc)
        (by simp only [TblIns.fits, hRcv, hRv']; rw [← pow_succ]; exact hW1) ⟨?_, ?_, ?_⟩
      · simp only [TblIns.exact]
        rw [Function.update_of_ne (by ldw_dist), Function.update_of_ne (by ldw_dist),
          Function.update_of_ne (by ldw_dist), hc2]
      · simp only [TblIns.exact]
        rw [Function.update_of_ne (by ldw_dist), Function.update_of_ne (by ldw_dist),
          Function.update_of_ne (by ldw_dist), hM2]
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [TblIns.exact]
          rw [Function.update_of_ne (by ldw_dist), Function.update_of_ne (by ldw_dist),
            Function.update_self]
        · simp only [TblIns.exact]
          rw [Function.update_of_ne (by ldw_dist), Function.update_self, hRcv, hRv', ← pow_succ]
        · intro x hx
          have hx' := hx
          simp only [List.mem_cons, not_or] at hx'
          simp only [TblIns.exact]
          rw [Function.update_of_ne hx'.2.2.1, Function.update_of_ne hx'.2.1,
            Function.update_of_ne hx'.1, Function.update_of_ne hx'.2.2.2.1]
          exact hfr2' x hx
        · simp [TblIns.exact, hacc2, hacc1, haccs]
    · intro s ⟨h1, _, h3, h4⟩ _ _
      exact ⟨h1, h3, h4⟩
  -- the program
  have hz1 := TblDo.ins (A := A) (W := W) (w := w) (.zero V2) (st := st)
    (P := fun s => s = ⟨Function.update st.val V2 0, st.acc⟩) (by simp [TblIns.run])
  have hz2 : ∀ s : TblSt n A, s = ⟨Function.update st.val V2 0, st.acc⟩ →
      TblDo A W w (.ins (.zero Rc)) s
        (fun s' => s' = ⟨Function.update (Function.update st.val V2 0) Rc 0, st.acc⟩) 1 := by
    intro s hs; subst hs; exact TblDo.ins _ (by simp [TblIns.run])
  have hz3 : ∀ s : TblSt n A, s = ⟨Function.update (Function.update st.val V2 0) Rc 0, st.acc⟩ →
      TblDo A W w (.ins (.inc Rc)) s
        (fun s' => s' = ⟨Function.update (Function.update st.val V2 0) Rc 1, st.acc⟩) 1 := by
    intro s hs; subst hs
    exact TblDo.ins _ (by simp [TblIns.run, Nat.mod_eq_of_lt h1W])
  have hl := hloop ⟨Function.update (Function.update st.val V2 0) Rc 1, st.acc⟩
    (by simp only; rw [Function.update_of_ne (by ldw_dist), Function.update_self])
    (by simp only; rw [Function.update_self])
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp only
      rw [Function.update_of_ne hx.2, Function.update_of_ne hx.1]) rfl
  have hc : ∀ s : TblSt n A, (s.val V2 = ldwPack Rv (fun c => G c (f c)) Mlen ∧
      ldwFr st s (V2 :: Rc :: c :: t :: y :: y2 :: Mb) ∧ s.acc = st.acc) →
      TblDo A W w (.ins (.copy V2 V)) s (fun s => s.val V = ldwPack Rv (fun c => G c (f c)) Mlen ∧
        ldwFr st s (V :: V2 :: Rc :: c :: t :: y :: y2 :: Mb) ∧ s.acc = st.acc) 1 := by
    intro s ⟨hv, hfr, hacc⟩
    refine TblDo.ins _ ⟨?_, ?_, ?_⟩
    · simp [TblIns.run, hv]
    · intro x hx
      simp only [List.mem_cons, not_or] at hx
      simp only [TblIns.run]
      rw [Function.update_of_ne hx.1]
      exact hfr x (by simp only [List.mem_cons, not_or]; exact hx.2)
    · simp [TblIns.run, hacc]
  exact ((hz1.seq fun s1 h1 => (hz2 s1 h1).seq fun s2 h2 => (hz3 s2 h2).seq fun s3 h3 =>
    h3 ▸ hl.seq hc)).mono (fun _ h => h) (by ring_nf; omega)

end IntegerMultBounds.MathlibTM2.Fast.TableVM
