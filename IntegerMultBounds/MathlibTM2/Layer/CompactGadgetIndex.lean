module

public import IntegerMultBounds.MathlibTM2.Layer.CompactGadget
public import IntegerMultBounds.Compact.Repair

/-!
# The compact gadget on record ranks

Records are ranked by an index in the mixed radix with field lengths `len`
(`IntegerMultBounds.MathlibTM2.Host.digit`); `Fields` names the compact fields `b`, `t`, `u` and
the slots `y`, `x` among them. `view i` reads the five fields of index `i`, and `Op.idx` runs an
instruction on indices through `setDigit`: `view (o.idx i) = o.pure p (view i)` (`view_idx`), every
other digit and every bit above the fields is kept (`digit_idx`, `div_idx`).

`runIdx prog` and `idealIdx` are the actual and the ideal maps on indices. They agree on every
good index (`runIdx_prog_good`). Each instruction of `prog` is undone by `Op.inv`
(`inv_idx_idx`), so `runIdx prog` is a bijection (`actual`); `idealIdx` is an involution (`ideal`).
The ideal map preserves the good set, so the abstract repair of `IntegerMultBounds.Compact.Repair`
applies (`actual_good_iff`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactGadget

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Host Finset

variable (p : Par) {nf : ℕ} (len : Fin nf → ℕ)

/-- The five gadget fields among the index fields. -/
structure Fields (nf : ℕ) where
  b : Fin nf
  t : Fin nf
  u : Fin nf
  y : Fin nf
  x : Fin nf

variable (F : Fields nf)

/-- The field lengths fit the gadget and the five fields are distinct. -/
structure Fields.Valid : Prop where
  lb : len F.b = p.wc
  lt : len F.t = p.wc
  lu : len F.u = p.wc
  ly : len F.y = p.wy
  lx : len F.x = p.wy
  distinct : [F.b, F.t, F.u, F.y, F.x].Nodup

/-- The five fields of an index. -/
def view (i : ℕ) : V := ⟨digit len F.b i, digit len F.t i, digit len F.u i, digit len F.y i,
  digit len F.x i⟩

/-- An instruction on indices. -/
def Op.idx : Op → ℕ → ℕ
  | .rotY neg o, i => setDigit len F.y (rotv p.wy neg (o.eval p (view len F i)) (digit len F.y i)) i
  | .rotB neg o, i => setDigit len F.b (rotv p.wc neg (o.eval p (view len F i)) (digit len F.b i)) i
  | .swapT, i => setDigit len F.t (digit len F.b i) (setDigit len F.b (digit len F.t i) i)
  | .swapU, i => setDigit len F.u (digit len F.b i) (setDigit len F.b (digit len F.u i) i)

/-- Run a list of instructions on an index. -/
def runIdx (l : List Op) (i : ℕ) : ℕ := l.foldl (fun i o => o.idx p len F i) i

/-- The ideal map on indices. -/
def idealIdx (i : ℕ) : ℕ :=
  setDigit len F.y (togY p (fun c => par p c (digit len F.x i)) (digit len F.y i)) i

/-- A good index. -/
def GoodIdx (i : ℕ) : Prop := Good p (view len F i)

/-- The fields that an instruction may change. -/
def touched (g : Fin nf) : Prop := g = F.b ∨ g = F.t ∨ g = F.u ∨ g = F.y

variable {p len F}

/-! ### Digits after an instruction -/

section Digits

variable (hF : F.Valid p len)
include hF

private lemma ne_of (i j : Fin 5) (hij : i ≠ j) :
    ![F.b, F.t, F.u, F.y, F.x] i ≠ ![F.b, F.t, F.u, F.y, F.x] j := by
  have hd := hF.distinct
  have : (List.ofFn ![F.b, F.t, F.u, F.y, F.x]).Nodup := by simpa [List.ofFn_succ] using hd
  exact fun h => hij (List.nodup_ofFn.1 this h)

lemma hbt : F.b ≠ F.t := ne_of hF 0 1 (by decide)
lemma hbu : F.b ≠ F.u := ne_of hF 0 2 (by decide)
lemma hby : F.b ≠ F.y := ne_of hF 0 3 (by decide)
lemma hbx : F.b ≠ F.x := ne_of hF 0 4 (by decide)
lemma htu : F.t ≠ F.u := ne_of hF 1 2 (by decide)
lemma hty : F.t ≠ F.y := ne_of hF 1 3 (by decide)
lemma htx : F.t ≠ F.x := ne_of hF 1 4 (by decide)
lemma huy : F.u ≠ F.y := ne_of hF 2 3 (by decide)
lemma hux : F.u ≠ F.x := ne_of hF 2 4 (by decide)
lemma hyx : F.y ≠ F.x := ne_of hF 3 4 (by decide)

lemma digit_lt_b (i : ℕ) : digit len F.b i < 2 ^ p.wc := by
  rw [← hF.lb]; exact Nat.mod_lt _ (by positivity)
lemma digit_lt_t (i : ℕ) : digit len F.t i < 2 ^ p.wc := by
  rw [← hF.lt]; exact Nat.mod_lt _ (by positivity)
lemma digit_lt_u (i : ℕ) : digit len F.u i < 2 ^ p.wc := by
  rw [← hF.lu]; exact Nat.mod_lt _ (by positivity)
lemma digit_lt_y (i : ℕ) : digit len F.y i < 2 ^ p.wy := by
  rw [← hF.ly]; exact Nat.mod_lt _ (by positivity)

lemma fits_view (i : ℕ) : Fits p (view len F i) :=
  ⟨digit_lt_b hF i, digit_lt_t hF i, digit_lt_u hF i, digit_lt_y hF i⟩

lemma view_set_y (v i : ℕ) :
    view len F (setDigit len F.y v i) = { view len F i with y := v % 2 ^ len F.y } := by
  simp only [view, digit_setDigit_self, digit_setDigit_ne len F.y F.b (hby hF),
    digit_setDigit_ne len F.y F.t (hty hF), digit_setDigit_ne len F.y F.u (huy hF),
    digit_setDigit_ne len F.y F.x (hyx hF).symm]

lemma view_set_b (v i : ℕ) :
    view len F (setDigit len F.b v i) = { view len F i with b := v % 2 ^ len F.b } := by
  simp only [view, digit_setDigit_self, digit_setDigit_ne len F.b F.t (hbt hF).symm,
    digit_setDigit_ne len F.b F.u (hbu hF).symm, digit_setDigit_ne len F.b F.y (hby hF).symm,
    digit_setDigit_ne len F.b F.x (hbx hF).symm]

lemma view_set_t (v i : ℕ) :
    view len F (setDigit len F.t v i) = { view len F i with t := v % 2 ^ len F.t } := by
  simp only [view, digit_setDigit_self, digit_setDigit_ne len F.t F.b (hbt hF),
    digit_setDigit_ne len F.t F.u (htu hF).symm, digit_setDigit_ne len F.t F.y (hty hF).symm,
    digit_setDigit_ne len F.t F.x (htx hF).symm]

lemma view_set_u (v i : ℕ) :
    view len F (setDigit len F.u v i) = { view len F i with u := v % 2 ^ len F.u } := by
  simp only [view, digit_setDigit_self, digit_setDigit_ne len F.u F.b (hbu hF),
    digit_setDigit_ne len F.u F.t (htu hF), digit_setDigit_ne len F.u F.y (huy hF).symm,
    digit_setDigit_ne len F.u F.x (hux hF).symm]

/-- **The five fields after an instruction.** -/
theorem view_idx (o : Op) (i : ℕ) : view len F (o.idx p len F i) = o.pure p (view len F i) := by
  cases o with
  | rotY neg o =>
    rw [Op.idx, view_set_y hF, hF.ly, Nat.mod_eq_of_lt (rotv_lt _ _ _ _)]
    rfl
  | rotB neg o =>
    rw [Op.idx, view_set_b hF, hF.lb, Nat.mod_eq_of_lt (rotv_lt _ _ _ _)]
    rfl
  | swapT =>
    rw [Op.idx, view_set_t hF, view_set_b hF, hF.lt, hF.lb,
      Nat.mod_eq_of_lt (digit_lt_t hF i)]
    simp only [view, Nat.mod_eq_of_lt (digit_lt_b hF i)]
    rfl
  | swapU =>
    rw [Op.idx, view_set_u hF, view_set_b hF, hF.lu, hF.lb,
      Nat.mod_eq_of_lt (digit_lt_u hF i)]
    simp only [view, Nat.mod_eq_of_lt (digit_lt_b hF i)]
    rfl

omit hF in
/-- **Every untouched digit is kept.** -/
theorem digit_idx (o : Op) (g : Fin nf) (hg : ¬ touched F g) (i : ℕ) :
    digit len g (o.idx p len F i) = digit len g i := by
  simp only [touched, not_or] at hg
  obtain ⟨hb, ht, hu, hy⟩ := hg
  cases o <;> simp only [Op.idx, digit_setDigit, hb, ht, hu, hy, ite_false]

omit hF in
/-- **The part above all fields is kept.** -/
theorem div_idx (o : Op) (i : ℕ) :
    o.idx p len F i / 2 ^ fieldsLen len = i / 2 ^ fieldsLen len := by
  cases o <;> simp only [Op.idx, setDigit_div_total]

theorem view_runIdx (l : List Op) (i : ℕ) :
    view len F (runIdx p len F l i) = run p l (view len F i) := by
  induction l generalizing i with
  | nil => rfl
  | cons o l ih =>
    simp only [runIdx, run, List.foldl_cons] at ih ⊢
    rw [ih, view_idx hF]

omit hF in
theorem digit_runIdx (l : List Op) (g : Fin nf) (hg : ¬ touched F g) (i : ℕ) :
    digit len g (runIdx p len F l i) = digit len g i := by
  induction l generalizing i with
  | nil => rfl
  | cons o l ih =>
    simp only [runIdx, List.foldl_cons] at ih ⊢
    rw [ih, digit_idx o g hg]

omit hF in
theorem div_runIdx (l : List Op) (i : ℕ) :
    runIdx p len F l i / 2 ^ fieldsLen len = i / 2 ^ fieldsLen len := by
  induction l generalizing i with
  | nil => rfl
  | cons o l ih =>
    simp only [runIdx, List.foldl_cons] at ih ⊢
    rw [ih, div_idx]

/-! ### The ideal map on indices -/

omit hF in
lemma togY_lt (z : ℕ → ℕ) (hz : ∀ c, z c = 0 ∨ z c = 1) {Y : ℕ} (hY : Y < 2 ^ p.wy)
    (hg : ∀ c < p.n, seg p.ρ p.K c Y / 2 + 1 < 2 ^ (p.K - 1)) (hK : 1 ≤ p.K) :
    togY p z Y < 2 ^ p.wy := by
  have hL : 2 ^ p.K = 2 * 2 ^ (p.K - 1) := by
    rw [← pow_succ']; congr 1; omega
  exact asm_lt (Nat.mod_lt _ (by positivity))
    (fun c hc => by rw [hL]; exact tog_lt (hz c) (hg c hc)) (top_lt hY)

theorem view_idealIdx {i : ℕ} (hlt : togY p (fun c => par p c (digit len F.x i))
    (digit len F.y i) < 2 ^ p.wy) : view len F (idealIdx p len F i) = ideal p (view len F i) := by
  rw [idealIdx, view_set_y hF, hF.ly, Nat.mod_eq_of_lt hlt]
  rfl

omit hF in
theorem digit_idealIdx (g : Fin nf) (hg : g ≠ F.y) (i : ℕ) :
    digit len g (idealIdx p len F i) = digit len g i := by
  simp only [idealIdx, digit_setDigit, hg, ite_false]

/-- **The actual and the ideal map agree on every good index.** -/
theorem runIdx_prog_good {i : ℕ} (hgood : GoodIdx p len F i) (hK : 1 ≤ p.K) :
    runIdx p len F prog i = idealIdx p len F i := by
  have hlt : togY p (fun c => par p c (digit len F.x i)) (digit len F.y i) < 2 ^ p.wy :=
    togY_lt _ (fun c => mod_two_cases _) (digit_lt_y hF i)
      (fun c hc => lt_of_le_of_lt (Nat.add_le_add_left Nat.one_le_two_pow _) (hgood c hc).2.2) hK
  have hv := view_runIdx hF prog i
  rw [prog_good (fits_view hF i) hgood hK, ← view_idealIdx hF hlt] at hv
  apply eq_of_digit_eq len
  · intro g
    by_cases ht : touched F g
    · rcases ht with rfl | rfl | rfl | rfl
      · exact congrArg V.b hv
      · exact congrArg V.t hv
      · exact congrArg V.u hv
      · exact congrArg V.y hv
    · simp only [touched, not_or] at ht
      rw [digit_runIdx prog g (by simp only [touched, not_or]; exact ht),
        digit_idealIdx g ht.2.2.2]
  · rw [div_runIdx, idealIdx, setDigit_div_total]

/-! ### Inverses -/

/-- The instruction undoing an instruction. -/
def _root_.IntegerMultBounds.MathlibTM2.Layer.CompactGadget.Op.inv : Op → Op
  | .rotY neg o => .rotY (!neg) o
  | .rotB neg o => .rotB (!neg) o
  | .swapT => .swapT
  | .swapU => .swapU

/-- A rotation reads only fields it does not change. -/
def _root_.IntegerMultBounds.MathlibTM2.Layer.CompactGadget.Op.WF : Op → Prop
  | .rotY _ o => o = .A ∨ o = .Z
  | .rotB _ o => o = .Y ∨ o = .YZ ∨ o = .X
  | .swapT => True
  | .swapU => True

omit hF in
lemma eval_set_y {o : Off} (ho : o = .A ∨ o = .Z) (b t u y y' x : ℕ) :
    o.eval p ⟨b, t, u, y', x⟩ = o.eval p ⟨b, t, u, y, x⟩ := by
  rcases ho with rfl | rfl <;> rfl

omit hF in
lemma eval_set_b {o : Off} (ho : o = .Y ∨ o = .YZ ∨ o = .X) (b b' t u y x : ℕ) :
    o.eval p ⟨b', t, u, y, x⟩ = o.eval p ⟨b, t, u, y, x⟩ := by
  rcases ho with rfl | rfl | rfl <;> rfl

omit hF in
lemma Op.inv_WF {o : Op} (ho : o.WF) : o.inv.WF := by
  cases o <;> exact ho

omit hF in
lemma Op.inv_inv (o : Op) : o.inv.inv = o := by
  cases o <;> simp [Op.inv]

omit hF in
lemma pure_inv_pure {o : Op} (ho : o.WF) {v : V} (hv : Fits p v) :
    o.inv.pure p (o.pure p v) = v := by
  obtain ⟨b, t, u, y, x⟩ := v
  cases o with
  | rotY neg o =>
    simp only [Op.inv, Op.pure]
    rw [eval_set_y ho b t u y, rotv_rotv neg _ hv.y]
  | rotB neg o =>
    simp only [Op.inv, Op.pure]
    rw [eval_set_b ho b, rotv_rotv neg _ hv.b]
  | swapT => rfl
  | swapU => rfl

omit hF in
lemma fits_pure (o : Op) {v : V} (hv : Fits p v) : Fits p (o.pure p v) := by
  obtain ⟨hb, ht, hu, hy⟩ := hv
  cases o with
  | rotY neg o => exact ⟨hb, ht, hu, rotv_lt _ _ _ _⟩
  | rotB neg o => exact ⟨rotv_lt _ _ _ _, ht, hu, hy⟩
  | swapT => exact ⟨ht, hb, hu, hy⟩
  | swapU => exact ⟨hu, ht, hb, hy⟩

omit hF in
/-- An index is determined by its five fields, its untouched digits and its high part. -/
lemma eq_of_view {i j : ℕ} (hv : view len F i = view len F j)
    (hd : ∀ g, ¬ touched F g → digit len g i = digit len g j)
    (hhi : i / 2 ^ fieldsLen len = j / 2 ^ fieldsLen len) : i = j := by
  apply eq_of_digit_eq len _ hhi
  intro g
  by_cases ht : touched F g
  · rcases ht with rfl | rfl | rfl | rfl
    · exact congrArg V.b hv
    · exact congrArg V.t hv
    · exact congrArg V.u hv
    · exact congrArg V.y hv
  · exact hd g ht

/-- **An instruction is undone by its inverse.** -/
theorem inv_idx_idx {o : Op} (ho : o.WF) (i : ℕ) : o.inv.idx p len F (o.idx p len F i) = i :=
  eq_of_view (by rw [view_idx hF, view_idx hF, pure_inv_pure ho (fits_view hF i)])
    (fun g hg => by rw [digit_idx _ g hg, digit_idx _ g hg])
    (by rw [div_idx, div_idx])

omit hF in
/-- Instructions keep every bit at or above the end of the touched fields. -/
theorem idx_div_of_le {q : ℕ} (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q) (o : Op)
    (i : ℕ) : o.idx p len F i / 2 ^ q = i / 2 ^ q := by
  have hb := hq F.b (Or.inl rfl)
  have ht := hq F.t (Or.inr (Or.inl rfl))
  have hu := hq F.u (Or.inr (Or.inr (Or.inl rfl)))
  have hy := hq F.y (Or.inr (Or.inr (Or.inr rfl)))
  cases o <;> simp only [Op.idx, setDigit_div_of_le len _ hb, setDigit_div_of_le len _ ht,
    setDigit_div_of_le len _ hu, setDigit_div_of_le len _ hy]

omit hF in
/-- Instructions keep the rank bound `R 2^q`. -/
theorem idx_lt {q R : ℕ} (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q) (o : Op)
    {i : ℕ} (hi : i < R * 2 ^ q) : o.idx p len F i < R * 2 ^ q := by
  have h := idx_div_of_le (p := p) hq o i
  have hpos : 0 < 2 ^ q := by positivity
  have h1 : i / 2 ^ q < R := (Nat.div_lt_iff_lt_mul hpos).2 hi
  rw [← h] at h1
  exact (Nat.div_lt_iff_lt_mul hpos).1 h1

/-- An instruction as a permutation of the ranks below `R 2^q`. -/
def opPerm {q R : ℕ} (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q) {o : Op} (ho : o.WF) :
    Equiv.Perm (Fin (R * 2 ^ q)) where
  toFun i := ⟨o.idx p len F i, idx_lt hq o i.isLt⟩
  invFun i := ⟨o.inv.idx p len F i, idx_lt hq o.inv i.isLt⟩
  left_inv i := Fin.ext (inv_idx_idx hF ho i)
  right_inv i := Fin.ext (by
    have := inv_idx_idx hF (Op.inv_WF ho) (i : ℕ)
    rwa [Op.inv_inv] at this)

end Digits

end IntegerMultBounds.MathlibTM2.Layer.CompactGadget
