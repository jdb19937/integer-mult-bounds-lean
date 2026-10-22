module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveXor

/-!
# The selective schedule on a fixed physical record-index layout

Least significant first, the fields are borrowed b, target y (including complete
prefix/suffix spectators), borrowed t, borrowed u, and an arbitrary-width spectator
word. The layout is unchanged throughout all rotations and interchanges.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (X : ℕ)

def selectiveLen : Fin 5 → ℕ := ![p.wc, p.wy, p.wc, p.wc, X]

def selectiveView (i : ℕ) : V :=
  ⟨digit (selectiveLen p X) 0 i, digit (selectiveLen p X) 2 i,
    digit (selectiveLen p X) 3 i, digit (selectiveLen p X) 1 i,
    digit (selectiveLen p X) 4 i⟩

/-- Each instruction changes precisely its actual physical field(s). -/
def selectiveIdx (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ) : Op → ℕ → ℕ
  | .rotY neg o, i => setDigit (selectiveLen p X) 1
      ((selectiveOp p active read (.rotY neg o) (selectiveView p X i)).y) i
  | .rotB neg o, i => setDigit (selectiveLen p X) 0
      ((selectiveOp p active read (.rotB neg o) (selectiveView p X i)).b) i
  | .swapT, i => setDigit (selectiveLen p X) 2 (digit (selectiveLen p X) 0 i)
      (setDigit (selectiveLen p X) 0 (digit (selectiveLen p X) 2 i) i)
  | .swapU, i => setDigit (selectiveLen p X) 3 (digit (selectiveLen p X) 0 i)
      (setDigit (selectiveLen p X) 0 (digit (selectiveLen p X) 3 i) i)

def selectiveRunIdx (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ)
    (os : List Op) (i : ℕ) : ℕ := os.foldl (fun i op => selectiveIdx p X active read op i) i

private theorem view_set_y (a i : ℕ) :
    selectiveView p X (setDigit (selectiveLen p X) 1 a i) =
      { selectiveView p X i with y := a % 2 ^ p.wy } := by
  simp [selectiveView, digit_setDigit, selectiveLen]

private theorem view_set_b (a i : ℕ) :
    selectiveView p X (setDigit (selectiveLen p X) 0 a i) =
      { selectiveView p X i with b := a % 2 ^ p.wc } := by
  simp [selectiveView, digit_setDigit, selectiveLen]

private theorem view_set_t (a i : ℕ) :
    selectiveView p X (setDigit (selectiveLen p X) 2 a i) =
      { selectiveView p X i with t := a % 2 ^ p.wc } := by
  simp [selectiveView, digit_setDigit, selectiveLen]

private theorem view_set_u (a i : ℕ) :
    selectiveView p X (setDigit (selectiveLen p X) 3 a i) =
      { selectiveView p X i with u := a % 2 ^ p.wc } := by
  simp [selectiveView, digit_setDigit, selectiveLen]

/-- The actual field updates have exactly the checked masked instruction semantics. -/
theorem selectiveView_idx (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ)
    (op : Op) (i : ℕ) :
    selectiveView p X (selectiveIdx p X active read op i) =
      selectiveOp p active read op (selectiveView p X i) := by
  cases op with
  | rotY neg o =>
    rw [selectiveIdx, view_set_y]
    simp [selectiveOp, maskedOp, Nat.mod_eq_of_lt (rotv_lt _ _ _ _)]
  | rotB neg o =>
    rw [selectiveIdx, view_set_b]
    cases o <;> simp [selectiveOp, maskedOp, Nat.mod_eq_of_lt (rotv_lt _ _ _ _)]
  | swapT =>
    rw [selectiveIdx, view_set_t, view_set_b]
    have ht : digit (selectiveLen p X) 2 i < 2 ^ p.wc := Nat.mod_lt _ (by positivity)
    have hb : digit (selectiveLen p X) 0 i < 2 ^ p.wc := Nat.mod_lt _ (by positivity)
    simp [selectiveOp, maskedOp, selectiveView, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hb]
  | swapU =>
    rw [selectiveIdx, view_set_u, view_set_b]
    have hu : digit (selectiveLen p X) 3 i < 2 ^ p.wc := Nat.mod_lt _ (by positivity)
    have hb : digit (selectiveLen p X) 0 i < 2 ^ p.wc := Nat.mod_lt _ (by positivity)
    simp [selectiveOp, maskedOp, selectiveView, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hb]

theorem selectiveView_runIdx (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ)
    (os : List Op) (i : ℕ) :
    selectiveView p X (selectiveRunIdx p X active read os i) =
      selectiveRun p active read os (selectiveView p X i) := by
  induction os generalizing i with
  | nil => rfl
  | cons op os ih =>
    change selectiveView p X (selectiveRunIdx p X active read os
      (selectiveIdx p X active read op i)) = _
    rw [ih, selectiveView_idx]
    rfl

/-- Bits above the complete layout are spectators at every intermediate step. -/
theorem selectiveIdx_div (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ)
    (op : Op) (i : ℕ) :
    selectiveIdx p X active read op i / 2 ^ fieldsLen (selectiveLen p X) =
      i / 2 ^ fieldsLen (selectiveLen p X) := by
  cases op <;> simp [selectiveIdx, setDigit_div_total]

theorem selectiveRunIdx_div (active : Fin p.n → Bool) (read : ℕ → ℕ → ℕ → ℕ)
    (os : List Op) (i : ℕ) :
    selectiveRunIdx p X active read os i / 2 ^ fieldsLen (selectiveLen p X) =
      i / 2 ^ fieldsLen (selectiveLen p X) := by
  induction os generalizing i with
  | nil => rfl
  | cons op os ih =>
    change selectiveRunIdx p X active read os (selectiveIdx p X active read op i) / _ = _
    rw [ih, selectiveIdx_div]

theorem selectiveView_fits (i : ℕ) : Fits p (selectiveView p X i) :=
  ⟨Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity),
    Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity)⟩

/-- The sparse requested XOR fits entirely inside the actual target field. -/
theorem targetWord_lt (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (y x : ℕ) :
    targetWord p active s y x < 2 ^ p.wy := by
  unfold targetWord
  apply lt_of_lt_of_le (placeVal_lt (posS_mono hK) _ p.n)
  exact Nat.pow_le_pow_right (by norm_num) (by unfold posS Par.wy; omega)

/-- The complete actual-rank schedule changes only the requested physical target
bits, retaining arbitrary initial borrowed fields and every spectator. -/
theorem selectiveRunIdx_good (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hs : ∀ c, (s c).Allowed active) (i : ℕ)
    (hgood : Good p (selectiveView p X i)) (hG : 0 < p.G) (hK : 1 ≤ p.K) :
    selectiveRunIdx p X active (slotRead p active (slotSourcesRead active s)) prog i =
      setDigit (selectiveLen p X) 1
        ((selectiveView p X i).y ^^^ targetWord p active s
          (selectiveView p X i).y (selectiveView p X i).x) i := by
  have hv := selectiveView_fits p X i
  have hlt := Nat.xor_lt_two_pow hv.y (targetWord_lt p X (by omega) active s (selectiveView p X i).y (selectiveView p X i).x)
  have hview := selectiveView_runIdx p X active
    (slotRead p active (slotSourcesRead active s)) prog i
  rw [selectiveRun_physical_xor active s hs hv hgood hG hK] at hview
  have heq : selectiveView p X
      (selectiveRunIdx p X active (slotRead p active (slotSourcesRead active s)) prog i) =
      selectiveView p X (setDigit (selectiveLen p X) 1
        ((selectiveView p X i).y ^^^ targetWord p active s
          (selectiveView p X i).y (selectiveView p X i).x) i) := by
    rw [view_set_y, Nat.mod_eq_of_lt hlt]
    exact hview
  apply eq_of_digit_eq (len := selectiveLen p X)
  · intro f
    fin_cases f
    · convert congrArg V.b heq using 1 <;> rfl
    · convert congrArg V.y heq using 1 <;> rfl
    · convert congrArg V.t heq using 1 <;> rfl
    · convert congrArg V.u heq using 1 <;> rfl
    · convert congrArg V.x heq using 1 <;> rfl
  · rw [selectiveRunIdx_div, setDigit_div_total]

end IntegerMultBounds.MathlibTM2.Routing
