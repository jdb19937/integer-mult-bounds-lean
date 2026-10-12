module

public import IntegerMultBounds.Resampling.AxisRounds
public import IntegerMultBounds.Resampling.FlatTensor

/-! The tensor driver's field moves on flat bit arrays. An interchange with
an outer prefix `Q · P` acts on each of the `Q` outer blocks
(`swapList_mul`); moving the outermost field inward past the others by
adjacent interchanges is one block transpose (`rotIn_eq_tr2`); and block
transposes and blockwise maps of entries are the same operations on their
bits (`flatten_trL`, `flatten_mapBlocks`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.ScriptSem

open AxisRounds FlatTensor

/-- Bits of a uniform-width list at an entry and offset. -/
theorem getD_flatten_uniform (B : ℕ) : ∀ (es : List (List Bool)), (∀ e ∈ es, e.length = B) →
    ∀ (i b : ℕ), i < es.length → b < B → es.flatten.getD (i * B + b) false = (es.getD i []).getD b false
  | [], _, i, _, hi, _ => by simp at hi
  | e :: es, h, i, b, hi, hb => by
    have he := h e (by simp)
    rw [List.flatten_cons]
    cases i with
    | zero =>
      simp only [zero_mul, zero_add, List.getD_cons_zero]
      rw [List.getD_append _ _ _ _ (by omega)]
    | succ i =>
      rw [List.getD_append_right _ _ _ _ (by rw [he]; nlinarith), he,
        show (i + 1) * B + b - B = i * B + b by rw [Nat.succ_mul]; omega,
        getD_flatten_uniform B es (fun x hx => h x (by simp [hx])) i b (by simp at hi; omega) hb]
      simp

/-- A position in `A · B` rows of width `B` is a row and an offset. -/
theorem decomp2 {z A B : ℕ} (h : z < A * B) : ∃ a b, a < A ∧ b < B ∧ z = a * B + b := by
  have hB : 0 < B := by rcases Nat.eq_zero_or_pos B with hB | hB <;> simp_all
  refine ⟨z / B, z % B, ?_, Nat.mod_lt _ hB, (Nat.div_add_mod' z B).symm⟩
  rw [Nat.div_lt_iff_lt_mul hB]; exact h

theorem length_swapList' (P H G D B : ℕ) (xs : List Bool) :
    (Schoenhage.SwapPrim.swapList P H G D B xs).length = P * D * G * H * B := length_swapList P H G D B xs

/-- An interchange with outer prefix `Q · P` acts on each of the `Q` outer blocks. -/
theorem swapList_mul (Q P H D B : ℕ) (xs : List Bool) (hl : xs.length = Q * (P * H * D * B))
    (hpos : 0 < P * H * D * B) :
    Schoenhage.SwapPrim.swapList (Q * P) H 1 D B xs = mapBlocks (P * H * D * B) (Schoenhage.SwapPrim.swapList P H 1 D B) xs := by
  apply ext_getD' false
  · rw [length_swapList', length_mapBlocks _ (P * D * 1 * H * B) _ _ (fun b _ => length_swapList' _ _ _ _ _ _), hl,
      Nat.mul_div_cancel _ hpos]; ring
  · intro z hz
    rw [length_swapList'] at hz
    obtain ⟨q, z1, hq, hz1, rfl⟩ := decomp2 (show z < Q * (P * D * H * B) by nlinarith)
    obtain ⟨p, z2, hp, hz2, rfl⟩ := decomp2 (show z1 < P * (D * H * B) by nlinarith)
    obtain ⟨d, z3, hd, hz3, rfl⟩ := decomp2 (show z2 < D * (H * B) by nlinarith)
    obtain ⟨h, b, hh, hb, rfl⟩ := decomp2 hz3
    have e1 : q * (P * D * H * B) + (p * (D * H * B) + (d * (H * B) + (h * B + b))) =
        ((((q * P + p) * D + d) * 1 + 0) * H + h) * B + b := by ring
    have hqp : q * P + p < Q * P := by nlinarith
    rw [e1, getD_swapList (Q * P) H 1 D B xs hqp hh (by omega) hd hb]
    have e2 : ((((q * P + p) * D + d) * 1 + 0) * H + h) * B + b =
        q * (P * D * 1 * H * B) + ((((p * D + d) * 1 + 0) * H + h) * B + b) := by ring
    rw [e2, getD_mapBlocks (P * H * D * B) (P * D * 1 * H * B) Q _ xs hpos hl
      (fun _ _ => length_swapList' _ _ _ _ _ _) hq (by nlinarith),
      getD_swapList P H 1 D B _ hp hh (by omega) hd hb,
      getD_block _ _ _ (by
        have h1 : p * H + h < P * H := by nlinarith
        have h2 : (p * H + h) * D + d < P * H * D := by nlinarith
        have h3 : ((p * H + h) * D + d) * B + b < P * H * D * B := by nlinarith
        simpa using h3)]
    congr 1; ring

/-- Move the field of `n` entries, just inside an outer prefix of `Q`, past the fields `gs`
(outer to inner) by adjacent interchanges of blocks of `B` bits. -/
def rotIn (n : ℕ) : ℕ → List ℕ → ℕ → List Bool → List Bool
  | _, [], _, xs => xs
  | Q, g :: gs, B, xs => rotIn n (Q * g) gs B (Schoenhage.SwapPrim.swapList Q n 1 g (B * gs.prod) xs)

theorem length_rotIn (n : ℕ) : ∀ (Q : ℕ) (gs : List ℕ) (B : ℕ) (xs : List Bool), xs.length = Q * n * gs.prod * B →
    (rotIn n Q gs B xs).length = Q * n * gs.prod * B
  | _, [], _, _, h => h
  | Q, g :: gs, B, xs, h => by
    rw [rotIn, length_rotIn n (Q * g) gs B _ (by rw [length_swapList']; ring)]; simp only [List.prod_cons]; ring

theorem rotIn_getD (n : ℕ) : ∀ (Q : ℕ) (gs : List ℕ) (B : ℕ) (xs : List Bool) {q j i b : ℕ},
    q < Q → j < gs.prod → i < n → b < B →
    (rotIn n Q gs B xs).getD (q * (gs.prod * n * B) + (j * n + i) * B + b) false =
      xs.getD (q * (n * gs.prod * B) + (i * gs.prod + j) * B + b) false
  | Q, [], B, xs, q, j, i, b, hq, hj, hi, hb => by
    simp only [List.prod_nil] at hj ⊢
    have : j = 0 := by omega
    subst this; simp [rotIn]
  | Q, g :: gs, B, xs, q, j, i, b, hq, hj, hi, hb => by
    simp only [List.prod_cons] at hj ⊢
    set R' := gs.prod
    have hR' : 0 < R' := by rcases Nat.eq_zero_or_pos R' with h | h <;> simp_all
    have hg : 0 < g := by rcases Nat.eq_zero_or_pos g with h | h <;> simp_all
    obtain ⟨j1, j2, hj1, hj2, rfl⟩ := decomp2 (show j < g * R' by exact hj)
    have e1 : q * (g * R' * n * B) + ((j1 * R' + j2) * n + i) * B + b =
        (q * g + j1) * (R' * n * B) + (j2 * n + i) * B + b := by ring
    rw [rotIn, e1, rotIn_getD n (Q * g) gs B _ (by nlinarith) hj2 hi hb]
    have e2 : (q * g + j1) * (n * R' * B) + (i * R' + j2) * B + b =
        ((((q * g + j1) * 1 + 0) * n + i) * (B * R') + (j2 * B + b)) := by ring
    have hjb : j2 * B + b < B * R' := by nlinarith
    rw [e2, getD_swapList Q n 1 g (B * R') xs hq hi (by omega) hj1 hjb]
    congr 1; ring

/-- Move the innermost field of `n` entries outward past the fields `gs` (inner to outer), just inside an
outer prefix of `Q`, by adjacent interchanges of blocks of `B` bits. -/
def rotOut (n : ℕ) : ℕ → List ℕ → ℕ → List Bool → List Bool
  | _, [], _, xs => xs
  | Q, g :: gs, B, xs => rotOut n Q gs (g * B) (Schoenhage.SwapPrim.swapList (Q * gs.prod) g 1 n B xs)

theorem rotOut_getD (n : ℕ) : ∀ (Q : ℕ) (gs : List ℕ) (B : ℕ) (xs : List Bool) {q j i b : ℕ},
    q < Q → j < gs.prod → i < n → b < B →
    (rotOut n Q gs B xs).getD (q * (n * gs.prod * B) + (i * gs.prod + j) * B + b) false =
      xs.getD (q * (gs.prod * n * B) + (j * n + i) * B + b) false
  | Q, [], B, xs, q, j, i, b, hq, hj, hi, hb => by
    simp only [List.prod_nil] at hj ⊢
    have : j = 0 := by omega
    subst this; simp [rotOut]
  | Q, g :: gs, B, xs, q, j, i, b, hq, hj, hi, hb => by
    simp only [List.prod_cons] at hj ⊢
    set R' := gs.prod
    have hR' : 0 < R' := by rcases Nat.eq_zero_or_pos R' with h | h <;> simp_all
    have hg : 0 < g := by rcases Nat.eq_zero_or_pos g with h | h <;> simp_all
    obtain ⟨j', jg, hj', hjg, rfl⟩ := decomp2 (show j < R' * g by rw [mul_comm]; exact hj)
    have e1 : q * (n * (g * R') * B) + (i * (g * R') + (j' * g + jg)) * B + b =
        q * (n * R' * (g * B)) + (i * R' + j') * (g * B) + (jg * B + b) := by ring
    have hjb : jg * B + b < g * B := by nlinarith
    rw [rotOut, e1, rotOut_getD n Q gs (g * B) _ hq hj' hi hjb]
    have e2 : q * (R' * n * (g * B)) + (j' * n + i) * (g * B) + (jg * B + b) =
        ((((q * R' + j') * n + i) * 1 + 0) * g + jg) * B + b := by ring
    have hqj : q * R' + j' < Q * R' := by nlinarith
    rw [e2, getD_swapList (Q * R') g 1 n B xs hqj hjg (by omega) hi hb]
    congr 1; ring

end IntegerMultBounds.Resampling.ScriptSem
