module

public import IntegerMultBounds.MathlibTM2.Node.SwapPass
public import IntegerMultBounds.MathlibTM2.Layer.CompactGadgetIndex

/-!
# Swapping two compact digits of the record index

`swapList_moveRecs_of`: the list interchange `swapList P H G D B` of a record stream moves the
records by any permutation `π` whose cell arithmetic matches it: record `r` and bit `e` sit at
cell `(q, h, g, d, e')` and the moved record at cell `(q, d, g, h, e')`.

`swapIdx_cells`: swapping digits `f₁ < f₂` of equal length `w` of a record index is such a
permutation, with `H = D = 2 ^ w`, the gap `G = 2 ^ (fieldOff f₂ - fieldOff f₁ - w)` between
them, the low part and the record bits `B = 2 ^ (fieldOff f₁) R` below, and the high part
`P = M / 2 ^ (fieldOff f₂ + w)` above.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits

/-- **The list interchange moves records by a matching permutation.** -/
theorem swapList_moveRecs_of {α : Type*} (dflt : α) {P H G D B R M : ℕ}
    (π : Equiv.Perm (Fin M)) (l : List (List α)) (hl : l.length = M)
    (hR : ∀ x ∈ l, x.length = R) (hvol : P * H * G * D * B = M * R)
    (hidx : ∀ (r : Fin M) (e : ℕ), e < R → ∃ q h g d e', q < P ∧ h < H ∧ g < G ∧ d < D ∧
      e' < B ∧ (r : ℕ) * R + e = (((q * H + h) * G + g) * D + d) * B + e' ∧
      (π r : ℕ) * R + e = (((q * D + d) * G + g) * H + h) * B + e') :
    swapList P H G D B dflt l.flatten = (moveRecs π l).flatten := by
  have hmem : ∀ x ∈ moveRecs π l, x.length = R := by
    intro x hx
    simp only [moveRecs, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    apply hR
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact (π.symm j).isLt)]
    exact List.getElem_mem _
  have hlen₀ : l.flatten.length = P * H * G * D * B := by
    rw [length_flatten_uniform _ hR, hl, hvol]
  have hlen₁ : (swapList P H G D B dflt l.flatten).length = M * R := by
    rw [swapList, List.length_map, List.length_range, ← hvol]; ring
  have hlen₂ : (moveRecs π l).flatten.length = M * R := by
    rw [length_flatten_uniform _ hmem, length_moveRecs]
  apply List.ext_getElem?
  intro z
  by_cases hz : z < M * R
  · have hR0 : 0 < R := by
      rcases Nat.eq_zero_or_pos R with h | h
      · rw [h, Nat.mul_zero] at hz; omega
      · exact h
    obtain ⟨q, i, hi, hq, rfl⟩ : ∃ q i, i < R ∧ q < M ∧ z = q * R + i :=
      ⟨z / R, z % R, Nat.mod_lt _ hR0, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]),
        (Nat.div_add_mod' z R).symm⟩
    set r := π.symm ⟨q, hq⟩ with hr
    have hπ : π r = ⟨q, hq⟩ := by simp [r]
    obtain ⟨q₁, h, g, d, e, b1, b2, b3, b4, b5, hs, ht⟩ := hidx r i hi
    rw [hπ] at ht
    have hrl : r.val < l.length := by rw [hl]; exact r.isLt
    have e₁ : (swapList P H G D B dflt l.flatten)[q * R + i]? = l[r.val]?.bind (·[i]?) := by
      rw [show q * R + i = (((q₁ * D + d) * G + g) * H + h) * B + e from ht,
        swapList_getElem? dflt l.flatten hlen₀ b1 b2 b3 b4 b5, ← hs,
        flatten_getElem?_uniform _ hR _ _ hi]
    have e₂ : (moveRecs π l).flatten[q * R + i]? = l[r.val]?.bind (·[i]?) := by
      rw [flatten_getElem?_uniform _ hmem _ _ hi]
      simp only [moveRecs, List.getElem?_ofFn, hq, dite_true, List.getElem?_eq_getElem hrl,
        Option.bind_some]
      rw [List.getD_eq_getElem _ _ hrl]
    rw [e₁, e₂]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ### Swapping two digits -/

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- Swap digits `f₁` and `f₂` of the index `i`. -/
def swapIdx (f₁ f₂ : Fin nf) (i : ℕ) : ℕ :=
  setDigit len f₂ (digit len f₁ i) (setDigit len f₁ (digit len f₂ i) i)

variable {len}

/-- An index from its five parts around two fields `f₁ < f₂` of length `w`. -/
lemma idx_five {f₁ f₂ : Fin nf} (h12 : f₁ < f₂) {w : ℕ} (hw₁ : len f₁ = w) (hw₂ : len f₂ = w)
    (i : ℕ) :
    i = i % 2 ^ fieldOff len f₁ + 2 ^ fieldOff len f₁ * (digit len f₁ i + 2 ^ w *
      (i / 2 ^ (fieldOff len f₁ + w) % 2 ^ (fieldOff len f₂ - fieldOff len f₁ - w) +
        2 ^ (fieldOff len f₂ - fieldOff len f₁ - w) * (digit len f₂ i + 2 ^ w *
          (i / 2 ^ (fieldOff len f₂ + w))))) := by
  have hle := fieldOff_add_le_of_lt len h12
  rw [hw₁] at hle
  obtain ⟨gap, hgap⟩ := Nat.exists_eq_add_of_le hle
  rw [show fieldOff len f₂ - fieldOff len f₁ - w = gap by omega]
  set o := fieldOff len f₁
  have hd₁ : digit len f₁ i = i / 2 ^ o % 2 ^ w := by rw [digit, hw₁]
  have hd₂ : digit len f₂ i = i / 2 ^ (o + w + gap) % 2 ^ w := by rw [digit, hw₂, hgap]
  rw [hd₁, hd₂, hgap]
  have e1 := Nat.mod_add_div i (2 ^ o)
  have e2 := Nat.mod_add_div (i / 2 ^ o) (2 ^ w)
  have e3 := Nat.mod_add_div (i / 2 ^ o / 2 ^ w) (2 ^ gap)
  have e4 := Nat.mod_add_div (i / 2 ^ o / 2 ^ w / 2 ^ gap) (2 ^ w)
  simp only [Nat.div_div_eq_div_mul, ← Nat.pow_add] at e2 e3 e4
  rw [show o + w + gap + w = o + w + gap + w from rfl]
  rw [← e4] at e3
  rw [← e3] at e2
  rw [← e2] at e1
  exact e1.symm

/-- The parts of a digit swap. -/
lemma swapIdx_parts {f₁ f₂ : Fin nf} (h12 : f₁ < f₂) {w : ℕ} (hw₁ : len f₁ = w)
    (hw₂ : len f₂ = w) (i : ℕ) :
    swapIdx len f₁ f₂ i % 2 ^ fieldOff len f₁ = i % 2 ^ fieldOff len f₁ ∧
    digit len f₁ (swapIdx len f₁ f₂ i) = digit len f₂ i ∧
    swapIdx len f₁ f₂ i / 2 ^ (fieldOff len f₁ + w) % 2 ^ (fieldOff len f₂ - fieldOff len f₁ - w) =
      i / 2 ^ (fieldOff len f₁ + w) % 2 ^ (fieldOff len f₂ - fieldOff len f₁ - w) ∧
    digit len f₂ (swapIdx len f₁ f₂ i) = digit len f₁ i ∧
    swapIdx len f₁ f₂ i / 2 ^ (fieldOff len f₂ + w) = i / 2 ^ (fieldOff len f₂ + w) := by
  have hne : f₂ ≠ f₁ := ne_of_gt h12
  have hle := fieldOff_add_le_of_lt len h12
  rw [hw₁] at hle
  have hdl : ∀ g, digit len g i < 2 ^ len g := fun g => Nat.mod_lt _ (by positivity)
  unfold swapIdx
  set Y := setDigit len f₁ (digit len f₂ i) i with hY
  set X := setDigit len f₂ (digit len f₁ i) Y with hX
  have hmod₂ : X % 2 ^ fieldOff len f₂ = Y % 2 ^ fieldOff len f₂ := setDigit_mod len f₂ _ Y
  have hdvd : 2 ^ fieldOff len f₁ ∣ 2 ^ fieldOff len f₂ := Nat.pow_dvd_pow 2 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.mod_mod_of_dvd X hdvd, hmod₂, Nat.mod_mod_of_dvd Y hdvd, hY, setDigit_mod]
  · rw [hX, digit_setDigit_ne len f₂ f₁ hne.symm, hY, digit_setDigit_self,
      Nat.mod_eq_of_lt (by rw [hw₁, ← hw₂]; exact hdl f₂)]
  · have hq : fieldOff len f₁ + w + (fieldOff len f₂ - fieldOff len f₁ - w) = fieldOff len f₂ := by
      omega
    have h1 := window_mod (p := fieldOff len f₁ + w) (w := fieldOff len f₂ - fieldOff len f₁ - w)
      (q := fieldOff len f₂) hq.le X
    have h2 := window_mod (p := fieldOff len f₁ + w) (w := fieldOff len f₂ - fieldOff len f₁ - w)
      (q := fieldOff len f₂) hq.le Y
    unfold window at h1 h2
    rw [← h1, hmod₂, h2, hY, ← hw₁, setDigit_div]
  · rw [digit_setDigit_self, Nat.mod_eq_of_lt (by rw [hw₂, ← hw₁]; exact hdl f₁)]
  · rw [← hw₂, setDigit_div, hw₂, setDigit_div_of_le len f₁ (by omega)]

/-- **The cells of a digit swap.** -/
theorem swapIdx_cells {f₁ f₂ : Fin nf} (h12 : f₁ < f₂) {w : ℕ} (hw₁ : len f₁ = w)
    (hw₂ : len f₂ = w) {Rr q : ℕ} (hq : fieldOff len f₂ + w ≤ q)
    (π : Equiv.Perm (Fin (Rr * 2 ^ q))) (hπ : ∀ r, (π r : ℕ) = swapIdx len f₁ f₂ r) (R : ℕ) :
    ∀ (r : Fin (Rr * 2 ^ q)) (e : ℕ), e < R → ∃ qq h g d e',
      qq < Rr * 2 ^ (q - (fieldOff len f₂ + w)) ∧ h < 2 ^ w ∧
      g < 2 ^ (fieldOff len f₂ - fieldOff len f₁ - w) ∧ d < 2 ^ w ∧
      e' < 2 ^ fieldOff len f₁ * R ∧
      (r : ℕ) * R + e = (((qq * 2 ^ w + h) * 2 ^ (fieldOff len f₂ - fieldOff len f₁ - w) + g) *
        2 ^ w + d) * (2 ^ fieldOff len f₁ * R) + e' ∧
      (π r : ℕ) * R + e = (((qq * 2 ^ w + d) * 2 ^ (fieldOff len f₂ - fieldOff len f₁ - w) + g) *
        2 ^ w + h) * (2 ^ fieldOff len f₁ * R) + e' := by
  intro r e he
  set o₁ := fieldOff len f₁
  set o₂ := fieldOff len f₂
  set gap := o₂ - o₁ - w
  have hdl : ∀ g, digit len g r < 2 ^ len g := fun g => Nat.mod_lt _ (by positivity)
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := swapIdx_parts h12 hw₁ hw₂ (r : ℕ)
  have hfive := idx_five h12 hw₁ hw₂ (r : ℕ)
  have hfive' := idx_five h12 hw₁ hw₂ (swapIdx len f₁ f₂ r)
  rw [hp1, hp2, hp3, hp4, hp5] at hfive'
  have hlow := Nat.mod_lt (r : ℕ) (show 0 < 2 ^ o₁ by positivity)
  have hq' : (2 : ℕ) ^ q = 2 ^ (o₂ + w) * 2 ^ (q - (o₂ + w)) := by
    rw [← Nat.pow_add]; congr 1; omega
  refine ⟨r / 2 ^ (o₂ + w), digit len f₂ r, r / 2 ^ (o₁ + w) % 2 ^ gap, digit len f₁ r,
    (r % 2 ^ o₁) * R + e, ?_, by rw [← hw₂]; exact hdl f₂, Nat.mod_lt _ (by positivity),
    by rw [← hw₁]; exact hdl f₁, ?_, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have h1 : (r : ℕ) < Rr * 2 ^ q := r.isLt
    calc (r : ℕ) < Rr * 2 ^ q := h1
      _ = Rr * 2 ^ (q - (o₂ + w)) * 2 ^ (o₂ + w) := by rw [hq']; ring
  · have : (r % 2 ^ o₁ + 1) * R ≤ 2 ^ o₁ * R := Nat.mul_le_mul_right _ hlow
    nlinarith
  · conv_lhs => rw [hfive]
    ring
  · rw [hπ r]
    conv_lhs => rw [hfive']
    ring

/-- The index map of `swapT` is a digit swap. -/
lemma swapT_idx (p : Layer.CompactGadget.Par) (F : Layer.CompactGadget.Fields nf) (i : ℕ) :
    Layer.CompactGadget.Op.swapT.idx p len F i = swapIdx len F.b F.t i := rfl

/-- The index map of `swapU` is a digit swap. -/
lemma swapU_idx (p : Layer.CompactGadget.Par) (F : Layer.CompactGadget.Fields nf) (i : ℕ) :
    Layer.CompactGadget.Op.swapU.idx p len F i = swapIdx len F.b F.u i := rfl

/-! ### The swap pass -/

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The interchange dimensions of a digit swap of `R`-symbol records. -/
def swapDimsIdx (f₁ f₂ : Fin nf) (w Rr q R : ℕ) : ℕ × ℕ × ℕ :=
  (Rr * 2 ^ (q - (fieldOff len f₂ + w)), 2 ^ (fieldOff len f₂ - fieldOff len f₁ - w),
    2 ^ fieldOff len f₁ * (3 * R))

/-- **The swap pass of two digits.** -/
theorem cxSwap_exec {t₀ T Q K : ℕ} {U F : Type} (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp) (hstr : ∀ j, ι j ≠ str) (htmp : ∀ j, ι j ≠ tmp)
    {f₁ f₂ : Fin nf} (h12 : f₁ < f₂) {w : ℕ} (hw₁ : len f₁ = w) (hw₂ : len f₂ = w)
    {Rr q : ℕ} (hRr : 0 < Rr) (hq : fieldOff len f₂ + w ≤ q)
    (π : Equiv.Perm (Fin (Rr * 2 ^ q))) (hπ : ∀ r, (π r : ℕ) = swapIdx len f₁ f₂ r)
    {B : ℕ} (hB : 0 < B) (l : List (List (Fin (prime + K + 4)))) (hl : l.length = Rr * 2 ^ q)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values
      (swapDimsIdx (len := len) f₁ f₂ w Rr q B).1 (swapDimsIdx (len := len) f₁ f₂ w Rr q B).2.1
      (swapDimsIdx (len := len) f₁ f₂ w Rr q B).2.2 w w k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ y, S.L y = [])
    (hR : S.R str = l.flatten) (htmp0 : S.R tmp = []) (hpay0 : S.R (ι (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ 3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (Rr * 2 ^ q * B : ℕ) *
          ((max 1 w : ℕ) : ℝ) ^ Parameters.tau +
        (6 * ∑ j, (S.R (ι j)).length + 34 * (Rr * 2 ^ q * B) + 2 * T + 6 * swapT t₀ + 23 : ℕ) ∧
      Exec body (swapPass hd pay hi hQ ι hι hT str tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs π l).flatten }) := by
  set P := (swapDimsIdx (len := len) f₁ f₂ w Rr q B).1
  set G := (swapDimsIdx (len := len) f₁ f₂ w Rr q B).2.1
  set B' := (swapDimsIdx (len := len) f₁ f₂ w Rr q B).2.2
  have hle := fieldOff_add_le_of_lt len h12
  rw [hw₁] at hle
  have hvol : P * 2 ^ w * G * 2 ^ w * B' = Rr * 2 ^ q * (3 * B) := by
    simp only [P, G, B', swapDimsIdx]
    have e : (2 : ℕ) ^ q = 2 ^ fieldOff len f₁ * 2 ^ w *
        2 ^ (fieldOff len f₂ - fieldOff len f₁ - w) * 2 ^ w * 2 ^ (q - (fieldOff len f₂ + w)) := by
      simp only [← Nat.pow_add]; congr 1; omega
    rw [e]; ring
  have hPpos : 0 < P := Nat.mul_pos hRr (by positivity)
  have hGpos : 0 < G := by simp only [G, swapDimsIdx]; positivity
  have hBpos : 0 < B' := Nat.mul_pos (by positivity) (by omega)
  have hmem : ∀ x ∈ moveRecs π l, x.length = B := fun x hx => hlB x (mem_moveRecs π hl hx)
  have hmap : (moveRecs π l).map toBits = moveRecs π (l.map toBits) := by
    simp only [moveRecs, List.map_ofFn]
    congr 1
    funext j
    simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[π.symm j]? <;> rfl
  have hswap : swapList P (2 ^ w) G (2 ^ w) B' blank (toBits l.flatten) =
      toBits (moveRecs π l).flatten := by
    rw [toBits_flatten, toBits_flatten, hmap]
    apply swapList_moveRecs_of blank π (l.map toBits) (by rw [List.length_map, hl])
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        rw [length_toBits, hlB y hy]) hvol
    exact swapIdx_cells h12 hw₁ hw₂ hq π hπ (3 * B)
  have hwlen : l.flatten.length = Rr * 2 ^ q * B := by rw [length_flatten_uniform _ hlB, hl]
  have hw'len : (moveRecs π l).flatten.length = Rr * 2 ^ q * B := by
    rw [length_flatten_uniform _ hmem, length_moveRecs]
  obtain ⟨v', m, hu, hm, he⟩ := swapPass_exec_of body hd pay hi hQ ι hι hT str tmp hst hstr htmp
    P G B' w (Rr * 2 ^ q * B) hPpos hGpos hBpos l.flatten (moveRecs π l).flatten hwlen hw'len
    (by rw [hvol]; ring) hswap
    (fun s hs' => by
      obtain ⟨x, hx, hsx⟩ := List.mem_flatten.1 hs'
      exact h8 x (mem_moveRecs π hl hx) s hsx) hs hv hc v S hL hR htmp0 hpay0 hpriv hhdr hother
  refine ⟨v', m, hu, ?_, he⟩
  have hC := (Classical.choose_spec BinaryInterchangeRun.uniform_bound).2
    P G B' w w hs hPpos hGpos hBpos (Nat.le_succ w) (Nat.le_succ w) hv hc
  rw [max_self, BinaryAdjacentWidthInterchange.volume, hvol] at hC
  have hvol' : ((Rr * 2 ^ q * (3 * B) : ℕ) : ℝ) = 3 * ((Rr * 2 ^ q * B : ℕ) : ℝ) := by
    push_cast; ring
  rw [hvol'] at hC
  exact cast_time_bound (hm.trans (le_of_eq (by ring))) hC

end IntegerMultBounds.MathlibTM2.Node
