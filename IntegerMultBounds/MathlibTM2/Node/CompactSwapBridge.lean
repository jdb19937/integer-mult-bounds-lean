module

public import IntegerMultBounds.MathlibTM2.Node.SwapPass
public import IntegerMultBounds.MathlibTM2.Node.RotGen

/-!
# The chunk swap of the packed rectangle as a field exchange

Two index models describe the same stream of records. The packed rectangle
(`Layer/PackedXor.lean`, `Node/SwapPass.lean`) ranks the addresses
`[N₀] × [2^L] × [N₁] × [2^L] × [N₂] × [2^L] × [N₃]` lexicographically with `N₃` least
significant; the instruction `swap a b` exchanges the chunk slots `a` and `b` of the triple, and
`rankPerm` is its map of ranks. The compact layout (`Layer/CompactXor.lean`) cuts an index into
fields of lengths `len`; `swapF len f g` exchanges the digits of the fields `f` and `g`.

When the rectangle has `N₀ = R · 2^n₀`, `N₁ = 2^n₁`, `N₂ = 2^n₂`, `N₃ = 2^n₃` and the three
chunk fields `hi`, `mid`, `lo` of the compact layout sit at the bit offsets of the chunk slots
`0`, `1`, `2`, the two maps agree pointwise (`rankPerm_swap_val`): the chunk field of a rank is
the chunk value (`dig_rank`), and both the rank of the swapped address and `swapF` of the rank
satisfy the same additive identity (`swapF_add`). Hence the two permutations move a record stream
the same way (`moveRecs_rankPerm_swap`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Layer.PackedXor IntegerMultBounds.MathlibTM2.Layer.CompactXor
  IntegerMultBounds.MathlibTM2 IntegerMultBounds

/-! ### Additive identities of field replacement -/

section FieldArith

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- Replacing a field adds the new value and removes the old one. -/
lemma setDig_add (f : Fin nf) (i v : ℕ) :
    setDig len f i v + 2 ^ foff len f * dig len f i = i + 2 ^ foff len f * v := by
  unfold setDig dig
  rw [pow_add, ← Nat.div_div_eq_div_mul, mul_add]
  have h1 := Nat.mod_add_div i (2 ^ foff len f)
  have h2 : 2 ^ foff len f * (i / 2 ^ foff len f % 2 ^ len f) +
      2 ^ foff len f * (2 ^ len f * (i / 2 ^ foff len f / 2 ^ len f)) =
      2 ^ foff len f * (i / 2 ^ foff len f) := by
    rw [← mul_add, Nat.mod_add_div]
  omega

/-- Exchanging two fields trades their values. -/
lemma swapF_add {f g : Fin nf} (hfg : f ≠ g) (hlen : len f = len g) (i : ℕ) :
    swapF len f g i + 2 ^ foff len f * dig len f i + 2 ^ foff len g * dig len g i =
      i + 2 ^ foff len g * dig len f i + 2 ^ foff len f * dig len g i := by
  have h1 := setDig_add len f (setDig len g i (dig len f i)) (dig len g i)
  rw [dig_setDig_ne len hfg _ (by rw [← hlen]; exact dig_lt len f i)] at h1
  have h2 := setDig_add len g i (dig len f i)
  unfold swapF
  omega

/-- The field `f` of an index split at that field. -/
lemma dig_of_split (f : Fin nf) {low v : ℕ} (X : ℕ) (hlow : low < 2 ^ foff len f)
    (hv : v < 2 ^ len f) :
    dig len f (low + 2 ^ foff len f * (v + 2 ^ len f * X)) = v := by
  unfold dig
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-- Two bounded digits pack below the summed width. -/
lemma add_mul_lt_pow_add {x y a b : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ b) :
    x + 2 ^ a * y < 2 ^ (a + b) := by
  rw [pow_add]
  calc x + 2 ^ a * y < 2 ^ a * (y + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_left (2 ^ a) hy

end FieldArith

/-! ### The chunk fields of a rank -/

section Bridge

variable {nf : ℕ} (len : Fin nf → ℕ) (lo mid hi : Fin nf) (n₀ n₁ n₂ n₃ L' R : ℕ)

/-- The chunk fields `hi`, `mid`, `lo` of the rank of an address hold the chunk slots `0`, `1`,
`2`. -/
lemma dig_rank (hlo : len lo = L') (hmid : len mid = L') (hhi : len hi = L')
    (hflo : foff len lo = n₃) (hfmid : foff len mid = n₃ + L' + n₂)
    (hfhi : foff len hi = n₃ + L' + n₂ + L' + n₁)
    (p : Addr (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L') :
    dig len hi (rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' p) = p.2 0 ∧
    dig len mid (rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' p) = p.2 1 ∧
    dig len lo (rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' p) = p.2 2 := by
  obtain ⟨⟨s₀, s₁, s₂, s₃⟩, c⟩ := p
  have c0 := (c 0).isLt
  have c1 := (c 1).isLt
  have c2 := (c 2).isLt
  have hs₁ := s₁.isLt
  have hs₂ := s₂.isLt
  have hs₃ := s₃.isLt
  refine ⟨?_, ?_, ?_⟩
  · have e : rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' ((s₀, s₁, s₂, s₃), c) =
        (s₃ + 2 ^ n₃ * (c 2 + 2 ^ L' * (s₂ + 2 ^ n₂ * (c 1 + 2 ^ L' * s₁)))) +
          2 ^ foff len hi * (c 0 + 2 ^ len hi * s₀) := by
      rw [hfhi, hhi]; simp only [rank]; ring
    rw [e]
    exact dig_of_split len hi _
      (by
        rw [hfhi, show n₃ + L' + n₂ + L' + n₁ = n₃ + (L' + (n₂ + (L' + n₁))) by ring]
        exact add_mul_lt_pow_add hs₃ (add_mul_lt_pow_add c2
          (add_mul_lt_pow_add hs₂ (add_mul_lt_pow_add c1 hs₁))))
      (by rw [hhi]; exact c0)
  · have e : rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' ((s₀, s₁, s₂, s₃), c) =
        (s₃ + 2 ^ n₃ * (c 2 + 2 ^ L' * s₂)) +
          2 ^ foff len mid * (c 1 + 2 ^ len mid * (s₁ + 2 ^ n₁ * (c 0 + 2 ^ L' * s₀))) := by
      rw [hfmid, hmid]; simp only [rank]; ring
    rw [e]
    exact dig_of_split len mid _
      (by
        rw [hfmid, show n₃ + L' + n₂ = n₃ + (L' + n₂) by ring]
        exact add_mul_lt_pow_add hs₃ (add_mul_lt_pow_add c2 hs₂))
      (by rw [hmid]; exact c1)
  · have e : rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' ((s₀, s₁, s₂, s₃), c) =
        s₃ + 2 ^ foff len lo *
          (c 2 + 2 ^ len lo * (s₂ + 2 ^ n₂ * (c 1 + 2 ^ L' * (s₁ + 2 ^ n₁ * (c 0 + 2 ^ L' * s₀))))) := by
      rw [hflo, hlo]; rfl
    rw [e]
    exact dig_of_split len lo _ (by rw [hflo]; exact hs₃) (by rw [hlo]; exact c2)

/-- The rank map of `swap a b` is the exchange of the chunk fields of the slots `a` and `b`. -/
theorem rankPerm_swap_val (hlo : len lo = L') (hmid : len mid = L') (hhi : len hi = L')
    (hflo : foff len lo = n₃) (hfmid : foff len mid = n₃ + L' + n₂)
    (hfhi : foff len hi = n₃ + L' + n₂ + L' + n₁) {a b : Fin 3}
    (hne : ![hi, mid, lo] a ≠ ![hi, mid, lo] b) (K ρ n : ℕ)
    (j : Fin (rectSize (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L')) :
    (rankPerm (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' K ρ n [.swap a b] j : ℕ) =
      swapF len (![hi, mid, lo] a) (![hi, mid, lo] b) j := by
  obtain ⟨p, rfl⟩ := (rankEquiv (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L').surjective j
  obtain ⟨hd0, hd1, hd2⟩ :=
    dig_rank len lo mid hi n₀ n₁ n₂ n₃ L' R hlo hmid hhi hflo hfmid hfhi p
  have hlen : ∀ k : Fin 3, len (![hi, mid, lo] k) = L' := by
    intro k; fin_cases k <;> simp [hhi, hmid, hlo]
  have key := swapF_add len hne (by rw [hlen, hlen])
    (rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' p)
  rw [rankPerm_swap, rankEquiv_val, rankEquiv_val]
  obtain ⟨⟨s₀, s₁, s₂, s₃⟩, c⟩ := p
  dsimp only at hd0 hd1 hd2 key ⊢
  have hr : ∀ c' : Tri L', rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' ((s₀, s₁, s₂, s₃), c') =
      (s₃ + 2 ^ (n₃ + L') * s₂ + 2 ^ (n₃ + L' + n₂ + L') * s₁ +
        2 ^ (n₃ + L' + n₂ + L' + n₁ + L') * s₀) +
        2 ^ (n₃ + L' + n₂ + L' + n₁) * c' 0 + 2 ^ (n₃ + L' + n₂) * c' 1 + 2 ^ n₃ * c' 2 := by
    intro c'; simp only [rank]; ring
  have hrc := hr c
  generalize rank (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' ((s₀, s₁, s₂, s₃), c) = r
    at hd0 hd1 hd2 key hrc ⊢
  rw [hr]
  fin_cases a <;> fin_cases b <;>
    simp [Equiv.swap_apply_of_ne_of_ne, hd0, hd1, hd2, hflo, hfmid, hfhi] at hne key ⊢ <;>
    omega

end Bridge

/-! ### Record streams -/

section Streams

/-- Two permutations of the record positions with the same values move a stream the same way. -/
theorem moveRecs_congr {α : Type*} {M M' : ℕ} (π : Equiv.Perm (Fin M)) (π' : Equiv.Perm (Fin M'))
    (hM : M = M') (h : ∀ (x : ℕ) (hx : x < M) (hx' : x < M'), (π ⟨x, hx⟩ : ℕ) = π' ⟨x, hx'⟩)
    (l : List (List α)) : moveRecs π l = moveRecs π' l := by
  subst hM
  have hπ : π = π' := Equiv.ext fun x => Fin.ext (h x x.isLt x.isLt)
  rw [hπ]

/-- The rectangle has `R · 2^S` records when `S` is the total width of its index. -/
lemma rectSize_eq_mul_pow (n₀ n₁ n₂ n₃ L' R : ℕ) :
    rectSize (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' =
      R * 2 ^ (n₃ + L' + n₂ + L' + n₁ + L' + n₀) := by
  simp only [rectSize]; ring

/-- **The chunk swap as a field exchange.** The instruction `swap a b` of the packed rectangle
`[R · 2^n₀] × [2^L'] × [2^n₁] × [2^L'] × [2^n₂] × [2^L'] × [2^n₃]` moves a record stream as the
compact exchange of the chunk fields `![hi, mid, lo] a` and `![hi, mid, lo] b`. -/
theorem moveRecs_rankPerm_swap {α : Type*} {nf : ℕ} (len : Fin nf → ℕ) (lo mid hi : Fin nf)
    (n₀ n₁ n₂ n₃ L' R S : ℕ) (hlo : len lo = L') (hmid : len mid = L') (hhi : len hi = L')
    (hflo : foff len lo = n₃) (hfmid : foff len mid = n₃ + L' + n₂)
    (hfhi : foff len hi = n₃ + L' + n₂ + L' + n₁) (hS : S = n₃ + L' + n₂ + L' + n₁ + L' + n₀)
    {a b : Fin 3} (hWF : CInstr.WF len S (.swap (![hi, mid, lo] a) (![hi, mid, lo] b)))
    (l : List (List α)) (K ρ n : ℕ) :
    moveRecs (rankPerm (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L' K ρ n [.swap a b]) l =
      moveRecs (Layer.CompactXor.instrPerm len (R := R) (S := S) hWF) l := by
  apply moveRecs_congr _ _ (by rw [rectSize_eq_mul_pow, hS])
  intro x hx hx'
  rw [rankPerm_swap_val len lo mid hi n₀ n₁ n₂ n₃ L' R hlo hmid hhi hflo hfmid hfhi hWF.1 K ρ n,
    Layer.CompactXor.instrPerm_apply]
  rfl

end Streams

end IntegerMultBounds.MathlibTM2.Node
