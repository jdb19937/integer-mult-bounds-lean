module
public import IntegerMultBounds.MathlibTM2.Layer.PackedXor
import Mathlib.Tactic.Positivity.Finset
public import IntegerMultBounds.MathlibTM2.Host.Index
public import IntegerMultBounds.MathlibTM2.Host.Route


/-!
# Destination keys for the exceptional repair

The stream holds the `M = rectSize N₀ N₁ N₂ N₃ L` records of the packed rectangle in rank order,
`N₁ = 2^n₁`, `N₂ = 2^n₂`, `N₃ = 2^n₃`, `N₀ = R · 2^n₀` with `R ≤ 2^rb`; the record at rank `i`
has logical address `(enc σ)⁻¹ i`. The binary digits of the index `i` sit in the field counter
of `IntegerMultBounds.MathlibTM2.Host.Index` with the eight fields `idxLen = [n₃, L, n₂, L, n₁, L, n₀, rb]` (least
significant first): `s₃`, chunk slot `2`, `s₂`, chunk slot `1`, `s₁`, chunk slot `0`, the low
`n₀` bits of `s₀`, and the row `⌊s₀ / 2^n₀⌋`. Chunk slot `p` is field `slotF p`, so the logical
name `k` sits in field `slotF (σ⁻¹ k)` (`digit_enc_name`). The index has
`k = keyLen = n₃ + 3L + n₂ + n₁ + n₀ + rb` bits and `M ≤ 2^k` (`rectSize_le`).

**Generic programs.** `mapLoop` pops one column of several registers per step and pushes a
function of it onto several output registers (`mapLoop_exec`); `resetFields` sets every field of
the counter to zero (`resetFields_exec`); `absAuto` is a code automaton over an abstract state
type, encoded into stack symbols (`absAuto_eval`).

**Key pass.** `addrPerm σ P` is the map of ranks of a map `P` of triples, and `keyRecs k π l`
puts the `k` bits of `π j`, least significant first, in front of record `j`. For each record,
`keyPass σ` pushes the key bits field by field (`keyF`): `copyF` copies a field register, and
`xorF` reads the field of `y`, the field of `x` and the mask register in parallel and emits
`y ⊕ (x ∧ selMask K ρ (f - 1))`, the `y` digit of `enc σ (idealT a)`; then it moves the record
itself (`xferBlock`) and increments the counter (`keyRec`). The keyed stream is accumulated
reversed and moved back at the end, and the counter is reset (`keyPassAt`).

`keyPass_exec`: `src` ends holding `(keyRecs k (addrPerm σ (idealT L K ρ f)) l).flatten`, every
other register ends as it started, in at most `106 M (B + k + 1) + 4 k + 37` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor


/-! ### The index fields of the rectangle -/

section Fields

variable (n₀ n₁ n₂ n₃ L rb : ℕ)

/-- Field lengths of the record index, least significant first: `s₃`, chunk slot `2`, `s₂`,
chunk slot `1`, `s₁`, chunk slot `0`, the low `n₀` bits of `s₀`, and the row `⌊s₀ / 2^n₀⌋`. -/
def idxLen : Fin 8 → ℕ := ![n₃, L, n₂, L, n₁, L, n₀, rb]

/-- The number of key bits `k = n₃ + 3L + n₂ + n₁ + n₀ + rb`. -/
def keyLen : ℕ := n₃ + (L + (n₂ + (L + (n₁ + (L + (n₀ + rb))))))

lemma sum_idxLen : ∑ j, idxLen n₀ n₁ n₂ n₃ L rb j = keyLen n₀ n₁ n₂ n₃ L rb := by
  simp [idxLen, keyLen, Fin.sum_univ_eight]; ring

/-- The index field holding physical chunk slot `p`. -/
def slotF : Fin 3 → Fin 8 := ![5, 3, 1]

lemma idxLen_slotF (p : Fin 3) : idxLen n₀ n₁ n₂ n₃ L rb (slotF p) = L := by
  fin_cases p <;> rfl

lemma slotF_injective : Function.Injective slotF := by decide

/-- A number from its eight field digits. -/
def nest8 (d : Fin 8 → ℕ) : ℕ :=
  d 0 + 2 ^ n₃ * (d 1 + 2 ^ L * (d 2 + 2 ^ n₂ * (d 3 + 2 ^ L * (d 4 + 2 ^ n₁ *
    (d 5 + 2 ^ L * (d 6 + 2 ^ n₀ * d 7))))))

lemma div_pow_add' (n p q : ℕ) : n / 2 ^ (p + q) = n / 2 ^ p / 2 ^ q := by
  rw [pow_add, Nat.div_div_eq_div_mul]

lemma peel (a b p : ℕ) (ha : a < 2 ^ p) : (a + 2 ^ p * b) / 2 ^ p = b := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, zero_add]

lemma low (a b p : ℕ) (ha : a < 2 ^ p) : (a + 2 ^ p * b) % 2 ^ p = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

/-- The digits of `nest8 d` are `d`. -/
lemma digit_nest8 (d : Fin 8 → ℕ) (hd : ∀ j, d j < 2 ^ idxLen n₀ n₁ n₂ n₃ L rb j) (j : Fin 8) :
    digit (idxLen n₀ n₁ n₂ n₃ L rb) j (nest8 n₀ n₁ n₂ n₃ L d) = d j := by
  have h0 : d 0 < 2 ^ n₃ := hd 0
  have h1 : d 1 < 2 ^ L := hd 1
  have h2 : d 2 < 2 ^ n₂ := hd 2
  have h3 : d 3 < 2 ^ L := hd 3
  have h4 : d 4 < 2 ^ n₁ := hd 4
  have h5 : d 5 < 2 ^ L := hd 5
  have h6 : d 6 < 2 ^ n₀ := hd 6
  have h7 : d 7 < 2 ^ rb := hd 7
  fin_cases j <;>
    simp [digit, fieldOff, idxLen, Finset.sum_filter, Fin.sum_univ_eight, nest8, div_pow_add',
      peel, Nat.mod_eq_of_lt, *]

/-- Binary digits of a two-part number. -/
lemma binBits_add_mul (p q a b : ℕ) (ha : a < 2 ^ p) :
    binBits (p + q) (a + 2 ^ p * b) = binBits p a ++ binBits q b := by
  unfold binBits
  rw [List.ofFn_add]
  congr 1
  · apply List.ofFn_inj.mpr
    funext t
    rw [Nat.add_comm a, Nat.testBit_two_pow_mul_add b ha]
    simp
  · apply List.ofFn_inj.mpr
    funext t
    rw [Nat.add_comm a, Nat.testBit_two_pow_mul_add b ha]
    simp

/-- The key bits of `nest8 d` are the field digits, field by field. -/
lemma binBits_nest8 (d : Fin 8 → ℕ) (hd : ∀ j, d j < 2 ^ idxLen n₀ n₁ n₂ n₃ L rb j) :
    binBits (keyLen n₀ n₁ n₂ n₃ L rb) (nest8 n₀ n₁ n₂ n₃ L d) =
      (List.finRange 8).flatMap fun j => binBits (idxLen n₀ n₁ n₂ n₃ L rb j) (d j) := by
  have h0 : d 0 < 2 ^ n₃ := hd 0
  have h1 : d 1 < 2 ^ L := hd 1
  have h2 : d 2 < 2 ^ n₂ := hd 2
  have h3 : d 3 < 2 ^ L := hd 3
  have h4 : d 4 < 2 ^ n₁ := hd 4
  have h5 : d 5 < 2 ^ L := hd 5
  have h6 : d 6 < 2 ^ n₀ := hd 6
  have h7 : d 7 < 2 ^ rb := hd 7
  have h7' : binBits rb (d 7) = binBits rb (d 7) ++ binBits 0 0 := by simp
  simp only [keyLen, nest8]
  rw [binBits_add_mul _ _ _ _ (by simpa using h0), binBits_add_mul _ _ _ _ (by simpa using h1),
    binBits_add_mul _ _ _ _ (by simpa using h2), binBits_add_mul _ _ _ _ (by simpa using h3),
    binBits_add_mul _ _ _ _ (by simpa using h4), binBits_add_mul _ _ _ _ (by simpa using h5),
    binBits_add_mul _ _ _ _ (by simpa using h6)]
  simp [List.finRange_succ, idxLen]

end Fields

section Digits

variable (N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ rb R : ℕ)

/-- The eight field digits of the physical address `(s, c)`. -/
def idxDig (s : Spec N₀ N₁ N₂ N₃) (c : Tri L) : Fin 8 → ℕ :=
  ![s.2.2.2, c 2, s.2.2.1, c 1, s.2.1, c 0, s.1 % 2 ^ n₀, s.1 / 2 ^ n₀]

lemma idxDig_slotF (s : Spec N₀ N₁ N₂ N₃) (c : Tri L) (p : Fin 3) :
    idxDig N₀ N₁ N₂ N₃ L n₀ s c (slotF p) = c p := by
  fin_cases p <;> rfl

/-- The digits off the chunk fields do not depend on the chunks. -/
lemma idxDig_off (s : Spec N₀ N₁ N₂ N₃) (c c' : Tri L) (j : Fin 8) (hj : ∀ p, j ≠ slotF p) :
    idxDig N₀ N₁ N₂ N₃ L n₀ s c j = idxDig N₀ N₁ N₂ N₃ L n₀ s c' j := by
  fin_cases j <;> first | rfl | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) |
    exact absurd rfl (hj 2)

variable {N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ rb R}

/-- The digits fit their fields. -/
lemma idxDig_lt (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (s : Spec N₀ N₁ N₂ N₃) (c : Tri L) (j : Fin 8) :
    idxDig N₀ N₁ N₂ N₃ L n₀ s c j < 2 ^ idxLen n₀ n₁ n₂ n₃ L rb j := by
  obtain ⟨s₀, s₁, s₂, s₃⟩ := s
  have h0 := s₀.isLt; have h1 := s₁.isLt; have h2 := s₂.isLt; have h3 := s₃.isLt
  have hc0 := (c 0).isLt; have hc1 := (c 1).isLt; have hc2 := (c 2).isLt
  have h7 : (s₀ : ℕ) / 2 ^ n₀ < 2 ^ rb := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc (s₀ : ℕ) < N₀ := h0
      _ = R * 2 ^ n₀ := hN₀
      _ ≤ 2 ^ rb * 2 ^ n₀ := Nat.mul_le_mul_right _ hR
  have h6 : (s₀ : ℕ) % 2 ^ n₀ < 2 ^ n₀ := Nat.mod_lt _ (by positivity)
  fin_cases j
  · show (s₃ : ℕ) < 2 ^ n₃; omega
  · show ((c 2 : Fin (2 ^ L)) : ℕ) < 2 ^ L; omega
  · show (s₂ : ℕ) < 2 ^ n₂; omega
  · show ((c 1 : Fin (2 ^ L)) : ℕ) < 2 ^ L; omega
  · show (s₁ : ℕ) < 2 ^ n₁; omega
  · show ((c 0 : Fin (2 ^ L)) : ℕ) < 2 ^ L; omega
  · exact h6
  · exact h7

/-- The rank of a physical address is the number with its field digits. -/
lemma rank_eq_nest8 (hN₁ : N₁ = 2 ^ n₁) (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃)
    (s : Spec N₀ N₁ N₂ N₃) (c : Tri L) :
    rank N₀ N₁ N₂ N₃ L (s, c) = nest8 n₀ n₁ n₂ n₃ L (idxDig N₀ N₁ N₂ N₃ L n₀ s c) := by
  subst hN₁ hN₂ hN₃
  simp only [rank, nest8, idxDig]
  simp only [Fin.isValue, Matrix.cons_val]
  rw [Nat.mod_add_div]

/-- Digit `j` of the rank of a physical address. -/
lemma digit_rank (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (s : Spec N₀ N₁ N₂ N₃) (c : Tri L) (j : Fin 8) :
    digit (idxLen n₀ n₁ n₂ n₃ L rb) j (rank N₀ N₁ N₂ N₃ L (s, c)) =
      idxDig N₀ N₁ N₂ N₃ L n₀ s c j := by
  rw [rank_eq_nest8 hN₁ hN₂ hN₃, digit_nest8 _ _ _ _ _ _ _ (idxDig_lt hN₀ hR hN₁ hN₂ hN₃ s c)]

/-- The chunk field of the logical name `k` holds the value `a.2 k`. -/
lemma digit_enc_name (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (σ : Equiv.Perm (Fin 3))
    (a : Addr N₀ N₁ N₂ N₃ L) (k : Fin 3) :
    digit (idxLen n₀ n₁ n₂ n₃ L rb) (slotF (σ.symm k)) (enc N₀ N₁ N₂ N₃ L σ a) = a.2 k := by
  rw [enc_val, digit_rank hN₀ hR hN₁ hN₂ hN₃, idxDig_slotF]
  simp [phys]

/-- The rectangle fits the key bits. -/
lemma rectSize_le (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) :
    rectSize N₀ N₁ N₂ N₃ L ≤ 2 ^ keyLen n₀ n₁ n₂ n₃ L rb := by
  subst hN₀ hN₁ hN₂ hN₃
  have : rectSize (R * 2 ^ n₀) (2 ^ n₁) (2 ^ n₂) (2 ^ n₃) L =
      R * 2 ^ (n₃ + (L + (n₂ + (L + (n₁ + (L + n₀)))))) := by
    simp only [rectSize, pow_add]; ring
  rw [this, keyLen, show n₃ + (L + (n₂ + (L + (n₁ + (L + (n₀ + rb)))))) =
    rb + (n₃ + (L + (n₂ + (L + (n₁ + (L + n₀)))))) by ring, Nat.pow_add (m := rb)]
  exact Nat.mul_le_mul_right _ hR

end Digits

/-! ### Generic host programs -/

section Programs

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {ni no : ℕ}

/-- A stateless word automaton: each step outputs `F` of its input column. -/
def mapAuto (F : (Fin ni → Fin (A + 4)) → Fin no → Fin (A + 4)) : Auto A ni no :=
  ⟨blank, fun s c => (s, F c)⟩

/-- Pop one column of the registers `ins`, push `F` of it onto the registers `outs`, while
`ins 0` is nonempty. -/
def mapLoop [NeZero ni] (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st : Fin T)
    (F : (Fin ni → Fin (A + 4)) → Fin no → Fin (A + 4)) : Pr P T Q A U :=
  .loop (·.flag) (.seq (.act (autoStep ins outs st (mapAuto F))) (.act (peekR (ins 0))))

/-- The first `m` columns of the lists `ws`. -/
def colsR (ws : Fin ni → List (Fin (A + 4))) : ℕ → List (Fin ni → Fin (A + 4))
  | 0 => []
  | m + 1 => (fun i => (ws i).head?.getD blank) :: colsR (fun i => (ws i).tail) m

lemma colsR_map (i : Fin ni) :
    ∀ (m : ℕ) (ws : Fin ni → List (Fin (A + 4))), (ws i).length = m →
      (colsR ws m).map (fun c => c i) = ws i := by
  intro m
  induction m with
  | zero =>
      intro ws h
      have h0 : ws i = [] := List.eq_nil_of_length_eq_zero h
      rw [h0]; rfl
  | succ m ih =>
      intro ws h
      have hne : ws i ≠ [] := by intro e; rw [e] at h; simp at h
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
      simp only [colsR, List.map_cons]
      rw [ih _ (by simp [h])]
      rw [hx]
      rfl

lemma colsR_binSyms (vals : Fin ni → ℕ) :
    ∀ m : ℕ, colsR (fun i => (binSyms m (vals i) : List (Fin (A + 4)))) m =
      List.ofFn fun (t : Fin m) i => bitSymbol ((vals i).testBit t) := by
  intro m
  induction m generalizing vals with
  | zero => rfl
  | succ m ih =>
      simp only [colsR, binSyms_succ, List.head?_cons, Option.getD_some, List.tail_cons]
      rw [ih, List.ofFn_succ]
      simp [Nat.testBit_div_two]

/-- The column loop of a stateless automaton over `m` columns: every input register is emptied
and output register `j` gains the outputs, reversed. -/
theorem mapLoop_exec [NeZero ni] {ins : Fin ni → Fin T} {outs : Fin no → Fin T} {st : Fin T}
    (hins : Function.Injective ins) (houts : Function.Injective outs)
    (hio : ∀ i j, ins i ≠ outs j) (hst : ∀ i, ins i ≠ st)
    (F : (Fin ni → Fin (A + 4)) → Fin no → Fin (A + 4)) :
    ∀ (m : ℕ) (ws : Fin ni → List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      (∀ i, (ws i).length = m) → (∀ i, S.R (ins i) = ws i) → v.flag = (ws 0).head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (mapLoop ins outs st F) (mk v S) (3 * m + 1) (mk v' { S with R := R' }) ∧
        (∀ i, R' (ins i) = []) ∧
        (∀ j, R' (outs j) = ((colsR ws m).map fun c => F c j).reverse ++ S.R (outs j)) ∧
        ∀ k, k ∉ Set.range ins → k ∉ Set.range outs → R' k = S.R k := by
  intro m
  induction m with
  | zero =>
      intro ws v S hlen hS hf
      have hnil : ∀ i, ws i = [] := fun i => List.eq_nil_of_length_eq_zero (hlen i)
      refine ⟨v, S.R, rfl, Exec.cast (.loop_false (by simp [hf, hnil])) (by simp) rfl,
        fun i => by rw [hS, hnil], fun j => by simp [colsR], fun _ _ _ => rfl⟩
  | succ m ih =>
      intro ws v S hlen hS hf
      obtain ⟨v₁, S₁, hrun₁, hu₁, _, _, hi₁, ho₁, hl₁, hin₁, hout₁, hoth₁⟩ :=
        autoStep_run hins houts hio hst (mapAuto F) v S
      have htop : topCol ins S = fun i => (ws i).head?.getD blank := by
        funext i; simp [topCol, hS]
      obtain ⟨v', R', hu, he, hin', hout', hoth'⟩ := ih (fun i => (ws i).tail)
        { v₁ with flag := (S₁.R (ins 0)).head?.isSome } S₁
        (fun i => by simp [hlen]) (fun i => by rw [hin₁, hS]) (by rw [hin₁, hS])
      have hS₁ : ({ S₁ with R := R' } : Stacks T A) = { S with R := R' } := by
        cases S₁; cases S; simp_all
      have hne : ∀ i, ws i ≠ [] := fun i h => by simpa [h] using hlen i
      have hft : v.flag = true := by
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (hne 0)
        rw [hf, hx]; rfl
      refine ⟨v', R', by rw [hu, hu₁], ?_, hin', ?_, ?_⟩
      · rw [← hS₁]
        exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hft
          (Exec.seq (hrun₁ ▸ Exec.act (body := body) (autoStep ins outs st (mapAuto F)) (mk v S))
            (Exec.act (body := body) (peekR (ins 0)) (mk v₁ S₁))) he) (by ring) rfl
      · intro j
        rw [hout', hout₁, htop]
        simp [colsR, mapAuto]
      · intro k hk1 hk2
        rw [hoth' k hk1 hk2, hoth₁ k hk1 hk2]

/-! #### Resetting the field counter -/

/-- Overwrite every symbol of register `c` by `bitSymbol false`, through the empty register
`tmp`. -/
def resetField (c tmp : Fin T) : Pr P T Q A U :=
  .seq (moveR c tmp (fun _ => bitSymbol false)) (moveR tmp c id)

/-- Reset the fields `cf` of the counter to zero. -/
def resetFields {nf : ℕ} (cf : Fin nf → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  Prog.seqList ((List.finRange nf).map fun f => resetField (cf f) tmp)

/-- One field: every symbol of `c` becomes `bitSymbol false`; `tmp` ends empty. Exactly
`4 * |c| + 4` steps. -/
theorem resetField_exec (c tmp : Fin T) (h : c ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (ht : S.R tmp = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (resetField c tmp) (mk v S) (4 * (S.R c).length + 4)
        (mk v' { S with
          R := Function.update S.R c (List.replicate (S.R c).length (bitSymbol false)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body c tmp h (fun _ => bitSymbol false) v S
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp c h.symm id v₁
    { S with R := movedR S.R c tmp (fun _ => bitSymbol false) (S.R c) }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [movedR, ht]; ring
  · congr 2
    funext k
    by_cases hk : k = c
    · subst hk; simp [movedR, ht, Function.update_of_ne h]
    · by_cases hk' : k = tmp
      · subst hk'; simp [movedR, hk, ht, Function.update_of_ne (Ne.symm hk)]
      · simp [movedR, hk, hk']

lemma binSyms_zero_eq (ℓ : ℕ) :
    (binSyms ℓ 0 : List (Fin (A + 4))) = List.replicate ℓ (bitSymbol false) := by
  simp [binSyms, List.ofFn_const]

/-- The fields `fs` of the counter, in order: each ends holding `binSyms (len f) 0`. -/
theorem resetList_exec {nf : ℕ} (cf : Fin nf → Fin T) (hcf : Function.Injective cf) (tmp : Fin T)
    (htmp : ∀ f, cf f ≠ tmp) (len : Fin nf → ℕ) :
    ∀ (fs : List (Fin nf)), fs.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A), S.R tmp = [] →
      (∀ f ∈ fs, (S.R (cf f)).length = len f) →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (Prog.seqList (fs.map fun f => resetField (cf f) tmp)) (mk v S)
          ((fs.map fun f => 4 * len f + 4).sum + 1) (mk v' { S with R := R' }) ∧
        (∀ f ∈ fs, R' (cf f) = binSyms (len f) 0) ∧
        ∀ k, (∀ f ∈ fs, k ≠ cf f) → R' k = S.R k := by
  intro fs
  induction fs with
  | nil =>
      intro _ v S _ _
      exact ⟨v, S.R, rfl, by simpa [Prog.seqList] using Exec.act (body := body) .done (mk v S),
        by simp, fun _ _ => rfl⟩
  | cons f fs ih =>
      intro hnd v S ht hlen
      rw [List.nodup_cons] at hnd
      obtain ⟨v₁, hu₁, he₁⟩ := resetField_exec body (cf f) tmp (htmp f) v S ht
      rw [hlen f List.mem_cons_self] at he₁
      obtain ⟨v', R', hu, he, hfs, hoth⟩ := ih hnd.2 v₁
        { S with R := Function.update S.R (cf f) (List.replicate (len f) (bitSymbol false)) }
        (by simp [Function.update_of_ne (htmp f).symm, ht])
        (by
          intro g hg
          have hgf : g ≠ f := fun h => hnd.1 (h ▸ hg)
          simp [Function.update_of_ne (fun h => hgf (hcf h)), hlen g (List.mem_cons_of_mem _ hg)])
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.seq he₁ he) ?_ rfl, ?_, ?_⟩
      · simp; ring
      · intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · rw [hoth _ (fun g' hg' h => hnd.1 (by rw [hcf h]; exact hg')), binSyms_zero_eq]
          simp
        · exact hfs g hg
      · intro k hk
        rw [hoth k (fun g hg => hk g (List.mem_cons_of_mem _ hg))]
        simp [Function.update_of_ne (hk f List.mem_cons_self)]

/-- Resetting the fields: every field `cf f` holding `len f` symbols ends holding
`binSyms (len f) 0`; every other register is unchanged. Exactly
`4 * (∑ f, len f) + 4 * nf + 1` steps. -/
theorem resetFields_exec {nf : ℕ} (cf : Fin nf → Fin T) (hcf : Function.Injective cf)
    (tmp : Fin T) (htmp : ∀ f, cf f ≠ tmp) (len : Fin nf → ℕ) (v : HS T Q A U) (S : Stacks T A)
    (ht : S.R tmp = []) (hlen : ∀ f, (S.R (cf f)).length = len f) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body (resetFields cf tmp) (mk v S) (4 * (∑ f, len f) + 4 * nf + 1)
        (mk v' { S with R := R' }) ∧
      (∀ f, R' (cf f) = binSyms (len f) 0) ∧ ∀ k, (∀ f, k ≠ cf f) → R' k = S.R k := by
  obtain ⟨v', R', hu, he, hfs, hoth⟩ := resetList_exec body cf hcf tmp htmp len
    (List.finRange nf) (List.nodup_finRange nf) v S ht (fun f _ => hlen f)
  refine ⟨v', R', hu, Exec.cast he ?_ rfl, fun f => hfs f (List.mem_finRange f),
    fun k hk => hoth k (fun f _ => hk f)⟩
  rw [← Fin.sum_univ_def, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [Nat.mul_comm]

/-! #### Code automata over an abstract state -/

/-- A code automaton on an abstract state type, through an encoding into stack symbols. -/
def absAuto {St : Type} {nr nd : ℕ} (enc : St → Fin (A + 4)) (dec : Fin (A + 4) → St)
    (s₀ : St) (stp : St → (Fin nr → Bool) → St) (outF : St → Fin nd) : CAuto A nr nd where
  init := enc s₀
  step := fun s c => enc (stp (dec s) c)
  out := fun s => outF (dec s)

/-- The code of an abstract automaton is its output after the left fold over the bit
positions `0, …, L - 1`. -/
lemma absAuto_eval {St : Type} {nr nd : ℕ} (enc : St → Fin (A + 4)) (dec : Fin (A + 4) → St)
    (hd : ∀ s, dec (enc s) = s) (s₀ : St) (step : St → (Fin nr → Bool) → St) (out : St → Fin nd)
    (L : ℕ) (vals : Fin nr → ℕ) :
    (absAuto enc dec s₀ step out).eval L vals =
      out ((List.range L).foldl (fun s t => step s fun r => (vals r).testBit t) s₀) := by
  have key : ∀ (l : List ℕ) (s : St),
      l.foldl (fun s t => enc (step (dec s) fun r => (vals r).testBit t)) (enc s) =
        enc (l.foldl (fun s t => step s fun r => (vals r).testBit t) s) := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons t l ih => intro s; simp only [List.foldl_cons, hd]; exact ih _
  simp only [CAuto.eval, CAuto.run_eq_foldl]
  show out (dec ((List.range L).foldl (fun s t => enc (step (dec s) fun r => (vals r).testBit t))
    (enc s₀))) = _
  rw [key, hd]

end Programs

/-! ### Rank permutations and keyed records -/

section Keys

variable (N₀ N₁ N₂ N₃ L : ℕ)

/-- The map of ranks of a map of logical triples, for the stream in physical order `σ`: the
record at `enc σ a` moves to `enc σ (liftA P a)`. -/
def addrPerm (σ : Equiv.Perm (Fin 3)) (Pm : Equiv.Perm (Tri L)) :
    Equiv.Perm (Fin (rectSize N₀ N₁ N₂ N₃ L)) :=
  (enc N₀ N₁ N₂ N₃ L σ).symm.trans ((liftA N₀ N₁ N₂ N₃ L Pm).trans (enc N₀ N₁ N₂ N₃ L σ))

@[simp] lemma addrPerm_enc (σ : Equiv.Perm (Fin 3)) (Pm : Equiv.Perm (Tri L))
    (a : Addr N₀ N₁ N₂ N₃ L) :
    addrPerm N₀ N₁ N₂ N₃ L σ Pm (enc N₀ N₁ N₂ N₃ L σ a) =
      enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L Pm a) := by
  simp [addrPerm]

end Keys

/-- The keyed records: record `j` of `l` preceded by the `k` bits of its key `π j`, least
significant first. -/
def keyRecs {A M : ℕ} (k : ℕ) (π : Equiv.Perm (Fin M)) (l : List (List (Fin (A + 4)))) :
    List (List (Fin (A + 4))) :=
  List.ofFn fun j : Fin M => binSyms k (π j) ++ l.getD j []

/-- Records `rs` numbered from `i`, each preceded by the key symbols `kb` of its number. -/
def keyedFrom {α : Type} (kb : ℕ → List α) : ℕ → List (List α) → List (List α)
  | _, [] => []
  | i, r :: rs => (kb i ++ r) :: keyedFrom kb (i + 1) rs

lemma keyedFrom_eq {α : Type} (kb : ℕ → List α) :
    ∀ (rs : List (List α)) (i : ℕ),
      keyedFrom kb i rs = (List.range rs.length).map fun j => kb (i + j) ++ rs.getD j []
  | [], _ => rfl
  | r :: rs, i => by
      rw [keyedFrom, keyedFrom_eq kb rs (i + 1), List.length_cons, List.range_succ_eq_map,
        List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp [Nat.add_assoc, Nat.add_comm 1 j]

/-- A list of `M` items in `ofFn` form as a map over `range M`. -/
lemma ofFn_eq_range_map {α : Type} {M : ℕ} (g : Fin M → α) (g' : ℕ → α)
    (h : ∀ j : Fin M, g j = g' j) : List.ofFn g = (List.range M).map g' := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun j _ => h j

/-! ### The key pass -/

section KeyPass

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

lemma notMem_range_iff {n : ℕ} (f : Fin n → Fin T) (k : Fin T) :
    k ∉ Set.range f ↔ ∀ i, f i ≠ k := by
  simp [Set.mem_range]

/-- Copy register `c` onto `acc` (reversed), through the empty register `t0`. -/
def copyF (c t0 acc st : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR c))
    (.seq (mapLoop ![c] ![t0, acc] st fun col => ![col 0, col 0]) (moveR t0 c id))

/-- `copyF`: `acc` gains the contents of `c`, reversed; every other register is restored. Exactly
`5 * |c| + 4` steps. -/
theorem copyF_exec (c t0 acc st : Fin T) (h1 : c ≠ t0) (h2 : c ≠ acc) (h3 : t0 ≠ acc)
    (h4 : c ≠ st) (v : HS T Q A U) (S : Stacks T A) (ht : S.R t0 = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (copyF c t0 acc st) (mk v S) (5 * (S.R c).length + 4)
        (mk v' { S with R := Function.update S.R acc ((S.R c).reverse ++ S.R acc) }) := by
  set ws := S.R c with hws
  obtain ⟨v₁, R₁, hu₁, he₁, hin₁, hout₁, hoth₁⟩ := mapLoop_exec body (ins := ![c])
    (outs := ![t0, acc]) (st := st) (fun i j _ => Subsingleton.elim i j)
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm h3])
    (by intro i j; fin_cases i; fin_cases j <;> simp [h1, h2])
    (by intro i; fin_cases i; simpa using h4)
    (fun col => ![col 0, col 0]) ws.length (fun _ => ws) { v with flag := ws.head?.isSome } S
    (fun _ => rfl) (by intro i; fin_cases i; rfl) rfl
  have hR₁t : R₁ t0 = ws.reverse := by
    have := hout₁ 0
    simp only [Matrix.cons_val_zero] at this
    rw [this, colsR_map 0 _ (fun _ => ws) rfl, ht, List.append_nil]
  have hR₁a : R₁ acc = ws.reverse ++ S.R acc := by
    have := hout₁ 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [this, colsR_map 0 _ (fun _ => ws) rfl]
  have hR₁c : R₁ c = [] := hin₁ 0
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t0 c (Ne.symm h1) id v₁ { S with R := R₁ }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq (Exec.act (body := body) (peekR c) (mk v S))
    (Exec.seq he₁ he₂)) ?_ ?_⟩
  · simp only [hR₁t, List.length_reverse]; ring
  · congr 2
    funext k
    by_cases hka : k = acc
    · subst hka
      simp [movedR, Ne.symm h2, Ne.symm h3, hR₁a]
    by_cases hkc : k = c
    · subst hkc
      simp [movedR, hka, hR₁t, hR₁c, hws]
    by_cases hkt : k = t0
    · subst hkt
      simp [movedR, hka, hkc, ht]
    simp only [movedR, Function.update_of_ne hka, Function.update_of_ne hkc,
      Function.update_of_ne hkt]
    exact hoth₁ k ((notMem_range_iff _ k).2 fun i => by fin_cases i; exact Ne.symm hkc)
      ((notMem_range_iff _ k).2 fun i => by fin_cases i <;> simp [Ne.symm hkt, Ne.symm hka])

/-- The bit `y ⊕ (x ∧ m)` of a column `(y, x, m)`. -/
def xorBit (col : Fin 3 → Fin (A + 4)) : Fin (A + 4) :=
  bitSymbol (xor (symBit (col 0)) (symBit (col 1) && symBit (col 2)))

/-- Push the bits of `y ⊕ (x ∧ m)` onto `acc` (reversed), reading the registers `cy`, `cx`,
`cm` in parallel through the empty registers `t0`, `t1`, `t2`. -/
def xorF (cy cx cm t0 t1 t2 acc st : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR cy))
    (.seq (mapLoop ![cy, cx, cm] ![t0, t1, t2, acc] st fun col => ![col 0, col 1, col 2,
        xorBit col])
      (.seq (moveR t0 cy id) (.seq (moveR t1 cx id) (moveR t2 cm id))))

lemma map_xorBit (L y x mm : ℕ) :
    (colsR (fun i => (binSyms L (![y, x, mm] i) : List (Fin (A + 4)))) L).map xorBit =
      binSyms L (y ^^^ (x &&& mm)) := by
  rw [colsR_binSyms, List.map_ofFn]
  simp only [binSyms]
  congr 1
  funext t
  simp [xorBit, Nat.testBit_xor, Nat.testBit_and]

/-- `xorF`: `acc` gains the bits of `y ⊕ (x ∧ m)`, reversed; every other register is restored.
Exactly `9 L + 8` steps. -/
theorem xorF_exec (cy cx cm t0 t1 t2 acc st : Fin T)
    (hnd : [cy, cx, cm, t0, t1, t2, acc].Nodup) (hst : st ∉ [cy, cx, cm]) (L y x mm : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hy : S.R cy = binSyms L y) (hx : S.R cx = binSyms L x)
    (hm : S.R cm = binSyms L mm) (ht0 : S.R t0 = []) (ht1 : S.R t1 = []) (ht2 : S.R t2 = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (xorF cy cx cm t0 t1 t2 acc st) (mk v S) (9 * L + 8)
        (mk v' { S with
          R := Function.update S.R acc ((binSyms L (y ^^^ (x &&& mm))).reverse ++ S.R acc) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd hst
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5⟩, ⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3⟩,
    ⟨e1, e2⟩, f1⟩ := hnd
  obtain ⟨s1, s2, s3⟩ := hst
  set ws : Fin 3 → List (Fin (A + 4)) := fun i => binSyms L (![y, x, mm] i) with hws
  obtain ⟨v₁, R₁, hu₁, he₁, hin₁, hout₁, hoth₁⟩ := mapLoop_exec body (ins := ![cy, cx, cm])
    (outs := ![t0, t1, t2, acc]) (st := st)
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm a1, Ne.symm a2, Ne.symm b1])
    (by intro i j h; fin_cases i <;> fin_cases j <;>
      simp_all [Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm e1, Ne.symm e2, Ne.symm f1])
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [*])
    (by intro i; fin_cases i <;> simp [Ne.symm s1, Ne.symm s2, Ne.symm s3])
    (fun col => ![col 0, col 1, col 2, xorBit col]) L ws { v with flag := (S.R cy).head?.isSome } S
    (fun i => by simp [ws]) (by intro i; fin_cases i <;> simp [ws, hy, hx, hm])
    (by rw [hy]; try rfl)
  have hR₁0 : R₁ t0 = (binSyms L y).reverse := by
    have := hout₁ 0
    simp only [Matrix.cons_val_zero] at this
    rw [this, colsR_map 0 _ ws (by simp [ws]), ht0, List.append_nil]
    rfl
  have hR₁1 : R₁ t1 = (binSyms L x).reverse := by
    have := hout₁ 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [this, colsR_map 1 _ ws (by simp [ws]), ht1, List.append_nil]
    rfl
  have hR₁2 : R₁ t2 = (binSyms L mm).reverse := by
    have := hout₁ 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at this
    rw [this, colsR_map 2 _ ws (by simp [ws]), ht2, List.append_nil]
    rfl
  have hR₁a : R₁ acc = (binSyms L (y ^^^ (x &&& mm))).reverse ++ S.R acc := by
    have := hout₁ 3
    simp only [Matrix.cons_val_three, 
      Matrix.tail_cons, Matrix.head_cons] at this
    rw [this, ← map_xorBit]
  have hR₁y : R₁ cy = [] := hin₁ 0
  have hR₁x : R₁ cx = [] := hin₁ 1
  have hR₁m : R₁ cm = [] := hin₁ 2
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t0 cy (Ne.symm a3) id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ t0 cy id (R₁ t0) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body t1 cx (Ne.symm b3) id v₂ { S with R := R₂ }
  set R₃ := movedR R₂ t1 cx id (R₂ t1) with hR₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body t2 cm (Ne.symm c3) id v₃ { S with R := R₃ }
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq
    (Exec.act (body := body) (peekR cy) (mk v S)) (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))))
    ?_ ?_⟩
  · simp [hR₃, hR₂, movedR, hR₁0, hR₁1, hR₁2, b2, 
      Ne.symm a1, Ne.symm a4, Ne.symm a5,
      Ne.symm b4, 
      Ne.symm d1, Ne.symm d2, Ne.symm e1]
    ring
  · congr 2
    funext k
    by_cases hka : k = acc
    · subst hka
      simp [hR₃, hR₂, movedR, hR₁a, b2, c1, c2, 
          Ne.symm a1, Ne.symm a2, Ne.symm a4, Ne.symm a5,
          Ne.symm a6, Ne.symm b1, Ne.symm b4, Ne.symm b5, 
          Ne.symm c4, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm e1,
          Ne.symm e2, Ne.symm f1]
    by_cases hky : k = cy
    · subst hky
      simp [hR₃, hR₂, movedR, hka, hR₁0, hR₁y, hy, a1, a2, a4, a5, b2, c1,
          c2, Ne.symm a1, Ne.symm a2, Ne.symm a4,
          Ne.symm a5, Ne.symm b1, Ne.symm b4, 
          Ne.symm d1, Ne.symm d2, 
          Ne.symm e1]
    by_cases hkx : k = cx
    · subst hkx
      simp [hR₃, hR₂, movedR, hka, hky, hR₁1, hR₁x, hx, b1, b2, b4, 
          c1, c2, Ne.symm a2, Ne.symm a4,
          Ne.symm a5, Ne.symm b1, Ne.symm b4, 
          Ne.symm d1, Ne.symm d2, 
          Ne.symm e1]
    by_cases hkm : k = cm
    · subst hkm
      simp [hR₃, hR₂, movedR, hka, hky, hkx, hR₁2, hR₁m, hm, b2, 
          c1, c2, Ne.symm a1, 
          Ne.symm a4, Ne.symm a5, Ne.symm b4,
          Ne.symm d1, Ne.symm d2,
          Ne.symm e1]
    by_cases hk0 : k = t0
    · subst hk0
      simp [hR₃, hR₂, movedR, hka, hky, hkx, hkm, ht0, b2, 
          c1, c2, d1, d2, Ne.symm a1, Ne.symm a2, Ne.symm a4,
          Ne.symm a5, Ne.symm b1, Ne.symm b4, 
          Ne.symm d1, Ne.symm d2, 
          Ne.symm e1]
    by_cases hk1 : k = t1
    · subst hk1
      simp [hR₃, hR₂, movedR, hka, hky, hkx, hkm, hk0, ht1, b2, 
          c1, c2, e1, Ne.symm a1, Ne.symm a2, 
          Ne.symm a5, Ne.symm b1, Ne.symm b4,
          Ne.symm d2,
          Ne.symm e1]
    by_cases hk2 : k = t2
    · subst hk2
      simp [hR₃, hR₂, movedR, hka, hky, hkx, hkm, hk0, hk1, ht2, b2,
          c1, c2, Ne.symm a1, Ne.symm a2, 
          Ne.symm a4, Ne.symm b1, 
          Ne.symm d1]
    simp only [hR₃, hR₂, movedR, Function.update_of_ne hka, Function.update_of_ne hky,
      Function.update_of_ne hkx, Function.update_of_ne hkm, Function.update_of_ne hk0,
      Function.update_of_ne hk1, Function.update_of_ne hk2]
    exact hoth₁ k ((notMem_range_iff _ k).2 fun i => by
        fin_cases i <;> simp [Ne.symm hky, Ne.symm hkx, Ne.symm hkm])
      ((notMem_range_iff _ k).2 fun i => by
        fin_cases i <;> simp [Ne.symm hk0, Ne.symm hk1, Ne.symm hk2, Ne.symm hka])


/-! #### The key fields of one record -/

/-- The key digit of field `j`: digit `y ⊕ (x ∧ m)` in the field `yF` holding `y` (with `x`
in field `xF`), the digit itself elsewhere. -/
def keyDig (yF xF : Fin 8) (mm : ℕ) (ds : Fin 8 → ℕ) (j : Fin 8) : ℕ :=
  if j = yF then ds yF ^^^ (ds xF &&& mm) else ds j

/-- The step count of the key field program of field `j`. -/
def keyCost (yF : Fin 8) (len : Fin 8 → ℕ) (j : Fin 8) : ℕ :=
  if j = yF then 9 * len j + 8 else 5 * len j + 4

lemma keyCost_le (yF : Fin 8) (len : Fin 8 → ℕ) (j : Fin 8) :
    keyCost yF len j ≤ 9 * len j + 8 := by
  unfold keyCost; split_ifs <;> omega

/-- The program for field `j` of the key: `xorF` for the field `yF`, `copyF` elsewhere. -/
def keyF (yF xF : Fin 8) (cf : Fin 8 → Fin T) (cm t0 t1 t2 acc st : Fin T) (j : Fin 8) :
    Pr P T Q A U :=
  if j = yF then xorF (cf yF) (cf xF) cm t0 t1 t2 acc st else copyF (cf j) t0 acc st

/-- Registers holding the digits `ds` in the fields `cf`, the mask `mm` in `cm`, and the empty
temporaries `t0`, `t1`, `t2`. -/
def KeyState (cf : Fin 8 → Fin T) (len : Fin 8 → ℕ) (L : ℕ) (cm t0 t1 t2 : Fin T)
    (ds : Fin 8 → ℕ) (mm : ℕ) (R : Fin T → List (Fin (A + 4))) : Prop :=
  (∀ g, R (cf g) = binSyms (len g) (ds g)) ∧ R cm = binSyms L mm ∧ R t0 = [] ∧ R t1 = [] ∧
    R t2 = []

lemma KeyState.update {cf : Fin 8 → Fin T} {len : Fin 8 → ℕ} {L : ℕ} {cm t0 t1 t2 acc : Fin T}
    {ds : Fin 8 → ℕ} {mm : ℕ} {R : Fin T → List (Fin (A + 4))}
    (h : KeyState cf len L cm t0 t1 t2 ds mm R) (hc : ∀ g, cf g ≠ acc) (h1 : cm ≠ acc)
    (h2 : t0 ≠ acc) (h3 : t1 ≠ acc) (h4 : t2 ≠ acc) (X : List (Fin (A + 4))) :
    KeyState cf len L cm t0 t1 t2 ds mm (Function.update R acc X) :=
  ⟨fun g => by rw [Function.update_of_ne (hc g), h.1 g], by rw [Function.update_of_ne h1, h.2.1],
    by rw [Function.update_of_ne h2, h.2.2.1], by rw [Function.update_of_ne h3, h.2.2.2.1],
    by rw [Function.update_of_ne h4, h.2.2.2.2]⟩

/-- Register facts of the key fields. -/
structure KeyFieldRegs (cf : Fin 8 → Fin T) (cm t0 t1 t2 acc st : Fin T) : Prop where
  cf_inj : Function.Injective cf
  cf_ne : ∀ g, cf g ∉ [cm, t0, t1, t2, acc]
  cf_st : ∀ g, cf g ≠ st
  cm_st : cm ≠ st
  nd : [cm, t0, t1, t2, acc].Nodup

lemma KeyFieldRegs.cf_acc {cf : Fin 8 → Fin T} {cm t0 t1 t2 acc st : Fin T}
    (h : KeyFieldRegs cf cm t0 t1 t2 acc st) (g : Fin 8) : cf g ≠ acc :=
  fun e => h.cf_ne g (by simp [e])

lemma KeyFieldRegs.cf_cm {cf : Fin 8 → Fin T} {cm t0 t1 t2 acc st : Fin T}
    (h : KeyFieldRegs cf cm t0 t1 t2 acc st) (g : Fin 8) : cf g ≠ cm :=
  fun e => h.cf_ne g (by simp [e])

lemma KeyFieldRegs.cf_t0 {cf : Fin 8 → Fin T} {cm t0 t1 t2 acc st : Fin T}
    (h : KeyFieldRegs cf cm t0 t1 t2 acc st) (g : Fin 8) : cf g ≠ t0 :=
  fun e => h.cf_ne g (by simp [e])

lemma KeyFieldRegs.cf_t1 {cf : Fin 8 → Fin T} {cm t0 t1 t2 acc st : Fin T}
    (h : KeyFieldRegs cf cm t0 t1 t2 acc st) (g : Fin 8) : cf g ≠ t1 :=
  fun e => h.cf_ne g (by simp [e])

lemma KeyFieldRegs.cf_t2 {cf : Fin 8 → Fin T} {cm t0 t1 t2 acc st : Fin T}
    (h : KeyFieldRegs cf cm t0 t1 t2 acc st) (g : Fin 8) : cf g ≠ t2 :=
  fun e => h.cf_ne g (by simp [e])

lemma KeyFieldRegs.acc_ne {cf : Fin 8 → Fin T} {cm t0 t1 t2 acc st : Fin T}
    (h : KeyFieldRegs cf cm t0 t1 t2 acc st) : acc ≠ cm ∧ acc ≠ t0 ∧ acc ≠ t1 ∧ acc ≠ t2 := by
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  exact ⟨Ne.symm hnd.1.2.2.2, Ne.symm hnd.2.1.2.2, Ne.symm hnd.2.2.1.2, Ne.symm hnd.2.2.2⟩

/-- The key field program of field `j`: `acc` gains the key digit of field `j`, reversed. -/
theorem keyF_exec {yF xF : Fin 8} (hyx : yF ≠ xF) {cf : Fin 8 → Fin T} {cm t0 t1 t2 acc st : Fin T}
    (h : KeyFieldRegs cf cm t0 t1 t2 acc st) {len : Fin 8 → ℕ} (hlen : len xF = len yF)
    {ds : Fin 8 → ℕ} {mm : ℕ} (j : Fin 8) (v : HS T Q A U) (S : Stacks T A)
    (hS : KeyState cf len (len yF) cm t0 t1 t2 ds mm S.R) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (keyF yF xF cf cm t0 t1 t2 acc st j) (mk v S) (keyCost yF len j)
        (mk v' { S with R := (Function.update S.R acc
          ((binSyms (len j) (keyDig yF xF mm ds j)).reverse ++ S.R acc)) }) := by
  have hc := h.cf_ne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hnd
  unfold keyF keyCost keyDig
  by_cases hj : j = yF
  · subst hj
    simp only [↓reduceIte]
    have hyx' : cf j ≠ cf xF := fun e => hyx (h.cf_inj e)
    obtain ⟨v', hu, he⟩ := xorF_exec body (cf j) (cf xF) cm t0 t1 t2 acc st
      (by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true, not_false_eq_true]
        exact ⟨⟨hyx', hc j⟩, hc xF, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm (h.cf_st j), Ne.symm (h.cf_st xF), Ne.symm h.cm_st⟩)
      (len j) (ds j) (ds xF) mm v S (hS.1 j) (by rw [hS.1 xF, hlen]) hS.2.1 hS.2.2.1 hS.2.2.2.1
      hS.2.2.2.2
    exact ⟨v', hu, he⟩
  · simp only [hj, ↓reduceIte]
    obtain ⟨v', hu, he⟩ := copyF_exec body (cf j) t0 acc st (hc j).2.1 (hc j).2.2.2.2 b3
      (h.cf_st j) v S hS.2.2.1
    rw [hS.1 j] at he
    exact ⟨v', hu, by simpa using he⟩

/-- The key fields `fs`, in order: `acc` gains the key digits of the fields, each least
significant bit first, reversed; every other register is unchanged. -/
theorem keyList_exec {yF xF : Fin 8} (hyx : yF ≠ xF) {cf : Fin 8 → Fin T}
    {cm t0 t1 t2 acc st : Fin T} (h : KeyFieldRegs cf cm t0 t1 t2 acc st) {len : Fin 8 → ℕ}
    (hlen : len xF = len yF) {ds : Fin 8 → ℕ} {mm : ℕ} :
    ∀ (fs : List (Fin 8)) (v : HS T Q A U) (S : Stacks T A),
      KeyState cf len (len yF) cm t0 t1 t2 ds mm S.R →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (Prog.seqList (fs.map (keyF yF xF cf cm t0 t1 t2 acc st))) (mk v S)
          ((fs.map (keyCost yF len)).sum + 1)
          (mk v' { S with R := (Function.update S.R acc
            ((fs.flatMap fun j => binSyms (len j) (keyDig yF xF mm ds j)).reverse ++
              S.R acc)) }) := by
  have hc := h.cf_ne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  have hnd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hnd
  intro fs
  induction fs with
  | nil =>
      intro v S _
      refine ⟨v, rfl, Exec.cast (Exec.act (body := body) .done (mk v S)) (by simp) ?_⟩
      simp
  | cons j fs ih =>
      intro v S hS
      obtain ⟨v₁, hu₁, he₁⟩ := keyF_exec body hyx h hlen j v S hS
      obtain ⟨v', hu, he⟩ := ih v₁ { S with R := (Function.update S.R acc
          ((binSyms (len j) (keyDig yF xF mm ds j)).reverse ++ S.R acc)) }
        (hS.update (fun g => (hc g).2.2.2.2) a4 b3 c2 d1 _)
      refine ⟨v', by rw [hu, hu₁], Exec.cast (Exec.seq he₁ he) (by simp; ring) ?_⟩
      simp only [Function.update_idem, Function.update_self, List.flatMap_cons,
        List.reverse_append, List.append_assoc]

/-! #### One record and the record loop -/

/-- One record of the key pass at index `i`: the key fields onto `acc`, the record itself from
`src` onto `acc`, an increment of the field counter, and a test of `src`. -/
def keyRec (yF xF : Fin 8) (src acc ctrB tmp cm t0 t1 t2 st : Fin T) (cf : Fin 8 → Fin T) :
    Pr P T Q A U :=
  .seq (Prog.seqList ((List.finRange 8).map (keyF yF xF cf cm t0 t1 t2 acc st)))
    (.seq (xferBlock (fun _ : Fin 1 => src) (fun _ => acc) ctrB tmp st 1 (fun _ => 0) .done)
      (.seq (incrFields cf tmp st) (.act (peekR src))))

/-- Register facts of the key pass. -/
structure KeyRegs (src acc ctrB tmp cm t0 t1 t2 st : Fin T) (cf : Fin 8 → Fin T) : Prop
    extends KeyFieldRegs cf cm t0 t1 t2 acc st where
  cf_src : ∀ g, cf g ≠ src
  cf_ctr : ∀ g, cf g ≠ ctrB
  cf_tmp : ∀ g, cf g ≠ tmp
  src_acc : src ≠ acc
  src_ctr : src ≠ ctrB
  src_tmp : src ≠ tmp
  acc_ctr : acc ≠ ctrB
  acc_tmp : acc ≠ tmp
  ctr_tmp : ctrB ≠ tmp
  src_cm : src ≠ cm
  src_t0 : src ≠ t0
  src_t1 : src ≠ t1
  src_t2 : src ≠ t2
  ctr_cm : ctrB ≠ cm
  ctr_t0 : ctrB ≠ t0
  ctr_t1 : ctrB ≠ t1
  ctr_t2 : ctrB ≠ t2
  tmp_cm : tmp ≠ cm
  tmp_t0 : tmp ≠ t0
  tmp_t1 : tmp ≠ t1
  tmp_t2 : tmp ≠ t2

/-- The key symbols emitted for the record with index `i`. -/
def keyBitsAt (yF xF : Fin 8) (len : Fin 8 → ℕ) (mm i : ℕ) : List (Fin (A + 4)) :=
  (List.finRange 8).flatMap fun j => binSyms (len j) (keyDig yF xF mm (fun g => digit len g i) j)

/-- The step count of one record of the key pass. -/
def keyRecCost (yF : Fin 8) (len : Fin 8 → ℕ) (B : ℕ) : ℕ :=
  ((List.finRange 8).map (keyCost yF len)).sum + 1 + (4 * B + 5) + (4 * (∑ f, len f) + 4 * 8 + 2)
    + 1

/-- One record of the key pass at index `i`: `src` loses the record `r`, `acc` gains the key
symbols and `r`, reversed, and the counter advances to `i + 1`. -/
theorem keyRec_exec {yF xF : Fin 8} (hyx : yF ≠ xF) {src acc ctrB tmp cm t0 t1 t2 st : Fin T}
    {cf : Fin 8 → Fin T} (h : KeyRegs src acc ctrB tmp cm t0 t1 t2 st cf) {len : Fin 8 → ℕ}
    (hlen : len xF = len yF) {mm i : ℕ} (r rest c : List (Fin (A + 4))) (hcr : c.length = r.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hS : KeyState cf len (len yF) cm t0 t1 t2 (fun g => digit len g i) mm S.R)
    (hsrc : S.R src = r ++ rest) (hctr : S.R ctrB = c) (htmp : S.R tmp = []) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      v'.flag = rest.head?.isSome ∧
      Exec body (keyRec yF xF src acc ctrB tmp cm t0 t1 t2 st cf) (mk v S)
        (keyRecCost yF len r.length) (mk v' { S with R := R' }) ∧
      R' src = rest ∧ R' acc = (keyBitsAt yF xF len mm i ++ r).reverse ++ S.R acc ∧
      (∀ g, R' (cf g) = binSyms (len g) (digit len g (i + 1))) ∧
      ∀ k, k ≠ src → k ≠ acc → (∀ g, k ≠ cf g) → R' k = S.R k := by
  obtain ⟨v₁, hu₁, he₁⟩ := keyList_exec body hyx h.toKeyFieldRegs hlen (List.finRange 8) v S hS
  set R₁ := Function.update S.R acc ((keyBitsAt yF xF len mm i).reverse ++ S.R acc) with hR₁
  have hR₁f : ∀ k, k ≠ acc → R₁ k = S.R k := fun k hk => Function.update_of_ne hk _ _
  obtain ⟨v₂, R₂, hu₂, -, he₂, hctr₂, htmp₂, hsrc₂, hacc₂, hoth₂⟩ :=
    xferBlock_exec body (fun _ : Fin 1 => src) (fun _ => acc) ctrB tmp st 1 (fun _ => 0) .done 0
      h.src_ctr h.src_tmp h.ctr_tmp (Ne.symm h.src_acc) h.acc_ctr h.acc_tmp c r rest v₁
      { S with R := R₁ } hcr (by show R₁ ctrB = c; rw [hR₁f _ (Ne.symm h.acc_ctr), hctr])
      (by show R₁ tmp = []; rw [hR₁f _ (Ne.symm h.acc_tmp), htmp])
      (by show R₁ src = r ++ rest; rw [hR₁f _ h.src_acc, hsrc])
      (Subsingleton.elim _ _)
  rw [run_done] at he₂
  have hR₂f : ∀ k, k ≠ src → k ≠ acc → R₂ k = S.R k := fun k hk1 hk2 => by
    by_cases hkc : k = ctrB
    · subst hkc; rw [hctr₂, hctr]
    by_cases hkt : k = tmp
    · subst hkt; rw [htmp₂, htmp]
    rw [hoth₂ k hk1 hkc hkt hk2]
    exact hR₁f k hk2
  have hacc : R₂ acc = (keyBitsAt yF xF len mm i ++ r).reverse ++ S.R acc := by
    rw [hacc₂]
    show r.reverse ++ R₁ acc = _
    rw [hR₁, Function.update_self, List.reverse_append, List.append_assoc]
  obtain ⟨v₃, R₃, hu₃, he₃, hcf₃, hoth₃⟩ := incrFields_exec body cf h.cf_inj tmp st h.cf_tmp len i
    _ { S with R := R₂ } htmp₂
    (fun g => by show R₂ (cf g) = _; rw [hR₂f _ (h.cf_src g) (h.cf_acc g)]; exact hS.1 g)
  have hR₃f : ∀ k, (∀ g, k ≠ cf g) → R₃ k = R₂ k := hoth₃
  refine ⟨_, R₃, by simp [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂
    (Exec.seq he₃ (Exec.act (body := body) (peekR src) _)))) ?_ rfl, ?_, ?_, hcf₃, ?_⟩
  · show (R₃ src).head?.isSome = _
    rw [hR₃f _ (fun g => Ne.symm (h.cf_src g)), hsrc₂]
  · simp only [keyRecCost, hcr]; ring
  · rw [hR₃f _ (fun g => Ne.symm (h.cf_src g)), hsrc₂]
  · rw [hR₃f _ (fun g => Ne.symm (h.cf_acc g)), hacc]
  · intro k hk1 hk2 hk3
    rw [hR₃f k hk3, hR₂f k hk1 hk2]

/-- The record loop of the key pass, from index `i` with the records `rs` left in `src`. -/
theorem keyLoop_exec {yF xF : Fin 8} (hyx : yF ≠ xF) {src acc ctrB tmp cm t0 t1 t2 st : Fin T}
    {cf : Fin 8 → Fin T} (h : KeyRegs src acc ctrB tmp cm t0 t1 t2 st cf) {len : Fin 8 → ℕ}
    (hlen : len xF = len yF) {mm B : ℕ} (hB : 1 ≤ B) (c : List (Fin (A + 4)))
    (hcB : c.length = B) :
    ∀ (rs : List (List (Fin (A + 4)))) (i : ℕ) (v : HS T Q A U) (S : Stacks T A),
      (∀ r ∈ rs, r.length = B) →
      KeyState cf len (len yF) cm t0 t1 t2 (fun g => digit len g i) mm S.R →
      S.R src = rs.flatten → S.R ctrB = c → S.R tmp = [] → v.flag = rs.flatten.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (.loop (·.flag) (keyRec yF xF src acc ctrB tmp cm t0 t1 t2 st cf)) (mk v S)
          (rs.length * (keyRecCost yF len B + 1) + 1) (mk v' { S with R := R' }) ∧
        R' src = [] ∧
        R' acc = (keyedFrom (keyBitsAt yF xF len mm) i rs).flatten.reverse ++ S.R acc ∧
        (∀ g, R' (cf g) = binSyms (len g) (digit len g (i + rs.length))) ∧
        ∀ k, k ≠ src → k ≠ acc → (∀ g, k ≠ cf g) → R' k = S.R k := by
  obtain ⟨a1, a2, a3, a4⟩ := h.acc_ne
  intro rs
  induction rs with
  | nil =>
      intro i v S _ hS hsrc _ _ hf
      refine ⟨v, S.R, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) rfl,
        by simpa using hsrc, by simp [keyedFrom], fun g => by rw [hS.1 g]; simp,
        fun _ _ _ _ => rfl⟩
  | cons r rs ih =>
      intro i v S hrs hS hsrc hctr htmp hf
      have hr : r.length = B := hrs r List.mem_cons_self
      obtain ⟨v₁, R₁, hu₁, hf₁, he₁, hsrc₁, hacc₁, hcf₁, hoth₁⟩ := keyRec_exec body hyx h hlen r
        rs.flatten c (by rw [hcB, hr]) v S hS (by simp [hsrc]) hctr htmp
      have hR₁ : ∀ k, k ≠ src → k ≠ acc → (∀ g, k ≠ cf g) → R₁ k = S.R k := hoth₁
      obtain ⟨v', R', hu, he, hsrc', hacc', hcf', hoth'⟩ := ih (i + 1) v₁ { S with R := R₁ }
        (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'))
        ⟨hcf₁, by
          show R₁ cm = _
          rw [hR₁ _ h.src_cm.symm a1.symm (fun g => (h.cf_cm g).symm), hS.2.1],
          by
            show R₁ t0 = _
            rw [hR₁ _ h.src_t0.symm a2.symm (fun g => (h.cf_t0 g).symm), hS.2.2.1],
          by
            show R₁ t1 = _
            rw [hR₁ _ h.src_t1.symm a3.symm (fun g => (h.cf_t1 g).symm), hS.2.2.2.1],
          by
            show R₁ t2 = _
            rw [hR₁ _ h.src_t2.symm a4.symm (fun g => (h.cf_t2 g).symm), hS.2.2.2.2]⟩
        hsrc₁
        (by
          show R₁ ctrB = c
          rw [hR₁ _ h.src_ctr.symm h.acc_ctr.symm (fun g => (h.cf_ctr g).symm), hctr])
        (by
          show R₁ tmp = []
          rw [hR₁ _ h.src_tmp.symm h.acc_tmp.symm (fun g => (h.cf_tmp g).symm), htmp])
        hf₁
      have hne : r ≠ [] := fun e => by rw [e] at hr; simp at hr; omega
      have hft : v.flag = true := by
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
        rw [hf, List.flatten_cons, hx]; rfl
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hft
        he₁ he) (by rw [hr, List.length_cons]; ring) rfl, hsrc', ?_, ?_, ?_⟩
      · rw [hacc']
        show _ ++ R₁ acc = _
        rw [hacc₁]
        simp [keyedFrom, List.flatten_cons, List.reverse_append, List.append_assoc]
      · intro g
        rw [hcf' g, List.length_cons, show i + 1 + rs.length = i + (rs.length + 1) by ring]
      · intro k hk1 hk2 hk3
        rw [hoth' k hk1 hk2 hk3]
        exact hR₁ k hk1 hk2 hk3

lemma length_keyBitsAt (yF xF : Fin 8) (len : Fin 8 → ℕ) (mm i : ℕ) :
    (keyBitsAt (A := A) yF xF len mm i).length = ∑ j, len j := by
  simp [keyBitsAt, List.length_flatMap, Fin.sum_univ_def]

lemma length_keyedFrom (yF xF : Fin 8) (len : Fin 8 → ℕ) (mm B : ℕ) :
    ∀ (rs : List (List (Fin (A + 4)))) (i : ℕ), (∀ r ∈ rs, r.length = B) →
      (keyedFrom (keyBitsAt yF xF len mm) i rs).flatten.length = rs.length * ((∑ j, len j) + B)
  | [], _, _ => by simp [keyedFrom]
  | r :: rs, i, h => by
      rw [keyedFrom, List.flatten_cons, List.length_append, List.length_append,
        length_keyBitsAt, h r List.mem_cons_self,
        length_keyedFrom yF xF len mm B rs (i + 1)
          (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]
      simp only [List.length_cons]
      ring

/-- The key pass for the chunk field `yF` holding `y` and `xF` holding `x`. -/
def keyPassAt (yF xF : Fin 8) (src acc ctrB tmp cm t0 t1 t2 st : Fin T) (cf : Fin 8 → Fin T) :
    Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (keyRec yF xF src acc ctrB tmp cm t0 t1 t2 st cf))
      (.seq (moveR acc src id) (resetFields cf tmp)))

/-- The key pass on any field layout: the records `l` in `src` are replaced by the keyed records
`keyedFrom (keyBitsAt …) 0 l`, and every other register is restored. -/
theorem keyPassAt_exec {yF xF : Fin 8} (hyx : yF ≠ xF) {src acc ctrB tmp cm t0 t1 t2 st : Fin T}
    {cf : Fin 8 → Fin T} (h : KeyRegs src acc ctrB tmp cm t0 t1 t2 st cf) {len : Fin 8 → ℕ}
    (hlen : len xF = len yF) {mm B : ℕ} (hB : 1 ≤ B) (l : List (List (Fin (A + 4))))
    (hlB : ∀ r ∈ l, r.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = l.flatten) (hacc : S.R acc = []) (hctr : (S.R ctrB).length = B)
    (htmp : S.R tmp = []) (hS : KeyState cf len (len yF) cm t0 t1 t2 (fun _ => 0) mm S.R) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (keyPassAt yF xF src acc ctrB tmp cm t0 t1 t2 st cf) (mk v S)
        (1 + (l.length * (keyRecCost yF len B + 1) + 1) +
          (2 * (l.length * ((∑ j, len j) + B)) + 2) + (4 * (∑ f, len f) + 4 * 8 + 1))
        (mk v' { S with R := (Function.update S.R src
          (keyedFrom (keyBitsAt yF xF len mm) 0 l).flatten) }) := by
  obtain ⟨a1, a2, a3, a4⟩ := h.acc_ne
  have hS0 : KeyState cf len (len yF) cm t0 t1 t2 (fun g => digit len g 0) mm S.R := by
    refine ⟨fun g => ?_, hS.2⟩
    rw [hS.1 g]; simp [digit]
  obtain ⟨v₁, R₁, hu₁, he₁, hsrc₁, hacc₁, hcf₁, hoth₁⟩ := keyLoop_exec body hyx h hlen hB
    (S.R ctrB) hctr l 0 { v with flag := (S.R src).head?.isSome } S hlB hS0 hsrc rfl htmp
    (by rw [hsrc])
  rw [hacc, List.append_nil] at hacc₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body acc src (Ne.symm h.src_acc) id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ acc src id (R₁ acc) with hR₂
  have hR₂src : R₂ src = (keyedFrom (keyBitsAt yF xF len mm) 0 l).flatten := by
    simp [hR₂, movedR, hacc₁, hsrc₁]
  have hR₂acc : R₂ acc = [] := by simp [hR₂, movedR, Ne.symm h.src_acc]
  have hR₂f : ∀ k, k ≠ src → k ≠ acc → R₂ k = R₁ k := fun k hk1 hk2 => by
    simp [hR₂, movedR, hk1, hk2]
  obtain ⟨v₃, R₃, hu₃, he₃, hcf₃, hoth₃⟩ := resetFields_exec body cf h.cf_inj tmp h.cf_tmp len
    v₂ { S with R := R₂ }
    (by
      show R₂ tmp = []
      rw [hR₂f _ h.src_tmp.symm h.acc_tmp.symm,
        hoth₁ _ h.src_tmp.symm h.acc_tmp.symm (fun g => (h.cf_tmp g).symm), htmp])
    (fun g => by
      show (R₂ (cf g)).length = _
      rw [hR₂f _ (h.cf_src g) (h.cf_acc g), hcf₁ g]; simp)
  refine ⟨v₃, by rw [hu₃, hu₂, hu₁], Exec.cast (Exec.seq (Exec.act (body := body) (peekR src)
    (mk v S)) (Exec.seq he₁ (Exec.seq he₂ he₃))) ?_ ?_⟩
  · show _ + (_ + (2 * (R₁ acc).length + 2 + _)) = _
    rw [hacc₁, List.length_reverse, length_keyedFrom yF xF len mm B l 0 hlB]
    ring
  · congr 2
    funext k
    by_cases hkc : ∃ g, k = cf g
    · obtain ⟨g, rfl⟩ := hkc
      rw [hcf₃ g, Function.update_of_ne (h.cf_src g), hS.1 g]
    simp only [not_exists] at hkc
    rw [hoth₃ k hkc]
    show R₂ k = _
    by_cases hks : k = src
    · subst hks; rw [hR₂src, Function.update_self]
    by_cases hka : k = acc
    · subst hka; rw [hR₂acc, Function.update_of_ne hks, hacc]
    rw [hR₂f k hks hka, hoth₁ k hks hka (fun g e => hkc g e), Function.update_of_ne hks]

end KeyPass

/-! #### The key pass on the rectangle -/

section KeyMain

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
  {N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ rb R : ℕ}

/-- **The key pass** for physical order `σ`: the chunk field of `y` is slot `σ⁻¹ 1`, of `x`
slot `σ⁻¹ 0`. -/
def keyPass (σ : Equiv.Perm (Fin 3)) (src acc ctrB tmp cm t0 t1 t2 st : Fin T)
    (cf : Fin 8 → Fin T) : Pr P T Q A U :=
  keyPassAt (slotF (σ.symm 1)) (slotF (σ.symm 0)) src acc ctrB tmp cm t0 t1 t2 st cf

/-- The value of `idealT` on the name `y`: `y ⊕ (x ∧ selMask K ρ (f - 1))`. -/
lemma idealT_apply_one (K ρ f : ℕ) (v : Tri L) :
    ((idealT L K ρ f v 1 : Fin (2 ^ L)) : ℕ) =
      (v 1 : ℕ) ^^^ ((v 0 : ℕ) &&& selMask K ρ (f - 1)) := by
  show ((xorMask L (selMask K ρ (f - 1)) v 1 : Fin (2 ^ L)) : ℕ) = _
  simp [xorMask]

/-- `idealT` fixes the names `x` and `z`. -/
lemma idealT_apply_ne (K ρ f : ℕ) (v : Tri L) (k : Fin 3) (hk : k ≠ 1) :
    idealT L K ρ f v k = v k := by
  show xorMask L (selMask K ρ (f - 1)) v k = _
  simp [xorMask, Function.update_of_ne hk]

/-- The key symbols of the record at `enc σ a` are the bits of `enc σ (idealT a)`. -/
lemma keyBitsAt_enc (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (K ρ f : ℕ) (σ : Equiv.Perm (Fin 3))
    (a : Addr N₀ N₁ N₂ N₃ L) :
    keyBitsAt (A := A) (slotF (σ.symm 1)) (slotF (σ.symm 0)) (idxLen n₀ n₁ n₂ n₃ L rb)
        (selMask K ρ (f - 1)) (enc N₀ N₁ N₂ N₃ L σ a) =
      binSyms (keyLen n₀ n₁ n₂ n₃ L rb)
        (enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f) a)) := by
  obtain ⟨s, v⟩ := a
  set c := phys L σ v with hc
  set c' := phys L σ (idealT L K ρ f v) with hc'
  have hdig : ∀ g, digit (idxLen n₀ n₁ n₂ n₃ L rb) g (enc N₀ N₁ N₂ N₃ L σ (s, v)) =
      idxDig N₀ N₁ N₂ N₃ L n₀ s c g := fun g => by
    rw [enc_val, digit_rank hN₀ hR hN₁ hN₂ hN₃]
  have hkey : ∀ j, keyDig (slotF (σ.symm 1)) (slotF (σ.symm 0)) (selMask K ρ (f - 1))
      (fun g => digit (idxLen n₀ n₁ n₂ n₃ L rb) g (enc N₀ N₁ N₂ N₃ L σ (s, v))) j =
      idxDig N₀ N₁ N₂ N₃ L n₀ s c' j := by
    intro j
    simp only [keyDig, hdig]
    split_ifs with hj
    · subst hj
      rw [idxDig_slotF, idxDig_slotF, idxDig_slotF, hc, hc']
      simp only [phys, Function.comp_apply, Equiv.apply_symm_apply]
      rw [idealT_apply_one]
    · by_cases hp : ∃ p, j = slotF p
      · obtain ⟨p, rfl⟩ := hp
        rw [idxDig_slotF, idxDig_slotF, hc, hc']
        have hσp : σ p ≠ 1 := fun e => hj (by rw [← e, Equiv.symm_apply_apply])
        simp only [phys, Function.comp_apply]
        rw [idealT_apply_ne K ρ f v (σ p) hσp]
      · simp only [not_exists] at hp
        exact idxDig_off N₀ N₁ N₂ N₃ L n₀ s c c' j hp
  have hlt := idxDig_lt (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) (L := L) hN₀ hR hN₁ hN₂ hN₃ s c'
  rw [keyBitsAt]
  simp only [hkey, binSyms_eq]
  rw [← List.map_flatMap, ← binBits_nest8 n₀ n₁ n₂ n₃ L rb _ hlt, ← rank_eq_nest8 hN₁ hN₂ hN₃,
    enc_val]
  rfl

/-- The keyed records built by the key pass are `keyRecs` of the ideal map. -/
lemma keyedFrom_eq_keyRecs (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (K ρ f : ℕ) (σ : Equiv.Perm (Fin 3))
    (l : List (List (Fin (A + 4)))) (hl : l.length = rectSize N₀ N₁ N₂ N₃ L) :
    keyedFrom (keyBitsAt (slotF (σ.symm 1)) (slotF (σ.symm 0)) (idxLen n₀ n₁ n₂ n₃ L rb)
        (selMask K ρ (f - 1))) 0 l =
      keyRecs (keyLen n₀ n₁ n₂ n₃ L rb) (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l := by
  rw [keyedFrom_eq, keyRecs, hl]
  symm
  apply ofFn_eq_range_map
  intro j
  obtain ⟨a, rfl⟩ := (enc N₀ N₁ N₂ N₃ L σ).surjective j
  rw [Nat.zero_add, addrPerm_enc, keyBitsAt_enc hN₀ hR hN₁ hN₂ hN₃]

/-- Register facts of the key pass from a duplicate-free register list. -/
lemma KeyRegs.of_nodup {src acc ctrB tmp cm t0 t1 t2 st : Fin T} {cf : Fin 8 → Fin T}
    (hreg : ([src, acc, ctrB, tmp, t0, t1, t2, cm] ++ List.ofFn cf).Nodup)
    (hst : st ∉ cm :: List.ofFn cf) : KeyRegs src acc ctrB tmp cm t0 t1 t2 st cf := by
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true, List.nodup_ofFn, List.mem_ofFn] at hreg hst
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c1, c2, c3, c4, c5⟩,
    ⟨d1, d2, d3, d4⟩, ⟨e1, e2, e3⟩, ⟨f1, f2⟩, g1⟩, hinj, hX⟩ := hreg
  have hX' : ∀ x, (x = src ∨ x = acc ∨ x = ctrB ∨ x = tmp ∨ x = t0 ∨ x = t1 ∨ x = t2 ∨ x = cm) →
      ∀ j, cf j ≠ x := fun x hx j e => hX x hx (cf j) ⟨j, rfl⟩ e.symm
  have hst' : ∀ j, cf j ≠ st := fun j e => hst.2 ⟨j, e⟩
  exact {
    cf_inj := hinj
    cf_ne := fun j => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hX' cm (by simp) j, hX' t0 (by simp) j, hX' t1 (by simp) j, hX' t2 (by simp) j,
        hX' acc (by simp) j⟩
    cf_st := hst'
    cm_st := Ne.symm hst.1
    nd := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨Ne.symm e3, Ne.symm f2, Ne.symm g1, Ne.symm b6⟩, ⟨e1, e2, Ne.symm b3⟩,
        ⟨f1, Ne.symm b4⟩, Ne.symm b5⟩
    cf_src := fun j => hX' src (by simp) j
    cf_ctr := fun j => hX' ctrB (by simp) j
    cf_tmp := fun j => hX' tmp (by simp) j
    src_acc := a1
    src_ctr := a2
    src_tmp := a3
    acc_ctr := b1
    acc_tmp := b2
    ctr_tmp := c1
    src_cm := a7
    src_t0 := a4
    src_t1 := a5
    src_t2 := a6
    ctr_cm := c5
    ctr_t0 := c2
    ctr_t1 := c3
    ctr_t2 := c4
    tmp_cm := d4
    tmp_t0 := d1
    tmp_t1 := d2
    tmp_t2 := d3 }

/-- **Key pass.** On the stream `l` of `M = rectSize` records of `B ≥ 1` symbols in register
`src` (record `j` at rank `j`), with the field counter `cf` at index `0`, the mask
`selMask K ρ (f - 1)` in `cm`, and empty `acc`, `tmp`, `t0`, `t1`, `t2`, the key pass leaves
in `src` the keyed records `keyRecs k π_T l`: record `j` preceded by the `k` bits of
`π_T j = enc σ (idealT ((enc σ)⁻¹ j))`, least significant first. Every other register ends as it
started. At most `106 M (B + k + 1) + 4 k + 37` steps. -/
theorem keyPass_exec (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (K ρ f : ℕ) (σ : Equiv.Perm (Fin 3))
    {src acc ctrB tmp cm t0 t1 t2 st : Fin T} {cf : Fin 8 → Fin T}
    (hreg : ([src, acc, ctrB, tmp, t0, t1, t2, cm] ++ List.ofFn cf).Nodup)
    (hst : st ∉ cm :: List.ofFn cf) {B : ℕ} (hB : 1 ≤ B) (l : List (List (Fin (A + 4))))
    (hl : l.length = rectSize N₀ N₁ N₂ N₃ L) (hlB : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = l.flatten) (hacc : S.R acc = [])
    (hctr : (S.R ctrB).length = B) (htmp : S.R tmp = []) (ht0 : S.R t0 = [])
    (ht1 : S.R t1 = []) (ht2 : S.R t2 = []) (hcm : S.R cm = binSyms L (selMask K ρ (f - 1)))
    (hcf : ∀ j, S.R (cf j) = binSyms (idxLen n₀ n₁ n₂ n₃ L rb j) 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 106 * (rectSize N₀ N₁ N₂ N₃ L * (B + keyLen n₀ n₁ n₂ n₃ L rb + 1)) +
        4 * keyLen n₀ n₁ n₂ n₃ L rb + 37 ∧
      Exec body (keyPass σ src acc ctrB tmp cm t0 t1 t2 st cf) (mk v S) m
        (mk v' { S with R := (Function.update S.R src
          (keyRecs (keyLen n₀ n₁ n₂ n₃ L rb) (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f))
            l).flatten) }) := by
  have h := KeyRegs.of_nodup hreg hst
  have hyx : slotF (σ.symm 1) ≠ slotF (σ.symm 0) := fun e => by
    have := σ.symm.injective (slotF_injective e)
    exact absurd this (by decide)
  have hlen : idxLen n₀ n₁ n₂ n₃ L rb (slotF (σ.symm 0)) =
      idxLen n₀ n₁ n₂ n₃ L rb (slotF (σ.symm 1)) := by rw [idxLen_slotF, idxLen_slotF]
  obtain ⟨v', hu, he⟩ := keyPassAt_exec body hyx h hlen (mm := selMask K ρ (f - 1)) hB l hlB v S
    hsrc hacc hctr htmp
    ⟨hcf, by rw [idxLen_slotF, hcm], ht0, ht1, ht2⟩
  rw [keyedFrom_eq_keyRecs hN₀ hR hN₁ hN₂ hN₃ K ρ f σ l hl] at he
  refine ⟨v', _, hu, ?_, he⟩
  rw [hl, sum_idxLen]
  set M := rectSize N₀ N₁ N₂ N₃ L
  set k := keyLen n₀ n₁ n₂ n₃ L rb
  have hsum : ((List.finRange 8).map (keyCost (slotF (σ.symm 1)) (idxLen n₀ n₁ n₂ n₃ L rb))).sum ≤
      9 * k + 64 := by
    rw [← Fin.sum_univ_def]
    calc ∑ j, keyCost (slotF (σ.symm 1)) (idxLen n₀ n₁ n₂ n₃ L rb) j
        ≤ ∑ j, (9 * idxLen n₀ n₁ n₂ n₃ L rb j + 8) :=
          Finset.sum_le_sum fun j _ => keyCost_le _ _ j
      _ = 9 * k + 64 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_idxLen]; simp [k]
  have hrec : keyRecCost (slotF (σ.symm 1)) (idxLen n₀ n₁ n₂ n₃ L rb) B ≤ 13 * k + 4 * B + 105 := by
    unfold keyRecCost
    rw [sum_idxLen]
    omega
  have hM := Nat.mul_le_mul_left M hrec
  nlinarith [hM]

end KeyMain

end IntegerMultBounds.MathlibTM2.Node
