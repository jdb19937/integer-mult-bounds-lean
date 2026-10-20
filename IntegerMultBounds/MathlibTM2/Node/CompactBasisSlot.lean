module

public import IntegerMultBounds.MathlibTM2.Node.CompactSlotCost
public import IntegerMultBounds.MathlibTM2.Node.CompactEncodingOffset
import IntegerMultBounds.MathlibTM2.Fast.ParamMachine

/-!
# One compact slot operation

`compactBasisSlot_exec`: from the unary descriptor registers of a compact layout and the stream
of an array `Z` with `o` low address bits, the compact slot XOR of the slots `x` and `y`
(`cxSlotProg`) leaves the stream of `pullM (compactOffsetEmbedding o bits) (sxXorCol x y) Z`
within `compactBasisSlotCost` steps. It works on the array with the `o` low bits folded into the
coefficients (`compactOffsetArray`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)

noncomputable section

variable {s : Shape} {T Q K : ℕ} {U P : Type}

/-- The descriptor values of a compact slot operation. -/
def compactDescriptorBankInputs {n a₀ k ρ left right : ℕ}
    (_layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (o R r w : ℕ) (x y : Fin m) : Fin 16 → ℕ :=
  ![s.chunk*(m*k),s.chunk,o+a₀,o,s.H+s.B,s.active,o+n,s.bits,R,r,w,
    x.val,y.val,s.axes,s.guard,ρ]

lemma compactSlot_volume {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (rowCount : ℕ) :
    (2^(n-s.bits)*rowCount)*s.recordWidth = (rowCount*2^n)*s.payload := by
  unfold Shape.recordWidth
  rw [show (2^(n-s.bits)*rowCount)*(2^s.bits*s.payload) =
    (rowCount*(2^(n-s.bits)*2^s.bits))*s.payload by ring]
  rw [←pow_add,Nat.sub_add_cancel layout.totalFits]

/-- The control states of the compact slot XOR. -/
abbrev compactRuntimeStates : ℕ := swapStates cxHd cxPay cxHd_inj

/-- The work registers of the compact slot XOR: the registers of the core and two banks. -/
inductive CxSlotReg where
  | core (x : CxReg)
  | bank (c : Fin 2) (j : Fin (swapT 6))
  deriving DecidableEq, Fintype

/-- The parameter conditions of a compact slot operation on `rows` rows of width `k`. -/
structure CompactSlotPacked (s : Shape) (k rows D : ℕ) : Prop where
  guard : 2 ≤ s.guard
  chunk : s.guard + 3 ≤ s.chunk
  record : s.bits + rows.log2 + 2 ≤ s.payload
  density : cxDensity s.chunk s.guard (k - 1) * ((s.bits + rows.log2 + 2 : ℕ) : ℝ) ≤ D

/-- The parameter conditions of the compact slot operations of a layout on `R` rows. -/
abbrev CompactLayoutPacked {n a₀ k ρ left right : ℕ}
    (_layout : CompactRecursiveLayout s n a₀ k ρ left right) (R D : ℕ) : Prop :=
  CompactSlotPacked s k (2^(n-s.bits)*R) D

/-- The numbers of the compact slot XOR of a layout. -/
def compactSlotData {n a₀ k ρ left right : ℕ}
    (_layout : CompactRecursiveLayout s n a₀ k ρ left right) (rowCount o r w : ℕ) (x y : Fin m) :
    CxData :=
  ⟨s.chunk, ρ, s.guard, k, a₀, n, s.H + s.B + s.active * s.chunk, rowCount, r * w * 2 ^ o, x, y⟩

/-- The program does not read the numbers beyond the slots. -/
def CxData.ofSlots (x y : Fin m) : CxData := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, x, y⟩

lemma compactSlotData_ok {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) {rowCount o r w : ℕ} {x y : Fin m}
    (hxy : x ≠ y) (hG : 1 ≤ s.guard) {D : ℕ}
    (hp : CompactSlotPacked s k (2^(n-s.bits)*rowCount) D) (hr : 0 < rowCount)
    (hpayload : s.payload = 2^o*(3*(r*w))) :
    (compactSlotData layout rowCount o r w x y).OK := by
  have hk := layout.positiveWidth
  have hax := layout.widthFits
  have hlow := layout.lowReserve
  have hact := layout.active
  have hbits := layout.totalFits
  have hH : (k - 1) * s.guard ≤ s.H := by
    unfold Shape.H CompactGadgetReservationCapacity.capacity
    exact Nat.mul_le_mul_right _ (by omega)
  have hactK : s.active * s.chunk = left * s.chunk + m * (k * s.chunk) + right * s.chunk := by
    rw [hact]; ring
  have hB : 0 < s.payload := by have := hp.record; omega
  refine ⟨layout.selectedFits, hk, hG, by show s.guard + 1 < s.chunk; have := hp.chunk; omega, hxy,
    ?_, ?_, ?_, hr, ?_⟩
  · show (k - 1) * s.guard ≤ a₀
    omega
  · show a₀ + m * (k * s.chunk) ≤ s.H + s.B + s.active * s.chunk
    omega
  · show s.H + s.B + s.active * s.chunk + 2 * ((k - 1) * s.guard) ≤ n
    unfold Shape.bits at hbits
    omega
  · show 1 ≤ r * w * 2 ^ o
    rw [hpayload] at hB
    have : 0 < r * w := by
      rcases Nat.eq_zero_or_pos (r * w) with h | h
      · rw [h] at hB; simp at hB
      · exact h
    exact Nat.mul_pos this (Nat.two_pow_pos _)

variable (ι : CxSlotReg → Fin T) (str : Fin T)

/-- The core registers: `src` is the stream register. -/
def cxSlotRegs : CxReg → Fin T := fun x => if x = .src then str else ι (.core x)

/-- The interchange banks. -/
def cxSlotBank : Fin 2 → Fin (swapT 6) → Fin T := fun c j => ι (.bank c j)

/-- The descriptor registers of the setup inputs. -/
def cxSlotIdx : Fin 11 → Fin 30 := ![1, 15, 14, 2, 3, 4, 5, 6, 8, 9, 10]

lemma cxSlotIdx_injective : Function.Injective cxSlotIdx := by decide

/-- The unary inputs of the setup among the descriptor registers. -/
def cxSlotInp (e : Fin 30 → Fin T) (ell : Fin T) : Fin 12 → Fin T :=
  Fin.lastCases ell fun i => e (cxSlotIdx i)

variable {ι str}

lemma cxSlotBanks (hι : Function.Injective ι) (hstr : ∀ j, ι j ≠ str) :
    Banks (cxSlotRegs ι str) (cxSlotBank ι) where
  inj c := fun a b e => by simpa using hι e
  ne c j x := by
    unfold cxSlotRegs cxSlotBank
    split_ifs
    · exact hstr _
    · exact fun e => by simpa using hι e

/-- The program of one compact slot operation. -/
def compactBasisSlotProg (hQ : compactRuntimeStates ≤ Q) (hι : Function.Injective ι)
    (hstr : ∀ j, ι j ≠ str) (hT : swapT 6 ≤ T) (e : Fin 30 → Fin T) (ell : Fin T)
    (x y : Fin m) : Pr P T Q (prime+K) U :=
  if hA : 4 ≤ prime+K then
    cxSlotProg (ι := cxSlotRegs ι str) (bank := cxSlotBank ι) (inp := cxSlotInp e ell)
      (CxData.ofSlots x y) hA (cxSlotBanks hι hstr) hQ hT
  else .act .done

/-- The step bound of one compact slot operation. -/
def compactBasisSlotCost (T D : ℕ) {n a₀ k ρ left right : ℕ}
    (_layout : CompactRecursiveLayout s n a₀ k ρ left right) (rowCount o r w : ℕ) : ℕ :=
  ⌈CxData.cxSlotConst T D * (rowCount * 2 ^ n * (n + (sxBits rowCount).length + r * w * 2 ^ o) : ℕ) *
    ((max 1 ((k - 1) * s.guard) : ℕ) : ℝ) ^ Parameters.tau⌉₊

/-- The row bits are paid by the row count of the stage. -/
lemma compactSlot_rowBits {n bits R : ℕ} (hn : bits ≤ n) (hR : 0 < R) :
    n + (sxBits R).length ≤ bits + (2 ^ (n - bits) * R).log2 + 1 := by
  rw [TableVM.pm_length_sxBits]
  have hs : 0 < Nat.size R := Nat.size_pos.2 hR
  have h1 : 2 ^ (Nat.size R - 1) ≤ R := Nat.lt_size.1 (by omega)
  have h2 : n - bits + (Nat.size R - 1) ≤ (2 ^ (n - bits) * R).log2 := by
    rw [Nat.le_log2 (Nat.mul_pos (Nat.two_pow_pos _) hR).ne', pow_add]
    exact Nat.mul_le_mul_left _ h1
  omega

variable (body : P → Pr P T Q (prime+K) U) in
/-- **One compact slot operation.** -/
theorem compactBasisSlot_exec {n a₀ k ρ left right o rowCount r w : ℕ}
    (hQ : compactRuntimeStates ≤ Q) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (e : Fin 30 → Fin T) (he : Function.Injective e) (ell : Fin T)
    (hell : ∀ i, ell ≠ e i) (hebank : ∀ i j, e i ≠ ι j) (hestr : ∀ i, e i ≠ str)
    (hellι : ∀ j, ell ≠ ι j) (hellstr : ell ≠ str) (hstr : ∀ j, ι j ≠ str)
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y)
    (hG : 1 ≤ s.guard) (hr : 0 < rowCount) (hA : 4 ≤ prime+K)
    (hpayload : s.payload = 2^o*(3*(r*w))) (D : ℕ)
    (hp : CompactSlotPacked s k (2^(n-s.bits)*rowCount) D)
    (Z : ZArr (Fin rowCount × Fin r) (o+n))
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j, S.L j = []) (hbank : ∀ j, S.R (ι j) = [])
    (hellen : (S.R ell).length = s.chunk*k)
    (hR : S.R str = encZ (prime+K) w Z)
    (hin : ∀ i : Fin 16, i ≠ 0 → i ≠ 11 → i ≠ 12 →
      (S.R (e (Fin.castAdd 14 i))).length = compactDescriptorBankInputs layout o rowCount r w x y i) :
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ compactBasisSlotCost T D layout rowCount o r w ∧
      Exec body (compactBasisSlotProg hQ hι hstr hT e ell x y) (mk v S) steps
        (mk v' {S with R := Function.update S.R str (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (sxXorCol x y) Z))}) := by
  set d := compactSlotData layout rowCount o r w x y with hdd
  have hd : d.OK := compactSlotData_ok layout hxy hG hp hr hpayload
  -- the registers
  have hcore : ∀ a b : CxReg, cxSlotRegs ι str a = cxSlotRegs ι str b → a = b := by
    intro a b h
    unfold cxSlotRegs at h
    split_ifs at h with ha hb hb
    · rw [ha, hb]
    · exact absurd h.symm (hstr _)
    · exact absurd h (hstr _)
    · simpa using hι h
  have hall : Function.Injective (cxAll (cxSlotRegs ι str) (cxSlotBank ι) (cxSlotInp e ell)) := by
    have hreg : ∀ (a : CxReg) (i : Fin 12), cxSlotRegs ι str a ≠ cxSlotInp e ell i := by
      intro a i
      induction i using Fin.lastCases with
      | last => unfold cxSlotRegs; simp only [cxSlotInp, Fin.lastCases_last]; split_ifs
                · exact hellstr.symm
                · exact (hellι _).symm
      | cast i => unfold cxSlotRegs; simp only [cxSlotInp, Fin.lastCases_castSucc]; split_ifs
                  · exact (hestr _).symm
                  · exact (hebank _ _).symm
    have hbk : ∀ (c : Fin 2) (j : Fin (swapT 6)) (i : Fin 12),
        cxSlotBank ι c j ≠ cxSlotInp e ell i := by
      intro c j i
      induction i using Fin.lastCases with
      | last => simp only [cxSlotInp, Fin.lastCases_last]; exact (hellι _).symm
      | cast i => simp only [cxSlotInp, Fin.lastCases_castSucc]; exact (hebank _ _).symm
    have hinp : Function.Injective (cxSlotInp e ell) := by
      intro a b h
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b => simp only [cxSlotInp, Fin.lastCases_last, Fin.lastCases_castSucc] at h
                    exact absurd h (hell _)
      | cast a =>
        induction b using Fin.lastCases with
        | last => simp only [cxSlotInp, Fin.lastCases_last, Fin.lastCases_castSucc] at h
                  exact absurd h.symm (hell _)
        | cast b => simp only [cxSlotInp, Fin.lastCases_castSucc] at h
                    rw [cxSlotIdx_injective (he h)]
    have hb := cxSlotBanks hι hstr
    rintro ((a | ⟨c, k⟩) | i) ((b | ⟨c', k'⟩) | j) h <;>
      simp only [cxAll, Sum.elim_inl, Sum.elim_inr, cxSetReg] at h
    · rw [hcore a b h]
    · exact absurd h.symm (hb.ne _ _ _)
    · exact absurd h (hreg _ _)
    · exact absurd h (hb.ne _ _ _)
    · have e1 := hι h
      simp only [CxSlotReg.bank.injEq] at e1
      obtain ⟨rfl, e2⟩ := e1
      have hk : k = k' := cxHd_inj (Fin.ext (by simpa [reg_val] using congrArg Fin.val e2))
      rw [hk]
    · exact absurd h (hbk _ _ _)
    · exact absurd h.symm (hreg _ _)
    · exact absurd h.symm (hbk _ _ _)
    · rw [hinp h]
  have hbank' : ∀ c c' j j', cxSlotBank ι c j = cxSlotBank ι c' j' → c = c' := by
    intro c c' j j' h
    have := hι h
    simp only [CxSlotReg.bank.injEq] at this
    exact this.1
  have h0 : ∀ x : CxSet, x ≠ .reg .src →
      S.R (cxSetReg (cxSlotRegs ι str) (cxSlotBank ι) x) = [] := by
    rintro (a | ⟨c, k⟩) ha
    · have : a ≠ .src := fun h => ha (h ▸ rfl)
      simp only [cxSetReg, cxSlotRegs, this, ↓reduceIte]
      exact hbank _
    · exact hbank _
  have hin' : CxSetupIn d (cxSlotInp e ell) S.R o (s.H + s.B) s.active r w := by
    refine ⟨hin 1 (by decide) (by decide) (by decide), hin 15 (by decide) (by decide) (by decide),
      hin 14 (by decide) (by decide) (by decide), hin 2 (by decide) (by decide) (by decide),
      hin 3 (by decide) (by decide) (by decide), hin 4 (by decide) (by decide) (by decide),
      hin 5 (by decide) (by decide) (by decide), hin 6 (by decide) (by decide) (by decide),
      hin 8 (by decide) (by decide) (by decide), hin 9 (by decide) (by decide) (by decide),
      hin 10 (by decide) (by decide) (by decide), ?_, rfl, rfl⟩
    show (S.R ell).length = k * s.chunk
    rw [hellen, Nat.mul_comm]
  have hsrc : S.R (cxSlotRegs ι str .src) = encZ (prime + K) w (compactOffsetArray Z) := by
    simp only [cxSlotRegs, ↓reduceIte]
    rw [hR, compactOffsetArray_encZ]
  obtain ⟨v', m', hu, hm, hex⟩ := cxSlotRun_exec (ι := cxSlotRegs ι str) (bank := cxSlotBank ι)
    (inp := cxSlotInp e ell) hall (cxSlotBanks hι hstr) hbank' body hd h0 (fun c j => hbank _)
    hin' (r := 2 ^ o * r) (w := w) (by show r * w * 2 ^ o = 2 ^ o * r * w; ring)
    (compactOffsetArray Z) hsrc (compactRecursiveBits_injective layout) (fun i => rfl) hA hQ hT
    v S hL rfl
  -- the cost
  have hbl : ∀ c, (∑ j, (cxFile (cxSlotRegs ι str) (cxSlotBank ι) d 41 S.R
      (cxSlotBank ι c j)).length) ≤ 5 * d.setupStep o (s.H + s.B) s.active r w :=
    cx_bankLen_le hall (cxSlotBanks hι hstr) hbank' hd o _ _ r w h0 (fun c j => hbank _)
  have hdens : cxDensity d.K d.G (d.k - 1) * ((d.n + d.rb + 1 : ℕ) : ℝ) ≤ D := by
    refine le_trans ?_ hp.density
    refine mul_le_mul_of_nonneg_left ?_ (cxDensity_nonneg _ _ _)
    have := compactSlot_rowBits (R := rowCount) layout.totalFits hr
    exact_mod_cast (show d.n + d.rb + 1 ≤ s.bits + (2 ^ (n - s.bits) * rowCount).log2 + 2 by
      show n + (sxBits rowCount).length + 1 ≤ _; omega)
  have hcost := hd.slotRun_cost_le (o := o) (hB := s.H + s.B) (act := s.active) (cr := r)
    (cw := w) rfl rfl T D _ hbl hdens
  refine ⟨v', m', hu, ?_, ?_⟩
  · unfold compactBasisSlotCost
    have := (hm.trans hcost).trans (Nat.le_ceil _)
    exact_mod_cast this
  · rw [← compactOffsetArray_encZ_pullM (compactRecursiveBits layout)
      (compactRecursiveBits_injective layout) x y Z]
    unfold compactBasisSlotProg
    rw [dite_eq_left hA]
    exact hex

end

end IntegerMultBounds.MathlibTM2.Node
