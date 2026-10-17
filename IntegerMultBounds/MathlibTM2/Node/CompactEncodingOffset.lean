module
public import IntegerMultBounds.MathlibTM2.Node.CompactGeometryRecursive
import Mathlib.Tactic.Positivity.Finset


/-! Absorb an arbitrary low address offset into the native payload without moving
the symbol stream. Low address bits become the outer coefficient coordinate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Layer
noncomputable section

/-- Retain the low address digits and append the local high address. -/
def compactOffsetBits (o n low : ℕ) (high : Fin n → ZMod 2) : Fin (o+n) → ZMod 2 := fun t =>
  if ht : t.val < o then addrBits o low ⟨t.val,ht⟩ else high ⟨t.val-o,by have := t.isLt; omega⟩

lemma compactOffsetBits_high (o : ℕ) {n : ℕ} (low : ℕ) (high : Fin n → ZMod 2) (t : Fin n) :
    compactOffsetBits o n low high (Fin.natAdd o t)=high t := by
  simp only [compactOffsetBits,Fin.val_natAdd]
  rw [dite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  simp

lemma compactOffsetBits_addrBits (o n low high : ℕ) (hlow : low < 2^o) :
    compactOffsetBits o n low (addrBits n high) = addrBits (o+n) (high*2^o+low) := by
  funext t
  simp only [compactOffsetBits,addrBits]
  rw [Nat.mul_comm high,Nat.testBit_two_pow_mul_add _ hlow]
  split_ifs <;> rfl

/-- The same physical data with low address bits folded into the coefficient index. -/
def compactOffsetArray {R r o n : ℕ} (Z : ZArr (Fin R × Fin r) (o+n)) :
    ZArr (Fin R × Fin (2^o*r)) n := fun p =>
  let c := finProdFinEquiv.symm p.1.2
  Z ((p.1.1,c.2),compactOffsetBits o n c.1.val p.2)

private lemma rowCoeffs_ofFn {R r n w : ℕ} (Z : ZArr (Fin R × Fin r) n) (u : Fin R) :
    rowCoeffs w Z u = (List.ofFn fun a : Fin (2^n) =>
      List.ofFn fun c : Fin r => red w (Z ((u,c),addrBits n a.val))).flatten := by
  unfold rowCoeffs
  rw [←List.map_coe_finRange_eq_range,List.flatMap_map]
  simp only [List.flatMap_def,←List.ofFn_eq_map]

/-- Literal coefficient serialization is unchanged by folding the low address bits. -/
theorem compactOffsetArray_coeffList {R r o n w : ℕ} (Z : ZArr (Fin R × Fin r) (o+n)) :
    coeffList w (compactOffsetArray Z)=coeffList w Z := by
  rw [coeffList_eq_rows,coeffList_eq_rows]
  apply List.flatMap_congr
  intro u _
  rw [rowCoeffs_ofFn,rowCoeffs_ofFn]
  have he : 2^(o+n)=2^n*2^o := by rw [pow_add,Nat.mul_comm]
  rw [List.ofFn_congr he,List.ofFn_mul]
  simp only [List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext hi
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext lo
  apply congrArg List.ofFn
  funext c
  simp only [compactOffsetArray]
  have hpair : finProdFinEquiv.symm (⟨lo.val*r+c.val,by nlinarith [lo.isLt,c.isLt]⟩ : Fin (2^o*r)) = (lo,c) := by
    apply finProdFinEquiv.injective
    simp only [Equiv.apply_symm_apply,finProdFinEquiv]
    apply Fin.ext
    change lo.val*r+c.val=c.val+r*lo.val
    ring
  rw [hpair,compactOffsetBits_addrBits o n lo.val hi.val lo.isLt]
  rfl

/-- The actual encoded symbol list requires no permutation or copy for the reshape. -/
theorem compactOffsetArray_encZ {A R r o n w : ℕ} (Z : ZArr (Fin R × Fin r) (o+n)) :
    encZ A w (compactOffsetArray Z)=encZ A w Z := by
  rw [encZ,compactOffsetArray_coeffList]
  rfl


/-- Shift a local selected-bit placement above the folded low address field. -/
def compactOffsetEmbedding (o : ℕ) {d n : ℕ} (e : Fin d → Fin n) : Fin d → Fin (o+n) :=
  fun i => Fin.natAdd o (e i)

lemma compactOffsetEmbedding_injective (o : ℕ) {d n : ℕ} {e : Fin d → Fin n}
    (he : Function.Injective e) : Function.Injective (compactOffsetEmbedding o e) := by
  intro i j hij
  apply he
  apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [compactOffsetEmbedding,Fin.val_natAdd] at hh
  omega

/-- Local XOR commutes with adjoining every low spectator bit. -/
theorem compactOffsetBits_sxMap {o n k : ℕ} (e : Fin (m*k) → Fin n)
    (he : Function.Injective e) (x y : Fin m) (low : ℕ) (high : Fin n → ZMod 2) :
    sxMap (compactOffsetEmbedding o e) x y (compactOffsetBits o n low high) =
      compactOffsetBits o n low (sxMap e x y high) := by
  have hei := compactOffsetEmbedding_injective o he
  funext t
  by_cases ht : ∃ c : Fin k, t=compactOffsetEmbedding o e (bitIdx y c)
  · obtain ⟨c,rfl⟩ := ht
    rw [sxMap_apply_y hei]
    simp only [compactOffsetEmbedding,compactOffsetBits_high,sxMap_apply_y he]
  · rw [sxMap_apply_ne hei x y _ t (fun c hc => ht ⟨c,hc.symm⟩)]
    by_cases hlo : t.val < o
    · simp only [compactOffsetBits,dite_eq_left hlo]
    · let i : Fin n := ⟨t.val-o,by have := t.isLt; omega⟩
      have hti : t=Fin.natAdd o i := by apply Fin.ext; simp only [Fin.val_natAdd,i]; omega
      rw [hti,compactOffsetBits_high,compactOffsetBits_high]
      symm
      apply sxMap_apply_ne he
      intro c hc
      apply ht
      refine ⟨c,?_⟩
      rw [hti,←hc]
      rfl

/-- Folding low bits into coefficients commutes with the live `pullM` slot XOR. -/
theorem compactOffsetArray_pullM {R r o n k : ℕ} (e : Fin (m*k) → Fin n)
    (he : Function.Injective e) (x y : Fin m) (Z : ZArr (Fin R × Fin r) (o+n)) :
    compactOffsetArray (pullM (compactOffsetEmbedding o e) (sxXorCol x y) Z) =
      pullM e (sxXorCol x y) (compactOffsetArray Z) := by
  funext p
  change Z ((p.1.1,(finProdFinEquiv.symm p.1.2).2),
      sxMap (compactOffsetEmbedding o e) x y (compactOffsetBits o n (finProdFinEquiv.symm p.1.2).1.val p.2)) =
    Z ((p.1.1,(finProdFinEquiv.symm p.1.2).2),
      compactOffsetBits o n (finProdFinEquiv.symm p.1.2).1.val (sxMap e x y p.2))
  rw [compactOffsetBits_sxMap e he]

/-- The unchanged executor on the reduced address width produces the exact original
stream action at the shifted selected bits. -/
theorem compactOffsetArray_encZ_pullM {A R r o n k w : ℕ} (e : Fin (m*k) → Fin n)
    (he : Function.Injective e) (x y : Fin m) (Z : ZArr (Fin R × Fin r) (o+n)) :
    encZ A w (pullM e (sxXorCol x y) (compactOffsetArray Z)) =
      encZ A w (pullM (compactOffsetEmbedding o e) (sxXorCol x y) Z) := by
  rw [←compactOffsetArray_pullM e he,compactOffsetArray_encZ]

/-- The expanded payload is exactly the complete folded low-address block. -/
theorem compactOffset_payload (o r w : ℕ) : 3*((2^o*r)*w) = 2^o*(3*(r*w)) := by ring

/-- Folding spectators changes neither the native bit volume nor the encoded volume. -/
theorem compactOffset_volume (R r o n w : ℕ) :
    (R*2^n)*(3*((2^o*r)*w)) = (R*2^(o+n))*(3*(r*w)) := by rw [pow_add]; ring

/-- Physical selected indices include the entire low offset in the original address. -/
theorem compactOffsetEmbedding_reserved_val {s : Machine.CompactGadgetReservationShape.Shape}
    {n a₀ k ρ left right : ℕ} (layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (o : ℕ) (i : Fin (m*k)) :
    (compactOffsetEmbedding o (compactRecursiveBits layout) i).val = o+a₀+ρ+s.chunk*i.val := by
  simp only [compactOffsetEmbedding,Fin.val_natAdd,compactRecursiveBits]
  omega

end
end IntegerMultBounds.MathlibTM2.Node
