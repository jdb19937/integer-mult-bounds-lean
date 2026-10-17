module

public import IntegerMultBounds.MathlibTM2.Node.CompactGeometryRecursive
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseRun
import Mathlib.Tactic.Positivity.Finset

/-! Exact three-bit serialization of live coefficient streams for native compact stages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Stack
open CompactGadgetReservationShape (Shape)
noncomputable section

private def compactBitRecords {R r n : ℕ} (A w : ℕ) (Z : ZArr (Fin R × Fin r) n) :=
  (recList w Z).map (fun rec => toBits (recSyms A w rec))

private theorem compactBitRecords_flatten {A w R r n : ℕ} (Z : ZArr (Fin R × Fin r) n) :
    (compactBitRecords A w Z).flatten = toBits (encZ A w Z) := by
  rw [sx_encZ_eq_flatten, toBits_flatten]
  simp only [compactBitRecords, List.map_map, Function.comp_def]

private theorem compactBitRecords_facts {A w R r n : ℕ} (hA : 4 ≤ A)
    (Z : ZArr (Fin R × Fin r) n) :
    (compactBitRecords A w Z).length = R * 2^n ∧
    ∀ rec ∈ compactBitRecords A w Z, rec.length = 3*(r*w) := by
  obtain ⟨hl, hb, _⟩ := sx_recSyms_facts (w:=w) hA Z
  constructor
  · simp [compactBitRecords, length_recList]
  · intro rec hrec
    simp only [compactBitRecords, List.mem_map] at hrec
    obtain ⟨v, hv, rfl⟩ := hrec
    rw [length_toBits, hb _ (List.mem_map.mpr ⟨v,hv,rfl⟩)]

theorem compactEncoding_length {A w R r n : ℕ} (hA : 4 ≤ A)
    (Z : ZArr (Fin R × Fin r) n) :
    (toBits (encZ A w Z)).length = (R*2^n)*(3*(r*w)) := by
  rw [←compactBitRecords_flatten, length_flatten_uniform _ (compactBitRecords_facts hA Z).2,
    (compactBitRecords_facts hA Z).1]

private theorem addrNum_mod (n : ℕ) (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (a : ℕ) :
    addrNum σ (a % 2^n) = addrNum σ a := by
  have h : addrBits n (a % 2^n) = addrBits n a := by
    funext t
    simp only [addrBits, Nat.testBit_mod_two_pow, t.isLt, decide_true, Bool.true_and]
  simp only [addrNum, h]

/-- A pulled live stream changes the address while retaining its row and all three-bit
payload positions. -/
theorem compactEncoding_pull_getElem {A w R r n : ℕ} (hA : 4 ≤ A)
    (Z : ZArr (Fin R × Fin r) n)
    (σ : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (z : ℕ)
    (hz : z < (R*2^n)*(3*(r*w))) :
    (toBits (encZ A w (pullAddr σ Z)))[z]? =
      (toBits (encZ A w Z))[
        ((z/(3*(r*w))/2^n)*2^n + addrNum σ (z/(3*(r*w))))*(3*(r*w)) + z%(3*(r*w))]? := by
  let p := 3*(r*w)
  have hp : 0 < p := by
    by_contra h
    have he : p = 0 := by omega
    change z < (R*2^n)*p at hz
    rw [he, Nat.mul_zero] at hz
    omega
  have hq : z/p < R*2^n := (Nat.div_lt_iff_lt_mul hp).mpr hz
  have hu : z/p/2^n < R := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by simpa [Nat.mul_comm] using hq)
  have ha : z/p%2^n < 2^n := Nat.mod_lt _ (by positivity)
  have hi : z%p < p := Nat.mod_lt _ hp
  have he : z = (z/p)*p+z%p := by simpa only [Nat.mul_comm] using (Nat.div_add_mod z p).symm
  rw [←compactBitRecords_flatten, ←compactBitRecords_flatten]
  rw [he, flatten_getElem?_uniform _ (compactBitRecords_facts hA (pullAddr σ Z)).2 _ _ hi]
  rw [←he]
  rw [flatten_getElem?_uniform _ (compactBitRecords_facts hA Z).2 _ _ hi]
  have hrec := recList_pull (w:=w) σ Z (z/p/2^n) hu (z/p%2^n) ha
  have hnum : 2^n*(z/p/2^n)+z/p%2^n = z/p := Nat.div_add_mod (z/p) (2^n)
  simp only [hnum, addrNum_mod] at hrec
  have hq' : (z/p/2^n)*2^n+addrNum σ (z/p) < R*2^n := by
    have := addrNum_lt σ (z/p)
    nlinarith
  have hqL : z/p < (recList w (pullAddr σ Z)).length := by simpa only [length_recList] using hq
  have hqR : (z/p/2^n)*2^n+addrNum σ (z/p) < (recList w Z).length := by simpa only [length_recList] using hq'
  change ((compactBitRecords A w (pullAddr σ Z))[z/p]?.bind fun rec => rec[z%p]?) =
    ((compactBitRecords A w Z)[(z/p/2^n)*2^n+addrNum σ (z/p)]?.bind fun rec => rec[z%p]?)
  simp only [compactBitRecords, List.getElem?_map,
    List.getElem?_eq_getElem hqL, List.getElem?_eq_getElem hqR, Option.map_some, Option.bind_some]
  congr 2
  simpa only [Nat.mul_comm] using congrArg (recSyms A w) hrec

/-- Every encoded coefficient stream has a native Boolean array representation when
its literal volume matches. No padding or width bound is inferred here. -/
theorem compactEncoding_exists {s : Shape} {A w R r n rows : ℕ} (hA : 4 ≤ A)
    (Z : ZArr (Fin R × Fin r) n)
    (hvolume : rows*s.recordWidth = (R*2^n)*(3*(r*w))) :
    ∃ array : ActiveRepairLayoutRecordsData.Array s rows,
      List.ofFn (fun i => (bitSymbol (array i) : Fin (A+4))) = toBits (encZ A w Z) := by
  obtain ⟨array, h⟩ := exists_ofFn_bits (toBits (encZ A w Z))
    (fun _ h => mem_toBits h) ((compactEncoding_length hA Z).trans hvolume.symm)
  exact ⟨array,h.symm⟩

/-- The actual native result reads from its actual selected destination. -/
theorem compactRuntime_result_read {s : Shape} (d : ActivePrefixStageFullData.Inputs s)
    (array : ActiveRepairLayoutRecordsData.Array s d.rows)
    (i : ActivePrefixStageFullSelected.Address d) :
    ActivePrefixStageRuntimeData.result d array (ActivePrefixDirtyControlGlobalSwap.index s
      (ActivePrefixStageFullSelected.geometry d) i) =
    array (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageRuntimeSelected.destination d i)) := by
  have h := ActivePrefixStageRuntimeSelected.entry d (ActivePrefixStageRuntimeData.result d array) i
  rw [ActivePrefixStageRuntimeInverseRun.involutive d array] at h
  exact h.symm

/-- The executed native result is exactly the bit encoding of the live slot XOR.
The input representation and physical payload/volume equalities are explicit. -/
theorem compactEncoding_runtime_result
    {s : Shape} {A w R r n a₀ k ρ left right rows : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (x y : Fin m) (hxy : x ≠ y)
    (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk)
    (hr : 0 < rows) (hrecord : s.bits+1 ≤ s.payload)
    (hA : 4 ≤ A) (hpayload : s.payload = 3*(r*w))
    (hvolume : rows*s.recordWidth = (R*2^n)*s.payload)
    (Z : ZArr (Fin R × Fin r) n)
    (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hencoding : List.ofFn (fun i => (bitSymbol (array i) : Fin (A+4))) = toBits (encZ A w Z)) :
    List.ofFn (fun i => (bitSymbol (ActivePrefixStageRuntimeData.result
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) array i) : Fin (A+4))) =
      toBits (encZ A w (pullM (compactRecursiveBits layout) (sxXorCol x y) Z)) := by
  let d := compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord
  let idx := ActivePrefixDirtyControlGlobalSwap.index (rows:=rows) s (ActivePrefixStageFullSelected.geometry d)
  have hidx : Function.Bijective idx := CompactActiveTargetLayout.index_bijective _ _ _ _ _ _ _ _
  have hp : 0 < s.payload := by omega
  change List.ofFn (fun i : Fin (rows*s.recordWidth) => (bitSymbol (ActivePrefixStageRuntimeData.result d array i) : Fin (A+4))) =
    toBits (encZ A w (pullAddr (sxMap (compactRecursiveBits layout) x y) Z))
  apply List.ext_getElem?
  intro z
  by_cases hz : z < rows*s.recordWidth
  · obtain ⟨i, hi⟩ := hidx.2 ⟨z,hz⟩
    have hiz : (idx i).val = z := congrArg Fin.val hi
    have ha : z/s.payload%2^n < 2^n := Nat.mod_lt _ (by positivity)
    have hpos : z%s.payload < s.payload := Nat.mod_lt _ hp
    have hdecomp : (idx i).val =
        ((z/s.payload/2^n)*2^n+z/s.payload%2^n)*s.payload+z%s.payload := by
      rw [hiz]
      have h₁ := Nat.div_add_mod (z/s.payload) (2^n)
      have h₂ := Nat.div_add_mod z s.payload
      rw [Nat.mul_comm (z/s.payload/2^n) (2^n), h₁]
      simpa only [Nat.mul_comm] using h₂.symm
    have hd := compactRecursiveNative_serialized_rank layout x y hxy rows hG hGK hr hrecord
      i (z/s.payload/2^n) (z/s.payload%2^n) (z%s.payload) ha hpos hdecomp
    simp only [addrNum_mod] at hd
    have hz' : z < (R*2^n)*(3*(r*w)) := by simpa only [hvolume,hpayload] using hz
    rw [compactEncoding_pull_getElem hA Z _ z hz']
    simp only [←hpayload]
    rw [←hd]
    have he := congrArg (fun l : List (Fin (A+4)) => l[(idx (ActivePrefixStageRuntimeSelected.destination d i)).val]?) hencoding
    simp only [List.getElem?_ofFn, dite_eq_left (idx (ActivePrefixStageRuntimeSelected.destination d i)).isLt] at he
    rw [←hiz]
    simp only [List.getElem?_ofFn, dite_eq_left (idx i).isLt]
    change some (bitSymbol (ActivePrefixStageRuntimeData.result d array (idx i))) = _
    calc
      _ = some (bitSymbol (array (idx (ActivePrefixStageRuntimeSelected.destination d i)))) :=
        congrArg (fun b => some (bitSymbol b : Fin (A+4))) (compactRuntime_result_read d array i)
      _ = _ := he
  · rw [List.getElem?_eq_none (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hz),
      List.getElem?_eq_none (by rw [compactEncoding_length hA,←hpayload,←hvolume]; omega)]

end
end IntegerMultBounds.MathlibTM2.Node
