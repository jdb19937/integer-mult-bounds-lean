module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimePower
public import IntegerMultBounds.Machine.RecursiveChildHeaderHandoff
public import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-!
# Cross views at runtime atom positions

Stage 1 prepares the headers of the cross view `child q 1 b v i j` (H field `i` against D field
`j`, `RecursiveCrossPrepare`) with `i` and `j` constants of the program: its four powers
`q^(i b)`, `q^((m-1-i) b)`, `q^(j b)`, `q^((m-1-j) b)` come from
`RadixPowerMultipleDescriptor.program k`. The stage-2 adapters select one atom of each field, at
positions known only at run time, so here the four exponent multiples are descriptors: the
powers come from `RuntimePower`, the four spectator products are stage 1's own stages
(`RecursiveChildDimensions.stage5_hoare` to `stage8_hoare`), and the clean-up and header handoff
are stage 1's (`RecursiveChildHeaderHandoff.generated_hoare`). The width descriptor is the atom
width `w` and the row descriptor is copied (one role).

The bank is stage 1's 38-tape header bank followed by nine tapes (`extras`): the atom width and
the four position counters `i`, `N - 1 - i`, `j`, `N - 1 - j`, and four blank work tapes.
`prepares`: from the parent headers to the headers of `child q 1 w v i j`, with the extras
restored, in time linear in the volume.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimeCross

open IntegerMultBounds.Machine
open RecursiveInterchangeLayout (Descriptor child volume)
open SharedPlacementAlphabet (setTape)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

/-- The atom width, the four position counters, four blank work tapes. -/
def extras (ws : Fin 5 → List Bool) : Tapes 9 q :=
  ⟨![1,1,1,1,1,0,0,0,0],
   ![RadixZeroFill.encodedBinary (ws 0),RadixZeroFill.encodedBinary (ws 1),
     RadixZeroFill.encodedBinary (ws 2),RadixZeroFill.encodedBinary (ws 3),
     RadixZeroFill.encodedBinary (ws 4),fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank]⟩

/-- A 19-tape dimension bank, nineteen blank tapes and the extras. -/
def big (d : Tapes 19 q) (ws : Fin 5 → List Bool) : Tapes 47 q :=
  (d.append (SharedBank.empty 19 q)).append (extras ws)

theorem big_setTape (d : Tapes 19 q) (ws : Fin 5 → List Bool) (i : Fin 19) (f : ℤ → Fin (q+4))
    (p : ℤ) : big (setTape d i f p) ws = setTape (big d ws) (Fin.castAdd 9 (Fin.castAdd 19 i)) f p := by
  rw [big, big, SharedPlacementAlphabet.setTape_append_left, SharedPlacementAlphabet.setTape_append_left]

/-! ### Placements -/

theorem extra_setTape {s u t a : ℕ} (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (k : Fin s)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.extra e (setTape v (e (Fin.castAdd u k)) f p) = Placement.extra e v := by
  have hne : ∀ i : Fin u, e (Fin.natAdd s i) ≠ e (Fin.castAdd u k) := fun i h => by
    have := congrArg Fin.val (e.injective h)
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  unfold Placement.extra setTape
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [Function.update_of_ne (hne i)]

theorem active_setTape {s u t a : ℕ} (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (k : Fin s)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.active e (setTape v (e (Fin.castAdd u k)) f p) = setTape (Placement.active e v) k f p := by
  unfold Placement.active setTape
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases h : i = k
  all_goals first
    | (subst h; simp)
    | (have hne : e (Fin.castAdd u i) ≠ e (Fin.castAdd u k) := fun he =>
          h (Fin.castAdd_injective _ _ (e.injective he))
       simp [Function.update_of_ne hne, Function.update_of_ne h])

private theorem placed_exact {t u n r a cost : ℕ} {M : Program t r a}
    (e : Fin (t+u) ≃ Fin n) (v w : Tapes n a) (small small' : Tapes t a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

theorem power_output (ks bs : List Bool) (n : ℕ) :
    setTape (RuntimePower.input (q := q) ks bs) 3 (RadixZeroFill.encodedBinary (RadixPowerDescriptor.bits hq n)) 1 =
      RuntimePower.output hq ks bs n := by
  unfold RuntimePower.input RuntimePower.output RuntimePower.bank setTape
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [RecursiveDimensionBank.head, RecursiveDimensionBank.tape, Function.update]

/-- One runtime power placed so that its output slot is `e 3`. -/
theorem stage_power (e : Fin (9+38) ≃ Fin 47) (v : Tapes 47 q) (ks bs : List Bool) (k b : ℕ)
    (hb0 : 0 < b) (hk : Counter.value ks = k) (hb : Counter.value bs = b)
    (ck : GrowingCounterData.Canonical ks) (cb : GrowingCounterData.Canonical bs)
    (ha : Placement.active e v = RuntimePower.input ks bs) :
    HoareTime (Placement.placed (RuntimePower.program hq) e) (fun x => x = v)
      (fun x => x = setTape v (e (Fin.castAdd 38 3))
        (RadixZeroFill.encodedBinary (RadixPowerDescriptor.bits hq (k*b))) 1)
      (RuntimePower.cost (q := q) k b) :=
  placed_exact e _ _ _ _ ha
    (by rw [active_setTape, ha, power_output])
    (extra_setTape e v 3 _ _).symm
    (RuntimePower.power_hoare hq ks bs k b hb0 hk hb ck cb)

def place1 : Fin (9+38) ≃ Fin 47 where
  toFun := ![0,1,9,11,39,43,44,45,46,2,3,4,5,6,7,8,10,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,40,41,42]
  invFun := ![0,1,9,10,11,12,13,14,15,2,16,3,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,4,44,45,46,5,6,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def place2 : Fin (9+38) ≃ Fin 47 where
  toFun := ![0,1,9,12,40,43,44,45,46,2,3,4,5,6,7,8,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,41,42]
  invFun := ![0,1,9,10,11,12,13,14,15,2,16,17,3,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,4,45,46,5,6,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def place3 : Fin (9+38) ≃ Fin 47 where
  toFun := ![0,1,9,13,41,43,44,45,46,2,3,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,42]
  invFun := ![0,1,9,10,11,12,13,14,15,2,16,17,18,3,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,4,46,5,6,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def place4 : Fin (9+38) ≃ Fin 47 where
  toFun := ![0,1,9,14,42,43,44,45,46,2,3,4,5,6,7,8,10,11,12,13,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
  invFun := ![0,1,9,10,11,12,13,14,15,2,16,17,18,19,3,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,4,5,6,7,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-! ### The eight construction stages -/

section Stages

open RecursiveChildDimensions (bank prefixBits ds0 ds1 ds2 ds3 ds4 ds5 ds6 ds7 ds8)

variable (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool) (ws : Fin 5 → List Bool)
  (b : ℕ) {m : ℕ} (i j : Fin m)

theorem ds1_eq : bank (q := q) hs bs rs (ds1 hq v b i j) =
    setTape (bank hs bs rs ds0) 11 (RadixZeroFill.encodedBinary (prefixBits hq i.val b)) 1 := by
  unfold bank ds0 ds1 setTape
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp [RecursiveDimensionBank.head, RecursiveDimensionBank.tape, Function.update]

theorem ds2_eq : bank (q := q) hs bs rs (ds2 hq v b i j) =
    setTape (bank hs bs rs (ds1 hq v b i j)) 12
      (RadixZeroFill.encodedBinary (prefixBits hq (m-1-i.val) b)) 1 := by
  unfold bank ds1 ds2 setTape
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp [RecursiveDimensionBank.head, RecursiveDimensionBank.tape, Function.update]

theorem ds3_eq : bank (q := q) hs bs rs (ds3 hq v b i j) =
    setTape (bank hs bs rs (ds2 hq v b i j)) 13 (RadixZeroFill.encodedBinary (prefixBits hq j.val b)) 1 := by
  unfold bank ds2 ds3 setTape
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp [RecursiveDimensionBank.head, RecursiveDimensionBank.tape, Function.update]

theorem ds4_eq : bank (q := q) hs bs rs (ds4 hq v b i j) =
    setTape (bank hs bs rs (ds3 hq v b i j)) 14
      (RadixZeroFill.encodedBinary (prefixBits hq (m-1-j.val) b)) 1 := by
  unfold bank ds3 ds4 setTape
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp [RecursiveDimensionBank.head, RecursiveDimensionBank.tape, Function.update]

variable (hb0 : 0 < b) (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
  (hc : ∀ z, GrowingCounterData.Canonical (ws z))
  (h1 : Counter.value (ws 1) = i.val) (h2 : Counter.value (ws 2) = m-1-i.val)
  (h3 : Counter.value (ws 3) = j.val) (h4 : Counter.value (ws 4) = m-1-j.val)
include hb0 hb cb hc

include h1 in
theorem stage1 : HoareTime (Placement.placed (RuntimePower.program hq) place1)
    (fun x => x = big (bank hs bs rs ds0) ws) (fun x => x = big (bank hs bs rs (ds1 hq v b i j)) ws)
    (RuntimePower.cost (q := q) i.val b) := by
  rw [ds1_eq, big_setTape]
  exact stage_power hq place1 _ (ws 1) bs i.val b hb0 h1 hb (hc 1) cb (by
    unfold Placement.active place1 big extras RuntimePower.input RuntimePower.bank bank ds0
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h2 in
theorem stage2 : HoareTime (Placement.placed (RuntimePower.program hq) place2)
    (fun x => x = big (bank hs bs rs (ds1 hq v b i j)) ws)
    (fun x => x = big (bank hs bs rs (ds2 hq v b i j)) ws)
    (RuntimePower.cost (q := q) (m-1-i.val) b) := by
  rw [ds2_eq hq v hs bs rs b i j, big_setTape]
  exact stage_power hq place2 _ (ws 2) bs (m-1-i.val) b hb0 h2 hb (hc 2) cb (by
    unfold Placement.active place2 big extras RuntimePower.input RuntimePower.bank bank ds1
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h3 in
theorem stage3 : HoareTime (Placement.placed (RuntimePower.program hq) place3)
    (fun x => x = big (bank hs bs rs (ds2 hq v b i j)) ws)
    (fun x => x = big (bank hs bs rs (ds3 hq v b i j)) ws)
    (RuntimePower.cost (q := q) j.val b) := by
  rw [ds3_eq hq v hs bs rs b i j, big_setTape]
  exact stage_power hq place3 _ (ws 3) bs j.val b hb0 h3 hb (hc 3) cb (by
    unfold Placement.active place3 big extras RuntimePower.input RuntimePower.bank bank ds2
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

include h4 in
theorem stage4 : HoareTime (Placement.placed (RuntimePower.program hq) place4)
    (fun x => x = big (bank hs bs rs (ds3 hq v b i j)) ws)
    (fun x => x = big (bank hs bs rs (ds4 hq v b i j)) ws)
    (RuntimePower.cost (q := q) (m-1-j.val) b) := by
  rw [ds4_eq hq v hs bs rs b i j, big_setTape]
  exact stage_power hq place4 _ (ws 4) bs (m-1-j.val) b hb0 h4 hb (hc 4) cb (by
    unfold Placement.active place4 big extras RuntimePower.input RuntimePower.bank bank ds3
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
      simp [Fin.castAdd, Tapes.append, RecursiveDimensionBank.head, RecursiveDimensionBank.tape,
        Fin.addCases, SharedBank.empty])

omit hb0 hb cb hc in
theorem stage5 (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (extend (extend (RecursiveChildDimensions.program5 (q := q)) 19) 9)
      (fun x => x = big (bank hs bs rs (ds4 hq v b i j)) ws)
      (fun x => x = big (bank hs bs rs (ds5 hq v b i j)) ws)
      (53*((v.beforeH)*(q^(i.val*b)))+28) :=
  FamilyPlacementAlphabet.extend_hoare (FamilyPlacementAlphabet.extend_hoare
    (RecursiveChildDimensions.stage5_hoare hq v hs bs rs b i j hv hvpos) _) _

omit hb0 hb cb hc in
theorem stage6 (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (extend (extend (RecursiveChildDimensions.program6 (q := q)) 19) 9)
      (fun x => x = big (bank hs bs rs (ds5 hq v b i j)) ws)
      (fun x => x = big (bank hs bs rs (ds6 hq v b i j)) ws)
      (53*((q^((m-1-i.val)*b))*(v.between))+28) :=
  FamilyPlacementAlphabet.extend_hoare (FamilyPlacementAlphabet.extend_hoare
    (RecursiveChildDimensions.stage6_hoare hq v hs bs rs b i j hv hvpos) _) _

omit hb0 hb cb hc in
theorem stage7 (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (extend (extend (RecursiveChildDimensions.program7 (q := q)) 19) 9)
      (fun x => x = big (bank hs bs rs (ds6 hq v b i j)) ws)
      (fun x => x = big (bank hs bs rs (ds7 hq v b i j)) ws)
      (53*((q^((m-1-i.val)*b)*v.between)*(q^(j.val*b)))+28) :=
  FamilyPlacementAlphabet.extend_hoare (FamilyPlacementAlphabet.extend_hoare
    (RecursiveChildDimensions.stage7_hoare hq v hs bs rs b i j hv hvpos) _) _

omit hb0 hb cb hc in
theorem stage8 (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (extend (extend (RecursiveChildDimensions.program8 (q := q)) 19) 9)
      (fun x => x = big (bank hs bs rs (ds7 hq v b i j)) ws)
      (fun x => x = big (bank hs bs rs (ds8 hq v b i j)) ws)
      (53*((q^((m-1-j.val)*b))*(v.afterD))+28) :=
  FamilyPlacementAlphabet.extend_hoare (FamilyPlacementAlphabet.extend_hoare
    (RecursiveChildDimensions.stage8_hoare hq v hs bs rs b i j hv hvpos) _) _

end Stages

/-! ### Construction, clean-up and handoff -/

open RecursiveChildDimensions (bank ds0 ds8)

/-- The eight construction stages. -/
def construct :=
  seq (seq (seq (seq (seq (seq (seq
    (Placement.placed (RuntimePower.program hq) place1) (Placement.placed (RuntimePower.program hq) place2))
      (Placement.placed (RuntimePower.program hq) place3)) (Placement.placed (RuntimePower.program hq) place4))
    (extend (extend (RecursiveChildDimensions.program5 (q := q)) 19) 9))
    (extend (extend (RecursiveChildDimensions.program6 (q := q)) 19) 9))
    (extend (extend (RecursiveChildDimensions.program7 (q := q)) 19) 9))
    (extend (extend (RecursiveChildDimensions.program8 (q := q)) 19) 9)

/-- The construction cost. -/
def constructCost (v : Descriptor) (b : ℕ) {m : ℕ} (i j : Fin m) : ℕ :=
  RuntimePower.cost (q := q) i.val b+1+RuntimePower.cost (q := q) (m-1-i.val) b+1+
    RuntimePower.cost (q := q) j.val b+1+RuntimePower.cost (q := q) (m-1-j.val) b+1+
    (53*((v.beforeH)*(q^(i.val*b)))+28)+1+(53*((q^((m-1-i.val)*b))*(v.between))+28)+1+
    (53*((q^((m-1-i.val)*b)*v.between)*(q^(j.val*b)))+28)+1+(53*((q^((m-1-j.val)*b))*(v.afterD))+28)

theorem construct_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ws : Fin 5 → List Bool) (b : ℕ) {m : ℕ} (i j : Fin m) (hb0 : 0 < b)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hc : ∀ z, GrowingCounterData.Canonical (ws z))
    (h1 : Counter.value (ws 1) = i.val) (h2 : Counter.value (ws 2) = m-1-i.val)
    (h3 : Counter.value (ws 3) = j.val) (h4 : Counter.value (ws 4) = m-1-j.val)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (construct hq) (fun x => x = big (bank hs bs rs ds0) ws)
      (fun x => x = big (bank hs bs rs (ds8 hq v b i j)) ws) (constructCost (q := q) v b i j) :=
  (((((((stage1 hq v hs bs rs ws b i j hb0 hb cb hc h1).seq
    (stage2 hq v hs bs rs ws b i j hb0 hb cb hc h2)).seq
    (stage3 hq v hs bs rs ws b i j hb0 hb cb hc h3)).seq
    (stage4 hq v hs bs rs ws b i j hb0 hb cb hc h4)).seq
    (stage5 hq v hs bs rs ws b i j hv hvpos)).seq
    (stage6 hq v hs bs rs ws b i j hv hvpos)).seq
    (stage7 hq v hs bs rs ws b i j hv hvpos)).seq
    (stage8 hq v hs bs rs ws b i j hv hvpos)

/-- A 19-tape slot inside the 47-tape bank. -/
abbrev slot (z : Fin 19) : Fin 47 := Fin.castAdd 9 (Fin.castAdd 19 z)

/-- Erase one product or power descriptor. -/
theorem bank_erase (hs : Fin 6 → List Bool) (bs rs : List Bool) (ds : Fin 8 → Option (List Bool))
    (k : Fin 8) : bank (q := q) hs bs rs (Function.update ds k none) =
      setTape (bank hs bs rs ds) (⟨11+k.val, by omega⟩ : Fin 19) (fun _ => blank) 0 := by
  unfold bank setTape
  fin_cases k <;> apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp [RecursiveDimensionBank.head, RecursiveDimensionBank.tape, Function.update]

theorem big_slot (d : Tapes 19 q) (ws : Fin 5 → List Bool) (z : Fin 19) :
    (big d ws).head (slot z) = d.head z ∧ (big d ws).tape (slot z) = d.tape z := by
  simp [big, slot, Tapes.append, Fin.addCases_left]

theorem bank_out (hs : Fin 6 → List Bool) (bs rs : List Bool) (ds : Fin 8 → Option (List Bool))
    (k : Fin 8) :
    (bank (q := q) hs bs rs ds).head ⟨11+k.val, by omega⟩ = RecursiveDimensionBank.head (ds k) ∧
    (bank (q := q) hs bs rs ds).tape ⟨11+k.val, by omega⟩ = RecursiveDimensionBank.tape (ds k) := by
  fin_cases k <;> exact ⟨rfl, rfl⟩

theorem erase_hoare (hs : Fin 6 → List Bool) (bs rs : List Bool) (ds : Fin 8 → Option (List Bool))
    (ws : Fin 5 → List Bool) (k : Fin 8) (xs : List Bool) (hk : ds k = some xs) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (a := q) (slot ⟨11+k.val, by omega⟩))
      (fun x => x = big (bank hs bs rs ds) ws)
      (fun x => x = big (bank hs bs rs (Function.update ds k none)) ws) (2*xs.length+4) := by
  rw [bank_erase, big_setTape]
  have hb := big_slot (bank (q := q) hs bs rs ds) ws ⟨11+k.val, by omega⟩
  have ho := bank_out (q := q) hs bs rs ds k
  rw [hk] at ho
  apply BinaryDescriptorCleanupList.one_hoare
  · rw [BinaryDescriptorStackRoundtrip.descriptor_encoded, hb.2, ho.2]; rfl
  · rw [hb.1, ho.1]; rfl

/-- Erase the four powers and the middle product. -/
def clean :=
  seq (seq (seq (seq
    (BinaryDescriptorCleanupList.oneProgram (a := q) (slot 11))
    (BinaryDescriptorCleanupList.oneProgram (a := q) (slot 12)))
    (BinaryDescriptorCleanupList.oneProgram (a := q) (slot 13)))
    (BinaryDescriptorCleanupList.oneProgram (a := q) (slot 14)))
    (BinaryDescriptorCleanupList.oneProgram (a := q) (slot 16))

def cleanCost (v : Descriptor) (b : ℕ) {m : ℕ} (i j : Fin m) : ℕ :=
  (2*(RecursiveChildDimensions.prefixBits hq i.val b).length+4)+1+
    (2*(RecursiveChildDimensions.prefixBits hq (m-1-i.val) b).length+4)+1+
    (2*(RecursiveChildDimensions.prefixBits hq j.val b).length+4)+1+
    (2*(RecursiveChildDimensions.prefixBits hq (m-1-j.val) b).length+4)+1+
    (2*(RecursiveChildDimensions.middleBits (q := q) v (m-1-i.val) b).length+4)

theorem clean_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ws : Fin 5 → List Bool) (b : ℕ) {m : ℕ} (i j : Fin m) :
    HoareTime (clean (q := q)) (fun x => x = big (bank hs bs rs (ds8 hq v b i j)) ws)
      (fun x => x = big (bank hs bs rs
        (RecursiveChildDimensionsClean.cleanDescriptors (ds8 hq v b i j))) ws)
      (cleanCost hq v b i j) := by
  have e1 := erase_hoare (q := q) hs bs rs (ds8 hq v b i j) ws 0 _ rfl
  have e2 := erase_hoare (q := q) hs bs rs (Function.update (ds8 hq v b i j) 0 none) ws 1 _ rfl
  have e3 := erase_hoare (q := q) hs bs rs
    (Function.update (Function.update (ds8 hq v b i j) 0 none) 1 none) ws 2 _ rfl
  have e4 := erase_hoare (q := q) hs bs rs
    (Function.update (Function.update (Function.update (ds8 hq v b i j) 0 none) 1 none) 2 none) ws 3 _ rfl
  have e5 := erase_hoare (q := q) hs bs rs
    (Function.update (Function.update (Function.update (Function.update (ds8 hq v b i j) 0 none) 1 none)
      2 none) 3 none) ws 5 _ rfl
  have he : Function.update (Function.update (Function.update (Function.update (Function.update
      (ds8 hq v b i j) 0 none) 1 none) 2 none) 3 none) 5 none =
      RecursiveChildDimensionsClean.cleanDescriptors (ds8 hq v b i j) := by
    funext z; fin_cases z <;> rfl
  rw [he] at e5
  exact (((e1.seq e2).seq e3).seq e4).seq e5

/-- Copy the atom width and the rows into the quotient slots. -/
def copies :=
  seq (BinaryDescriptorInstall.program q (38 : Fin 47) (slot 9) (by decide))
    (BinaryDescriptorInstall.program q (slot 4) (slot 10) (by decide))

theorem copies_hoare (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) :
    HoareTime (copies (q := q)) (fun x => x = (RecursiveChildHeaderHandoff.canonical hs).append (extras ws))
      (fun x => x = big (RecursiveChildDimensions.input hs (ws 0) (hs 1)) ws)
      (2*(ws 0).length+5+1+(2*(hs 1).length+5)) := by
  have c1 := BinaryDescriptorInstall.install_hoare (q := q) (38 : Fin 47) (slot 9) (by decide)
    ((RecursiveChildHeaderHandoff.canonical hs).append (extras ws)) (ws 0) rfl rfl rfl rfl
  have c2 := BinaryDescriptorInstall.install_hoare (q := q) (slot 4) (slot 10) (by decide)
    (setTape ((RecursiveChildHeaderHandoff.canonical hs).append (extras ws)) (slot 9)
      (RadixZeroFill.encodedBinary (ws 0)) 1) (hs 1) rfl rfl rfl rfl
  refine (c1.seq c2).consequence (fun _ h => h) (fun x hx => hx.trans ?_) le_rfl
  unfold big RecursiveChildHeaderHandoff.canonical RecursiveChildDimensions.input
  rw [slot, slot, SharedPlacementAlphabet.setTape_append_left, SharedPlacementAlphabet.setTape_append_left]
  congr 1
  unfold setTape Tapes.append RecursiveDimensionBank.bank RecursiveChildDimensions.bank
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp [Function.update, RecursiveDimensionBank.head, RecursiveDimensionBank.tape, SharedBank.empty,
      RecursiveDimensionBank.ds0, RecursiveChildDimensions.ds0, Fin.addCases]

/-- **The runtime cross view.** -/
def program :=
  seq (seq (seq (copies (q := q)) (construct hq)) (clean (q := q)))
    (extend (RecursiveChildHeaderHandoff.program q) 9)

def cost (v : Descriptor) (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) (b : ℕ) {m : ℕ}
    (i j : Fin m) : ℕ :=
  (2*(ws 0).length+5+1+(2*(hs 1).length+5))+1+constructCost (q := q) v b i j+1+cleanCost hq v b i j+1+
    RecursiveChildHeaderHandoff.cost hs (RecursiveChildDimensions.childHeaders (q := q) v hs (ws 0) (hs 1) b i j)

/-- **Runtime cross-view preparation.** From the parent headers and the counters of the atom
width `b` and the positions `i`, `N - 1 - i`, `j`, `N - 1 - j`, the canonical headers of the view
`child q 1 b v i j` are installed; the counters are restored and every work tape is blank. -/
theorem prepares (v : Descriptor) (hs : Fin 6 → List Bool) (ws : Fin 5 → List Bool) (b : ℕ)
    {m : ℕ} (i j : Fin m) (hb0 : 0 < b) (hb : Counter.value (ws 0) = b)
    (hc : ∀ z, GrowingCounterData.Canonical (ws z))
    (h1 : Counter.value (ws 1) = i.val) (h2 : Counter.value (ws 2) = m-1-i.val)
    (h3 : Counter.value (ws 3) = j.val) (h4 : Counter.value (ws 4) = m-1-j.val)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    RecursiveDimensionBank.Headers (child q 1 b v i j)
        (RecursiveChildDimensions.childHeaders (q := q) v hs (ws 0) (hs 1) b i j) ∧
      HoareTime (program hq) (fun x => x = (RecursiveChildHeaderHandoff.canonical hs).append (extras ws))
        (fun x => x = (RecursiveChildHeaderHandoff.canonical
          (RecursiveChildDimensions.childHeaders (q := q) v hs (ws 0) (hs 1) b i j)).append (extras ws))
        (cost hq v hs ws b i j) := by
  refine ⟨RecursiveChildDimensions.child_headers 1 b v hs (ws 0) (hs 1) i j hv hb (hc 0)
    (by rw [Nat.div_one]; exact hv.1 1) (hv.2 1), ?_⟩
  have hg := FamilyPlacementAlphabet.extend_hoare
    (RecursiveChildHeaderHandoff.generated_hoare hq v hs (ws 0) (hs 1) b i j) (extras ws)
  exact (((copies_hoare hs ws).seq (construct_hoare hq v hs (ws 0) (hs 1) ws b i j hb0 hb (hc 0) hc
    h1 h2 h3 h4 hv hvpos)).seq (clean_hoare hq v hs (ws 0) (hs 1) ws b i j)).seq hg

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RuntimeCross
