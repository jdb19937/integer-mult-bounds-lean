module

public import IntegerMultBounds.Machine.DimensionProductDescriptor
public import IntegerMultBounds.Machine.InjectivePlacement

/-!
# Shift dimensions from runtime counters

`TranslationDimensions` builds the dimensions of a coordinate shift with the coordinate counts
as literals of its program. Here they are runtime descriptors: from the width `b`, the record
width `W` and four counters `T` (target), `R` (coordinates after the target), `K` (control) and
`M` (coordinates between the control and the target), one fixed program computes the radix
`Q = q^b`, the prefix size `P = q^(T b)`, the suffix size `B = q^(R b) W` and the padded prefix
widths `M b` and `K b` (`construct_hoare`). Each step is a placed power or product routine on a
17-tape bank of optional descriptors (`bank`), and all scratch is returned blank.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.CounterDimensions
noncomputable section

variable {q : ℕ} (hq : 2 ≤ q)

def descriptorHead : Option (List Bool) → ℤ
  | none => 0
  | some _ => 1

def descriptorTape (q : ℕ) : Option (List Bool) → ℤ → Fin (q+4)
  | none => fun _ => blank
  | some xs => RadixZeroFill.encodedBinary xs

/-- A bank of optional descriptors: a descriptor at head one, or a blank tape at head zero. -/
def bank (d : Fin 17 → Option (List Bool)) : Tapes 17 q :=
  ⟨fun i => descriptorHead (d i), fun i => descriptorTape q (d i)⟩

/-- A placed routine on a descriptor bank changes only its own slots. -/
theorem placed_bank {k r c : ℕ} {M : Program k r q} (slot : Fin k → Fin 17)
    (hinj : Function.Injective slot) (hk : k + (17 - k) = 17)
    {small small' : Tapes k q} {d d' : Fin 17 → Option (List Bool)}
    (hin : (⟨fun i => descriptorHead (d (slot i)), fun i => descriptorTape q (d (slot i))⟩ : Tapes k q) = small)
    (hout : (⟨fun i => descriptorHead (d' (slot i)), fun i => descriptorTape q (d' (slot i))⟩ : Tapes k q) = small')
    (hframe : ∀ j, (∀ i, slot i ≠ j) → d' j = d j)
    (hM : HoareTime M (fun v => v = small) (fun v => v = small') c) :
    HoareTime (Placement.placed M (InjectivePlacement.placement slot hinj hk))
      (fun v => v = bank d) (fun v => v = bank d') c := by
  set e := InjectivePlacement.placement slot hinj hk
  have ha : Placement.active e (bank d) = small := by
    rw [InjectivePlacement.active_bank]; exact hin
  apply (Placement.hoare_at hM e (bank d) ha).consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨w', rfl, rfl⟩
  rw [← hout]
  have hslot (i : Fin k) : e (Fin.castAdd (17 - k) i) = slot i := InjectivePlacement.active_slot _ _ _ i
  have hrest (i : Fin (17 - k)) : d' (e (Fin.natAdd k i)) = d (e (Fin.natAdd k i)) := by
    apply hframe
    intro i₀ h
    rw [← hslot i₀] at h
    have := e.injective h
    have hv := congrArg Fin.val this
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  unfold Placement.replace
  have key (j : Fin 17) :
      (Placement.combine e (⟨fun i => descriptorHead (d' (slot i)),
        fun i => descriptorTape q (d' (slot i))⟩ : Tapes k q) (Placement.extra e (bank d))).head j =
        (bank (q := q) d').head j ∧
      (Placement.combine e (⟨fun i => descriptorHead (d' (slot i)),
        fun i => descriptorTape q (d' (slot i))⟩ : Tapes k q) (Placement.extra e (bank d))).tape j =
        (bank (q := q) d').tape j := by
    obtain ⟨i, rfl⟩ := e.surjective j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Placement.combine_head_active, Placement.combine_tape_active]
      simp [bank, hslot]
    · rw [Placement.combine_head_extra, Placement.combine_tape_extra]
      simp [Placement.extra, bank, hrest]
  exact congrArg₂ Tapes.mk (funext fun j => (key j).1) (funext fun j => (key j).2)

/-! ### The construction -/

variable (bs ws ts rs ks ms : List Bool) (b W T R K M : ℕ)

/-- Slots `3..8` hold `b, W, T, R, K, M`; everything else is blank. -/
def inputs : Fin 17 → Option (List Bool) :=
  ![none, none, none, some bs, some ws, some ts, some rs, some ks, some ms,
    none, none, none, none, none, none, none, none]

def input : Tapes 17 q := bank (inputs bs ws ts rs ks ms)

def qBits (b : ℕ) : List Bool := RadixPowerDescriptor.bits hq b
def tbBits (T b : ℕ) : List Bool := DimensionProductDescriptor.bits T b
def pBits (T b : ℕ) : List Bool := RadixPowerDescriptor.bits hq (T*b)
def rbBits (R b : ℕ) : List Bool := DimensionProductDescriptor.bits R b
def sBits (R b : ℕ) : List Bool := RadixPowerDescriptor.bits hq (R*b)
def bBits (R b W : ℕ) : List Bool := DimensionProductDescriptor.bits (q^(R*b)) W
def mbBits (M b : ℕ) : List Bool := DimensionProductDescriptor.bits M b
def kbBits (K b : ℕ) : List Bool := DimensionProductDescriptor.bits K b

/-- Slots `9..16` receive `Q, P, S, B, M b, K b, T b, R b`. -/
def outputs : Fin 17 → Option (List Bool) :=
  ![none, none, none, some bs, some ws, some ts, some rs, some ks, some ms,
    some (qBits hq b), some (pBits hq T b), some (sBits hq R b), some (bBits (q := q) R b W),
    some (mbBits M b), some (kbBits K b), some (tbBits T b), some (rbBits R b)]

def output : Tapes 17 q := bank (outputs hq bs ws ts rs ks ms b W T R K M)

/-- The slot written by each step. -/
def slotOf : ℕ → Fin 17
  | 0 => 9 | 1 => 15 | 2 => 10 | 3 => 16 | 4 => 11 | 5 => 12 | 6 => 13 | _ => 14

/-- The descriptor written by each step. -/
def valOf : ℕ → List Bool
  | 0 => qBits hq b | 1 => tbBits T b | 2 => pBits hq T b | 3 => rbBits R b
  | 4 => sBits hq R b | 5 => bBits (q := q) R b W | 6 => mbBits M b | _ => kbBits K b

/-- The partial results after each step. -/
def after : ℕ → Fin 17 → Option (List Bool)
  | 0 => inputs bs ws ts rs ks ms
  | n+1 => Function.update (after n) (slotOf n) (some (valOf hq b W T R K M n))

variable {bs ws ts rs ks ms b W T R K M}

omit hq in
theorem slotOf_ge (n : ℕ) : 9 ≤ (slotOf n).val := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp [slotOf]

theorem after_scratch (n : ℕ) (i : Fin 17) (hi : i.val < 3) :
    after hq bs ws ts rs ks ms b W T R K M n i = none := by
  induction n with
  | zero => fin_cases i <;> first | rfl | (simp at hi)
  | succ n ih =>
    have hne : i ≠ slotOf n := fun h => by have := slotOf_ge n; rw [← h] at this; omega
    rw [after, Function.update_of_ne hne, ih]

theorem after_frame (n : ℕ) (j : Fin 17) (hj : j ≠ slotOf n) :
    after hq bs ws ts rs ks ms b W T R K M (n+1) j = after hq bs ws ts rs ks ms b W T R K M n j :=
  Function.update_of_ne hj _ _

theorem after_zero : after hq bs ws ts rs ks ms b W T R K M 0 = inputs bs ws ts rs ks ms := rfl

theorem after_eight : after hq bs ws ts rs ks ms b W T R K M 8 = outputs hq bs ws ts rs ks ms b W T R K M := by
  funext i
  fin_cases i <;> simp [after, slotOf, valOf, inputs, outputs, Function.update_apply]

/-- The power slots: radix scratch, clock scratch, exponent, output. -/
def powerSlots (e o : Fin 17) : Fin 4 → Fin 17 := ![0, 1, e, o]

/-- The product slots: spare, output, inner clock, inner count, outer clock, outer count. -/
def productSlots (w o n : Fin 17) : Fin 6 → Fin 17 := ![0, o, 1, w, 2, n]

omit hq in
theorem power_input (xs : List Bool) :
    (RadixPowerDescriptor.input xs : Tapes 4 q) =
      ⟨![0, 0, 1, 0], ![fun _ => blank, fun _ => blank, RadixZeroFill.encodedBinary xs, fun _ => blank]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl


theorem power_step {n : ℕ} {e o : Fin 17} {xs : List Bool} {x : ℕ}
    (hinj : Function.Injective (powerSlots e o))
    (hx : Counter.value xs = x) (cx : GrowingCounterData.Canonical xs)
    (hd : after hq bs ws ts rs ks ms b W T R K M n e = some xs)
    (hs : ∀ i : Fin 17, i.val < 3 → after hq bs ws ts rs ks ms b W T R K M n i = none ∧
      after hq bs ws ts rs ks ms b W T R K M (n+1) i = none)
    (ho₀ : after hq bs ws ts rs ks ms b W T R K M n o = none)
    (ho₁ : after hq bs ws ts rs ks ms b W T R K M (n+1) o = some (RadixPowerDescriptor.bits hq x))
    (he₁ : after hq bs ws ts rs ks ms b W T R K M (n+1) e = some xs)
    (hframe : ∀ j : Fin 17, j ≠ o → after hq bs ws ts rs ks ms b W T R K M (n+1) j =
      after hq bs ws ts rs ks ms b W T R K M n j) :
    HoareTime (Placement.placed (RadixPowerDescriptor.program hq)
        (InjectivePlacement.placement (u := 13) (powerSlots e o) hinj (by norm_num)))
      (fun v => v = bank (after hq bs ws ts rs ks ms b W T R K M n))
      (fun v => v = bank (after hq bs ws ts rs ks ms b W T R K M (n+1))) (99*q^x) := by
  have h0 := hs 0 (by decide)
  have h1 := hs 1 (by decide)
  refine placed_bank _ _ _ ?_ ?_ ?_ (RadixPowerDescriptor.construct_hoare_linear hq xs x hx cx)
  · rw [power_input]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [powerSlots, h0.1, h1.1, hd, ho₀, descriptorHead, descriptorTape]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [powerSlots, h0.2, h1.2, he₁, ho₁, descriptorHead, descriptorTape, RadixPowerDescriptor.output]
  · intro j hj
    exact hframe j (fun h => hj 3 (by simp [powerSlots, h]))

theorem product_step {n : ℕ} {w o m : Fin 17} {xs ys : List Bool} {x y : ℕ}
    (hinj : Function.Injective (productSlots w o m)) (hy0 : 0 < y)
    (hx : Counter.value xs = x) (cx : GrowingCounterData.Canonical xs)
    (hy : Counter.value ys = y) (cy : GrowingCounterData.Canonical ys)
    (hdw : after hq bs ws ts rs ks ms b W T R K M n w = some ys)
    (hdm : after hq bs ws ts rs ks ms b W T R K M n m = some xs)
    (hs : ∀ i : Fin 17, i.val < 3 → after hq bs ws ts rs ks ms b W T R K M n i = none ∧
      after hq bs ws ts rs ks ms b W T R K M (n+1) i = none)
    (ho₀ : after hq bs ws ts rs ks ms b W T R K M n o = none)
    (ho₁ : after hq bs ws ts rs ks ms b W T R K M (n+1) o = some (DimensionProductDescriptor.bits x y))
    (hw₁ : after hq bs ws ts rs ks ms b W T R K M (n+1) w = some ys)
    (hm₁ : after hq bs ws ts rs ks ms b W T R K M (n+1) m = some xs)
    (hframe : ∀ j : Fin 17, j ≠ o → after hq bs ws ts rs ks ms b W T R K M (n+1) j =
      after hq bs ws ts rs ks ms b W T R K M n j) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q))
        (InjectivePlacement.placement (u := 11) (productSlots w o m) hinj (by norm_num)))
      (fun v => v = bank (after hq bs ws ts rs ks ms b W T R K M n))
      (fun v => v = bank (after hq bs ws ts rs ks ms b W T R K M (n+1))) (53*(x*y)+28) := by
  have h0 := hs 0 (by decide)
  have h1 := hs 1 (by decide)
  have h2 := hs 2 (by decide)
  refine placed_bank _ _ _ ?_ ?_ ?_
    (DimensionProductDescriptor.construct_hoare ys xs x y hy0 hy hx cy cx)
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [productSlots, h0.1, h1.1, h2.1, hdw, hdm, ho₀, descriptorHead, descriptorTape,
        DimensionProductDescriptor.input]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [productSlots, h0.2, h1.2, h2.2, hw₁, hm₁, ho₁, descriptorHead, descriptorTape,
        DimensionProductDescriptor.output]
  · intro j hj
    exact hframe j (fun h => hj 1 (by simp [productSlots, h]))

omit hq in
theorem powerSlots_inj (e o : Fin 17) (he : 2 ≤ e.val) (ho : 2 ≤ o.val) (h : e.val ≠ o.val) :
    Function.Injective (powerSlots e o) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> first | rfl | ((simp [powerSlots] at hv) <;> omega)

omit hq in
theorem productSlots_inj (w o m : Fin 17) (hw : 3 ≤ w.val) (ho : 3 ≤ o.val) (hm : 3 ≤ m.val)
    (h₁ : w.val ≠ o.val) (h₂ : w.val ≠ m.val) (h₃ : o.val ≠ m.val) :
    Function.Injective (productSlots w o m) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> first | rfl | ((simp [productSlots] at hv) <;> omega)

def powerAt (e o : Fin 17) (h : Function.Injective (powerSlots e o)) :=
  Placement.placed (RadixPowerDescriptor.program hq)
    (InjectivePlacement.placement (u := 13) (powerSlots e o) h (by norm_num))

def productAt (w o m : Fin 17) (h : Function.Injective (productSlots w o m)) :=
  Placement.placed (DimensionProductDescriptor.program (q := q))
    (InjectivePlacement.placement (u := 11) (productSlots w o m) h (by norm_num))

/-- One fixed program: no counter value enters it. -/
def program :=
  seq (seq (seq (seq (seq (seq (seq
    (powerAt hq 3 9 (powerSlots_inj 3 9 (by decide) (by decide) (by decide)))
    (productAt (q := q) 3 15 5 (productSlots_inj 3 15 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))
    (powerAt hq 15 10 (powerSlots_inj 15 10 (by decide) (by decide) (by decide))))
    (productAt (q := q) 3 16 6 (productSlots_inj 3 16 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))
    (powerAt hq 16 11 (powerSlots_inj 16 11 (by decide) (by decide) (by decide))))
    (productAt (q := q) 4 12 11 (productSlots_inj 4 12 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))
    (productAt (q := q) 3 13 8 (productSlots_inj 3 13 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))
    (productAt (q := q) 3 14 7 (productSlots_inj 3 14 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))

local macro "aft" : tactic =>
  `(tactic| simp [after, slotOf, valOf, inputs, Function.update_apply, qBits, tbBits, pBits, rbBits,
    sBits, bBits, mbBits, kbBits])

/-- **The dimensions from counters.** -/
theorem construct_hoare (hb : Counter.value bs = b) (hw : Counter.value ws = W)
    (ht : Counter.value ts = T) (hr : Counter.value rs = R) (hk : Counter.value ks = K)
    (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cw : GrowingCounterData.Canonical ws)
    (ct : GrowingCounterData.Canonical ts) (cr : GrowingCounterData.Canonical rs)
    (ck : GrowingCounterData.Canonical ks) (cm : GrowingCounterData.Canonical ms)
    (hb0 : 0 < b) (hW : 0 < W) :
    HoareTime (program hq) (fun v => v = input (q := q) bs ws ts rs ks ms)
      (fun v => v = output hq bs ws ts rs ks ms b W T R K M)
      (99*q^b+(53*(T*b)+28)+99*q^(T*b)+(53*(R*b)+28)+99*q^(R*b)+(53*(q^(R*b)*W)+28)+
        (53*(M*b)+28)+(53*(K*b)+28)+7) := by
  have hs (n : ℕ) : ∀ i : Fin 17, i.val < 3 → after hq bs ws ts rs ks ms b W T R K M n i = none ∧
      after hq bs ws ts rs ks ms b W T R K M (n+1) i = none :=
    fun i hi => ⟨after_scratch hq n i hi, after_scratch hq (n+1) i hi⟩
  have s1 := power_step (n := 0) (e := 3) (o := 9) hq (bs := bs) (ws := ws) (ts := ts) (rs := rs)
    (ks := ks) (ms := ms) (b := b) (W := W) (T := T) (R := R) (K := K) (M := M)
    (powerSlots_inj 3 9 (by decide) (by decide) (by decide)) hb cb (by aft) (hs 0)
    (by aft) (by aft) (by aft) (after_frame hq 0)
  have s2 := product_step (n := 1) (x := T) (y := b) (w := 3) (o := 15) (m := 5) hq (bs := bs) (ws := ws) (ts := ts)
    (rs := rs) (ks := ks) (ms := ms) (b := b) (W := W) (T := T) (R := R) (K := K) (M := M)
    (productSlots_inj 3 15 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hb0 ht ct hb cb (by aft) (by aft) (hs 1) (by aft) (by aft) (by aft) (by aft)
    (after_frame hq 1)
  have s3 := power_step (n := 2) (x := T*b) (e := 15) (o := 10) hq (bs := bs) (ws := ws) (ts := ts) (rs := rs)
    (ks := ks) (ms := ms) (b := b) (W := W) (T := T) (R := R) (K := K) (M := M)
    (powerSlots_inj 15 10 (by decide) (by decide) (by decide))
    (DimensionProductDescriptor.bits_value T b) (DimensionProductDescriptor.bits_canonical T b)
    (by aft) (hs 2) (by aft) (by aft) (by aft)
    (after_frame hq 2)
  have s4 := product_step (n := 3) (x := R) (y := b) (w := 3) (o := 16) (m := 6) hq (bs := bs) (ws := ws) (ts := ts)
    (rs := rs) (ks := ks) (ms := ms) (b := b) (W := W) (T := T) (R := R) (K := K) (M := M)
    (productSlots_inj 3 16 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hb0 hr cr hb cb (by aft) (by aft) (hs 3) (by aft) (by aft) (by aft) (by aft)
    (after_frame hq 3)
  have s5 := power_step (n := 4) (x := R*b) (e := 16) (o := 11) hq (bs := bs) (ws := ws) (ts := ts) (rs := rs)
    (ks := ks) (ms := ms) (b := b) (W := W) (T := T) (R := R) (K := K) (M := M)
    (powerSlots_inj 16 11 (by decide) (by decide) (by decide))
    (DimensionProductDescriptor.bits_value R b) (DimensionProductDescriptor.bits_canonical R b)
    (by aft) (hs 4) (by aft) (by aft) (by aft)
    (after_frame hq 4)
  have s6 := product_step (n := 5) (x := q^(R*b)) (y := W) (w := 4) (o := 12) (m := 11) hq (bs := bs) (ws := ws) (ts := ts)
    (rs := rs) (ks := ks) (ms := ms) (b := b) (W := W) (T := T) (R := R) (K := K) (M := M)
    (productSlots_inj 4 12 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hW (RadixPowerDescriptor.bits_value hq (R*b)) (RadixPowerDescriptor.bits_canonical hq (R*b)) hw cw
    (by aft) (by aft) (hs 5) (by aft) (by aft) (by aft) (by aft)
    (after_frame hq 5)
  have s7 := product_step (n := 6) (x := M) (y := b) (w := 3) (o := 13) (m := 8) hq (bs := bs) (ws := ws) (ts := ts)
    (rs := rs) (ks := ks) (ms := ms) (b := b) (W := W) (T := T) (R := R) (K := K) (M := M)
    (productSlots_inj 3 13 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hb0 hm cm hb cb (by aft) (by aft) (hs 6) (by aft) (by aft) (by aft) (by aft)
    (after_frame hq 6)
  have s8 := product_step (n := 7) (x := K) (y := b) (w := 3) (o := 14) (m := 7) hq (bs := bs) (ws := ws) (ts := ts)
    (rs := rs) (ks := ks) (ms := ms) (b := b) (W := W) (T := T) (R := R) (K := K) (M := M)
    (productSlots_inj 3 14 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hb0 hk ck hb cb (by aft) (by aft) (hs 7) (by aft) (by aft) (by aft) (by aft)
    (after_frame hq 7)
  have h := (((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8)
  rw [after_zero, after_eight] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- The construction is linear in the array volume `q^(T b) q^b q^(R b) W`. -/
theorem construct_hoare_volume (hb : Counter.value bs = b) (hw : Counter.value ws = W)
    (ht : Counter.value ts = T) (hr : Counter.value rs = R) (hk : Counter.value ks = K)
    (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cw : GrowingCounterData.Canonical ws)
    (ct : GrowingCounterData.Canonical ts) (cr : GrowingCounterData.Canonical rs)
    (ck : GrowingCounterData.Canonical ks) (cm : GrowingCounterData.Canonical ms)
    (hb0 : 0 < b) (hW : 0 < W) (hKT : K ≤ T) (hMT : M ≤ T) :
    HoareTime (program hq) (fun v => v = input (q := q) bs ws ts rs ks ms)
      (fun v => v = output hq bs ws ts rs ks ms b W T R K M)
      (720*(q^(T*b)*q^b*(q^(R*b)*W))) := by
  apply (construct_hoare hq hb hw ht hr hk hm cb cw ct cr ck cm hb0 hW).consequence
    (fun _ h => h) (fun _ h => h)
  have hP : 1 ≤ q^(T*b) := Nat.one_le_pow _ _ (by omega)
  have hQ : 1 ≤ q^b := Nat.one_le_pow _ _ (by omega)
  have hS : 1 ≤ q^(R*b) := Nat.one_le_pow _ _ (by omega)
  have hTb : T*b ≤ q^(T*b) := (Nat.lt_pow_self (n := T*b) (by omega : 1 < q)).le
  have hRb : R*b ≤ q^(R*b) := (Nat.lt_pow_self (n := R*b) (by omega : 1 < q)).le
  have hMb : M*b ≤ T*b := Nat.mul_le_mul_right b hMT
  have hKb : K*b ≤ T*b := Nat.mul_le_mul_right b hKT
  have hSW : q^(R*b) ≤ q^(R*b)*W := Nat.le_mul_of_pos_right _ hW
  set P := q^(T*b)
  set Q := q^b
  set S := q^(R*b)
  have hB : 1 ≤ S*W := hS.trans hSW
  have hPQ : 1 ≤ P*Q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hV1 : S*W ≤ P*Q*(S*W) := Nat.le_mul_of_pos_left _ hPQ
  have hV2 : P ≤ P*Q*(S*W) := by
    calc P ≤ P*Q := Nat.le_mul_of_pos_right _ hQ
      _ ≤ P*Q*(S*W) := Nat.le_mul_of_pos_right _ hB
  have hV3 : Q ≤ P*Q*(S*W) := by
    calc Q ≤ P*Q := Nat.le_mul_of_pos_left _ hP
      _ ≤ P*Q*(S*W) := Nat.le_mul_of_pos_right _ hB
  have hV4 : 1 ≤ P*Q*(S*W) := hQ.trans hV3
  omega

end
end IntegerMultBounds.Machine.CounterDimensions
