module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafRoutines
public import IntegerMultBounds.Machine.CounterAdvance

/-!
# Counter steps on the common bank

Each counter step is one routine on optional descriptors, placed on the common bank with its
inputs and outputs on counters and its scratch on private tapes (`blk`). A step routes some of
its slots to counters (`route`); the other slots are private and blank before and after. The
steps: erase a counter (`erase_runs`), write zero (`zero_runs`), add one counter to another
(`adv_runs`, and `advs_runs` for a fixed number of times), a difference (`diff_runs`), a product
(`mul_runs`) and a division with remainder (`div_runs`). Every step keeps the headers and every
counter it does not write.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Counters

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank Target word K)
open Routines (sel canon)
open Blocks (seqB seq_runs runs_mono Leading)

variable {t : ℕ}

/-! ### Routing -/

/-- A step's routing: some of its slots on counters, the others private. -/
def route (a : Fin 22 → Option (Fin K)) : Fin 22 → Option (Target 22) := fun i => (a i).map .aux

/-- No counter takes two slots. -/
def Inj (a : Fin 22 → Option (Fin K)) : Prop := ∀ i i' j, a i = some j → a i' = some j → i = i'

theorem route_inj {a : Fin 22 → Option (Fin K)} (h : Inj a) : Function.Injective (sel (route a)) := by
  intro i i' he
  simp only [sel, route] at he
  rcases hi : a i with _ | j <;> rcases hi' : a i' with _ | j' <;> rw [hi, hi'] at he <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
      reduceCtorEq] at he
  · exact Target.priv.inj he
  · exact h i i' j hi (by rw [hi', Target.aux.inj he])

/-- A step placed on the common bank. -/
def blk {q : ℕ} (M : Program 22 q prime) (a : Fin 22 → Option (Fin K)) (h : Inj a) :
    Graph.Block (CommonBank.count t) prime :=
  Embed.place (u := CommonBank.count t) M (fun i => (sel (route a) i).slot (t := t))
    ((Routines.slot_injective 22).comp (route_inj h)) (Nat.add_comm _ _)

theorem blk_leading {q : ℕ} (M : Program 22 q prime) (a : Fin 22 → Option (Fin K)) (h : Inj a) :
    Leading (blk (t := t) M a h) := Blocks.place_leading _ _ _ _

/-- The descriptor a routed slot holds. -/
def val (a : Fin 22 → Option (Fin K)) (c : Fin K → Option ℕ) (i : Fin 22) : Option (List Bool) :=
  match a i with
  | some j => word (c j)
  | none => none

theorem value_route (a : Fin 22 → Option (Fin K)) (hs : Fin 6 → List Bool) (c : Fin K → Option ℕ) :
    (fun i => (sel (route a) i).value hs c) = val a c := by
  funext i
  simp only [sel, route, val]
  rcases a i with _ | j <;> rfl

variable {roles : Tapes t prime} {hs : Fin 6 → List Bool} {f : ℤ → Fin (prime+4)} {p : ℤ}
  {node scalar : Tapes 1 prime} {c : Fin K → Option ℕ} {st : Tapes 2 prime}

/-- **A routed step**: a run of the step from the routed values of `c` to those of `c'`, where
`c'` agrees with `c` off the routed counters. -/
theorem blk_runs {q B : ℕ} {M : Program 22 q prime} {a : Fin 22 → Option (Fin K)} (h : Inj a)
    (c' : Fin K → Option ℕ)
    (hM : HoareTime M (fun w => w = Headers.bank (val a c)) (fun w => w = Headers.bank (val a c')) B)
    (hc : ∀ j, (∀ i, a i ≠ some j) → c' j = c j) :
    Runs (blk (t := t) M a h) (bank roles hs f p node scalar c st) (bank roles hs f p node scalar c' st) B := by
  rw [← value_route a hs c] at hM
  refine Routines.routine_runs (route a) (route_inj h) hM hs c' (fun i => ?_) (fun _ _ => rfl)
    (fun j hj => hc j fun i hi => hj i ?_)
  · rw [← value_route a hs c']
  · simp only [sel, route, hi, Option.map_some, Option.getD_some]

theorem val_some {a : Fin 22 → Option (Fin K)} {c : Fin K → Option ℕ} {i : Fin 22} {j : Fin K}
    (hi : a i = some j) : val a c i = word (c j) := by simp [val, hi]

theorem val_none {a : Fin 22 → Option (Fin K)} {c : Fin K → Option ℕ} {i : Fin 22}
    (hi : a i = none) : val a c i = none := by simp [val, hi]

/-- Writing a routed counter writes its slot. -/
theorem val_update {a : Fin 22 → Option (Fin K)} (h : Inj a) {i₀ : Fin 22} {j : Fin K} (h₀ : a i₀ = some j)
    (c : Fin K → Option ℕ) (x : Option ℕ) :
    val a (Function.update c j x) = Function.update (val a c) i₀ (word x) := by
  funext i
  by_cases hi : i = i₀
  · subst hi; simp [val, h₀]
  · rw [Function.update_of_ne hi]
    unfold val
    rcases ha : a i with _ | j'
    · rfl
    · have hj : j' ≠ j := fun he => hi (h i i₀ j (he ▸ ha) h₀)
      simp only [Function.update_of_ne hj]

/-! ### The steps -/

section Steps

/-- The routing of one counter at slot `0`. -/
def one (j : Fin K) : Fin 22 → Option (Fin K) := fun i => if i = 0 then some j else none

theorem one_inj (j : Fin K) : Inj (one j) := by
  intro i i' k hi hi'
  simp only [one] at hi hi'
  split_ifs at hi hi' with h h'
  simp_all

theorem val_one (j : Fin K) (c : Fin K → Option ℕ) (i : Fin 22) :
    val (one j) c i = if i = 0 then word (c j) else none := by
  simp only [val, one]; split_ifs <;> rfl

/-- Erase a counter. -/
def erase (j : Fin K) : Graph.Block (CommonBank.count t) prime :=
  blk (Headers.eraseAt (q := prime) 0) (one j) (one_inj j)

theorem erase_runs {j : Fin K} {x : ℕ} (hj : c j = some x) :
    Runs (erase (t := t) j) (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update c j none) st) (2*(bits x).length+4) := by
  refine blk_runs (one_inj j) _ ?_ (fun k hk => ?_)
  · have h := Headers.erase_step (q := prime) (d := val (one j) c) (j := 0) (xs := bits x)
      (by simp [val, one, hj, word])
    rw [val_update (one_inj j) (i₀ := 0) (by simp [one]) c none]
    exact h
  · exact Function.update_of_ne (fun h => hk 0 (by simp [one, h])) _ _

/-- Write zero on an absent counter. -/
def zero (j : Fin K) : Graph.Block (CommonBank.count t) prime :=
  blk (CounterAdvance.zeroProgram (a := prime) (0 : Fin 22)) (one j) (one_inj j)

theorem zero_runs {j : Fin K} (hj : c j = none) :
    Runs (zero (t := t) j) (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update c j (some 0)) st) 6 := by
  refine blk_runs (one_inj j) _ ?_ (fun k hk => ?_)
  · have h := CounterAdvance.zero_hoare (a := prime) (0 : Fin 22) (Headers.bank (q := prime) (val (one j) c))
      (by simp [Headers.bank, val_one, hj, word, CounterDimensions.descriptorTape])
      (by simp [Headers.bank, val_one, hj, word, CounterDimensions.descriptorHead])
    rw [val_update (one_inj j) (i₀ := 0) (by simp [one]) c (some 0), Headers.bank_update]
    exact h
  · exact Function.update_of_ne (fun h => hk 0 (by simp [one, h])) _ _

/-- The routing of two counters at slots `0` and `2`. -/
def two (x k : Fin K) : Fin 22 → Option (Fin K) :=
  fun i => if i = 0 then some x else if i = 2 then some k else none

theorem two_inj {x k : Fin K} (h : x ≠ k) : Inj (two x k) := by
  intro i i' j hi hi'
  simp only [two] at hi hi'
  split_ifs at hi hi' <;> simp_all

/-- Add counter `k` to counter `x`. -/
def adv (x k : Fin K) (h : x ≠ k) : Graph.Block (CommonBank.count t) prime :=
  blk (CounterAdvance.advProgram (a := prime) (0 : Fin 22) 1 2 (by decide) (by decide) (by decide))
    (two x k) (two_inj h)

def advCost (X Y : ℕ) : ℕ := 10*Y+2*(bits X).length+7*(bits Y).length+28

theorem adv_runs {x k : Fin K} (h : x ≠ k) {X Y : ℕ} (hx : c x = some X) (hk : c k = some Y) :
    Runs (adv (t := t) x k h) (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update c x (some (X+Y))) st) (advCost X Y) := by
  have v0 : val (two x k) c 0 = some (bits X) := by simp [val, two, hx, word]
  have v1 : val (two x k) c 1 = none := by simp [val, two]
  have v2 : val (two x k) c 2 = some (bits Y) := by simp [val, two, hk, word]
  refine blk_runs (two_inj h) _ ?_ (fun j hj => ?_)
  · have hh := CounterAdvance.adv_hoare (a := prime) (i := (0 : Fin 22)) (c := 1) (k := 2) (by decide) (by decide)
      (by decide) (Headers.bank (q := prime) (val (two x k) c)) X Y
      (by simp [Headers.bank, v0, CounterDimensions.descriptorTape])
      (by simp [Headers.bank, v0, CounterDimensions.descriptorHead])
      (by simp [Headers.bank, v1, CounterDimensions.descriptorTape])
      (by simp [Headers.bank, v1, CounterDimensions.descriptorHead])
      (by simp [Headers.bank, v2, CounterDimensions.descriptorTape])
      (by simp [Headers.bank, v2, CounterDimensions.descriptorHead])
    rw [val_update (two_inj h) (i₀ := 0) (by simp [two]) c (some (X+Y)), Headers.bank_update]
    exact hh
  · exact Function.update_of_ne (fun he => hj 0 (by simp [two, he])) _ _

/-- Add counter `k` to counter `x`, `r + 1` times. -/
def advs (x k : Fin K) (h : x ≠ k) : ℕ → Graph.Block (CommonBank.count t) prime
  | 0 => adv x k h
  | r+1 => seqB (advs x k h r) (adv x k h)

theorem advs_leading (x k : Fin K) (h : x ≠ k) : ∀ r, Leading (advs (t := t) x k h r)
  | 0 => blk_leading _ _ (two_inj h)
  | _+1 => Blocks.seq_leading _ _

def advsCost (X Y : ℕ) : ℕ → ℕ
  | 0 => advCost X Y
  | r+1 => advsCost X Y r + advCost (X + (r+1)*Y) Y + 1

theorem advs_runs {x k : Fin K} (h : x ≠ k) {X Y : ℕ} (hx : c x = some X) (hk : c k = some Y) :
    ∀ r, Runs (advs (t := t) x k h r) (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update c x (some (X+(r+1)*Y))) st) (advsCost X Y r)
  | 0 => by
    rw [Nat.zero_add, Nat.one_mul]
    exact adv_runs h hx hk
  | r+1 => by
    have h₁ := advs_runs h hx hk r
    have h₂ := adv_runs (roles := roles) (hs := hs) (f := f) (p := p) (node := node) (scalar := scalar)
      (st := st) (c := Function.update c x (some (X+(r+1)*Y))) h (X := X+(r+1)*Y) (Y := Y) (by simp)
      (by rw [Function.update_of_ne h.symm]; exact hk)
    rw [Function.update_idem, show X + (r+1)*Y + Y = X + (r+1+1)*Y by ring] at h₂
    exact seq_runs (advs_leading x k h r) (blk_leading _ _ (two_inj h)) h₁ h₂

/-- The routing of three counters at slots `0`, `1`, `2`. -/
def three (x y o : Fin K) : Fin 22 → Option (Fin K) :=
  fun i => if i = 0 then some x else if i = 1 then some y else if i = 2 then some o else none

theorem three_inj {x y o : Fin K} (hxy : x ≠ y) (hxo : x ≠ o) (hyo : y ≠ o) : Inj (three x y o) := by
  intro i i' j hi hi'
  simp only [three] at hi hi'
  split_ifs at hi hi' <;> simp_all

/-- `o = x - y`. -/
def diff (x y o : Fin K) (hxy : x ≠ y) (hxo : x ≠ o) (hyo : y ≠ o) : Graph.Block (CommonBank.count t) prime :=
  blk (Arith.diffAt (q := prime) 0 1 2 (by decide)) (three x y o) (three_inj hxy hxo hyo)

theorem diff_runs {x y o : Fin K} (hxy : x ≠ y) (hxo : x ≠ o) (hyo : y ≠ o) {X Y : ℕ} (hle : Y ≤ X)
    (hx : c x = some X) (hy : c y = some Y) (ho : c o = none) :
    Runs (diff (t := t) x y o hxy hxo hyo) (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update c o (some (X-Y))) st) (6*X+27) := by
  refine blk_runs (three_inj hxy hxo hyo) _ ?_ (fun j hj => ?_)
  · have hh := Arith.difference_hoare (q := prime) (d := val (three x y o) c) (x := 0) (y := 1) (o := 2)
      (by decide) (xs := bits X) (ys := bits Y) (by simpa using hle)
      (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
      (by simp [val, three, hx, word]) (by simp [val, three, hy, word]) (by simp [val, three, ho, word])
    rw [FlatCoordinateSchedule.bits_value, FlatCoordinateSchedule.bits_value, LeafRoutines.quot_bits] at hh
    rw [val_update (three_inj hxy hxo hyo) (i₀ := 2) (by simp [three]) c (some (X-Y))]
    exact hh
  · exact Function.update_of_ne (fun he => hj 2 (by simp [three, he])) _ _

/-- The routing of a product: `y` at slot `3`, the output at `4`, `x` at `5`. -/
def prodRoute (x y o : Fin K) : Fin 22 → Option (Fin K) :=
  fun i => if i = 3 then some y else if i = 4 then some o else if i = 5 then some x else none

theorem prodRoute_inj {x y o : Fin K} (hxy : x ≠ y) (hxo : x ≠ o) (hyo : y ≠ o) : Inj (prodRoute x y o) := by
  intro i i' j hi hi'
  simp only [prodRoute] at hi hi'
  split_ifs at hi hi' <;> simp_all

/-- `o = x * y`. -/
def mul (x y o : Fin K) (hxy : x ≠ y) (hxo : x ≠ o) (hyo : y ≠ o) : Graph.Block (CommonBank.count t) prime :=
  blk (Headers.productAt (q := prime) 3 4 5 (Headers.productSlots_inj 3 4 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))) (prodRoute x y o) (prodRoute_inj hxy hxo hyo)

theorem mul_runs {x y o : Fin K} (hxy : x ≠ y) (hxo : x ≠ o) (hyo : y ≠ o) {X Y : ℕ} (hY : 0 < Y)
    (hx : c x = some X) (hy : c y = some Y) (ho : c o = none) :
    Runs (mul (t := t) x y o hxy hxo hyo) (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update c o (some (X*Y))) st) (53*(X*Y)+28) := by
  refine blk_runs (prodRoute_inj hxy hxo hyo) _ ?_ (fun j hj => ?_)
  · have hh := Headers.product_step (q := prime) (d := val (prodRoute x y o) c) (w := 3) (o := 4) (m := 5)
      (Headers.productSlots_inj 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      hY (FlatCoordinateSchedule.bits_value X) (FlatCoordinateSchedule.bits_canonical X)
      (FlatCoordinateSchedule.bits_value Y) (FlatCoordinateSchedule.bits_canonical Y)
      (by simp [val, prodRoute, hy, word]) (by simp [val, prodRoute, hx, word])
      (by simp [val, prodRoute]) (by simp [val, prodRoute]) (by simp [val, prodRoute])
      (by simp [val, prodRoute, ho, word])
    rw [val_update (prodRoute_inj hxy hxo hyo) (i₀ := 4) (by simp [prodRoute]) c (some (X*Y))]
    exact hh
  · exact Function.update_of_ne (fun he => hj 4 (by simp [prodRoute, he])) _ _

/-- The routing of a division: `y` at slot `3`, `d` at `4`, the quotient at `8`, the remainder at
`9`. -/
def divRoute (y d qo ro : Fin K) : Fin 22 → Option (Fin K) :=
  fun i => if i = 3 then some y else if i = 4 then some d else if i = 8 then some qo else
    if i = 9 then some ro else none

/-- The four counters of a division are distinct. -/
structure Distinct4 (y d qo ro : Fin K) : Prop where
  yd : y ≠ d
  yq : y ≠ qo
  yr : y ≠ ro
  dq : d ≠ qo
  dr : d ≠ ro
  qr : qo ≠ ro

theorem divRoute_inj {y d qo ro : Fin K} (h : Distinct4 y d qo ro) : Inj (divRoute y d qo ro) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  intro i i' j hi hi'
  simp only [divRoute] at hi hi'
  split_ifs at hi hi' <;> simp_all

/-- `qo = ⌊y / d⌋`, `ro = y mod d`. -/
def div (y d qo ro : Fin K) (h : Distinct4 y d qo ro) : Graph.Block (CommonBank.count t) prime :=
  blk (Arith.split (q := prime)) (divRoute y d qo ro) (divRoute_inj h)

theorem div_runs {y d qo ro : Fin K} (h : Distinct4 y d qo ro) {Y D : ℕ} (hD : 0 < D)
    (hy : c y = some Y) (hd : c d = some D) (hq : c qo = none) (hr : c ro = none) :
    ∃ B ≤ BinaryDescriptorDivMod.linearConstant (bits D) * (Y + 1),
      Runs (div (t := t) y d qo ro h) (bank roles hs f p node scalar c st)
        (bank roles hs f p node scalar (Function.update (Function.update c qo (some (Y / D))) ro
          (some (Y % D))) st) B := by
  have hd0 : 0 < Counter.value (bits D) := by rw [FlatCoordinateSchedule.bits_value]; exact hD
  obtain ⟨zs, rs, cz, cr, vz, vr, hh⟩ := Arith.split_hoare (q := prime)
    (d := val (divRoute y d qo ro) c) (ys := bits Y) hd0
    (by simp [val, divRoute, hy, word]) (by simp [val, divRoute, hd, word])
    (by simp [val, divRoute, hq, word]) (by simp [val, divRoute, hr, word])
    (by intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [val, divRoute])
  have hz : zs = bits (Y / D) := (canon cz).trans (by simp only [vz, FlatCoordinateSchedule.bits_value])
  have hrs : rs = bits (Y % D) := (canon cr).trans (by simp only [vr, FlatCoordinateSchedule.bits_value])
  rw [hz, hrs] at hh
  have hh' : HoareTime (Arith.split (q := prime)) (fun w => w = Headers.bank (val (divRoute y d qo ro) c))
      (fun w => w = Headers.bank (val (divRoute y d qo ro)
        (Function.update (Function.update c qo (some (Y / D))) ro (some (Y % D)))))
      (BinaryDescriptorDivMod.cost (bits Y) (bits D)) := by
    rw [val_update (divRoute_inj h) (i₀ := 9) (by simp [divRoute]) _ (some (Y % D)),
      val_update (divRoute_inj h) (i₀ := 8) (by simp [divRoute]) _ (some (Y / D))]
    exact hh
  refine ⟨_, ?_, blk_runs (divRoute_inj h) _ hh' (fun j hj => ?_)⟩
  · have h1 := BinaryDescriptorDivMod.cost_linear (bits Y) (bits D) (FlatCoordinateSchedule.bits_canonical Y)
    rwa [FlatCoordinateSchedule.bits_value] at h1
  · have h₁ : j ≠ qo := fun he => hj 8 (by simp [divRoute, he])
    have h₂ : j ≠ ro := fun he => hj 9 (by simp [divRoute, he])
    rw [Function.update_of_ne h₂, Function.update_of_ne h₁]

end Steps

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Counters
