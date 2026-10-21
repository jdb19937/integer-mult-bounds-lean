module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomStep

/-!
# The cost of one refined atom operation

Every descriptor that the runtime views compute is a factor of the view's volume, which is the
parent's volume, and every canonical word is at most its value plus one bit long. So one refined
atom operation costs at most a constant times the volume, with the constant depending on the
action only (`realizes_le`). This is the uniform per-level cost of the level loops.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomStepCost

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection layout)
open RecursiveViewFrameRoleBank (count bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open AtomStep (hq words machine)
variable {t u : ℕ}
noncomputable section

theorem len_le (xs : List Bool) (cx : GrowingCounterData.Canonical xs) :
    xs.length ≤ Counter.value xs + 1 := by
  have h := GrowingCounterData.canonical_width xs cx
  have := Nat.log2_le_self (Counter.value xs)
  omega

/-- The factors of a positive descriptor are at most its volume. -/
theorem factors_le (v : Descriptor) (hp : v.Positive) :
    v.beforeH ≤ volume prime v ∧ v.between ≤ volume prime v ∧ v.afterD ≤ volume prime v ∧
      prime^v.width ≤ volume prime v ∧ v.rows ≤ volume prime v := by
  rcases hp with ⟨hA, hR, hB, hC, hE⟩
  have hQ : 0 < prime^v.width := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> unfold volume
  · calc v.beforeH ≤ v.beforeH * (v.beforeRows*v.rows*prime^v.width*v.between*prime^v.width*v.afterD) :=
          Nat.le_mul_of_pos_right _ (by positivity)
      _ = _ := by ring
  · calc v.between ≤ v.between * (v.beforeRows*v.rows*v.beforeH*prime^v.width*prime^v.width*v.afterD) :=
          Nat.le_mul_of_pos_right _ (by positivity)
      _ = _ := by ring
  · exact Nat.le_mul_of_pos_left _ (by positivity)
  · calc prime^v.width ≤ prime^v.width * (v.beforeRows*v.rows*v.beforeH*v.between*prime^v.width*v.afterD) :=
          Nat.le_mul_of_pos_right _ (by positivity)
      _ = _ := by ring
  · calc v.rows ≤ v.rows * (v.beforeRows*v.beforeH*prime^v.width*v.between*prime^v.width*v.afterD) :=
          Nat.le_mul_of_pos_right _ (by positivity)
      _ = _ := by ring

theorem header_len (v : Descriptor) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (z : Fin 6) : (hs z).length ≤ 2*volume prime v := by
  have h := RecursiveAffinePrepare.header_log hq v hp hs hv z
  have := Nat.log2_le_self (volume prime v)
  have := RecursiveAffinePrepare.volume_positive hq v hp
  omega

theorem lt_pow (n : ℕ) : n < prime^n := Nat.lt_pow_self (by have := hq; omega)

/-- The cost of the action, linear in the volume. -/
theorem action_le (act : RecursiveViewedAction.Action t) (w : Descriptor) (hV : 0 < volume prime w) :
    RecursiveViewedAction.cost w act ≤ RecursiveViewedAction.coefficient act * volume prime w := by
  cases act with
  | shift wire r hd =>
    simp only [RecursiveViewedAction.cost, RecursiveViewedAction.coefficient]; omega
  | scale wire r hr target =>
    have hh := RecursiveInterchangeScalingClean.bound_linear r _ hV
    simp only [RecursiveViewedAction.cost, RecursiveViewedAction.coefficient]
    convert hh using 1
    unfold RecursiveInterchangeScalingClean.bound
    ring

/-- The constant of one refined atom operation. -/
def constant (act : RecursiveViewedAction.Action t) : ℕ := 3000+RecursiveViewedAction.coefficient act

theorem prefix_len (k b : ℕ) (hk : prime^(k*b) ≤ V) :
    (RadixPowerDescriptor.bits hq (k*b)).length ≤ V+1 := by
  have := len_le _ (RadixPowerDescriptor.bits_canonical hq (k*b))
  rw [RadixPowerDescriptor.bits_value] at this
  omega

theorem product_len (N W V : ℕ) (h : N*W ≤ V) : (DimensionProductDescriptor.bits N W).length ≤ V+1 := by
  have := len_le _ (DimensionProductDescriptor.bits_canonical N W)
  rw [DimensionProductDescriptor.bits_value] at this
  omega

/-- **The bounded cross step.** -/
theorem cross_le {N b : ℕ} (hb0 : 0 < b) (i j : Fin N) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes u prime)
    (data : RecursiveViewedAction.Data t v) :
    HoareTime (machine (u := u) (.cross i j) act).program
      (fun x => x = raw (bank (roles data) hs (SharedBank.empty 1 prime)
        ((AtomView.counters (words b (.cross i j))).append aux)) (machine (u := u) (.cross i j) act).tapes)
      (fun x => x = raw (bank (roles (RecursiveViewedAction.array (.cross i j) act b v hw data)) hs
        (SharedBank.empty 1 prime) ((AtomView.counters (words b (.cross i j))).append aux))
        (machine (u := u) (.cross i j) act).tapes) (constant act * volume prime v) := by
  have hc := AtomStep.words_canonical b (.cross i j)
  obtain ⟨hch, hprep⟩ := RuntimeCross.prepares hq v hs (words b (.cross i j)) b i j hb0
    (FlatCoordinateSchedule.bits_value b) hc (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_value _) hv hp
  have he := RecursiveViewRoleBank.layout_volume (.cross i j) b v hw
  have hwp := AtomStep.layout_positive (.cross i j) b v hp
  have hh := AtomView.realizes (u := u) (RuntimeCross.program hq) act he hs _ (words b (.cross i j)) aux hch
    hwp _ hprep data
  refine hh.consequence (fun _ h => h) (fun _ h => h) ?_
  -- the bounds
  set V := volume prime v with hVdef
  have hV : 0 < V := RecursiveAffinePrepare.volume_positive hq v hp
  obtain ⟨fB, fC, fE, fQ, -⟩ := factors_le _ hwp
  rw [he] at fB fC fE fQ
  change v.beforeH * prime^(i.val*b) ≤ V at fB
  change prime^((N-1-i.val)*b) * v.between * prime^(j.val*b) ≤ V at fC
  change prime^((N-1-j.val)*b) * v.afterD ≤ V at fE
  change prime^b ≤ V at fQ
  have hp' := hp
  rcases hp' with ⟨-, -, hB, hC, hE⟩
  have q1 : prime^(i.val*b) ≤ V := le_trans (Nat.le_mul_of_pos_left _ hB) fB
  have m1 : prime^((N-1-i.val)*b) * v.between ≤ V := le_trans (Nat.le_mul_of_pos_right _ (pow_pos (by have := hq; omega) _)) fC
  have q2 : prime^((N-1-i.val)*b) ≤ V := le_trans (Nat.le_mul_of_pos_right _ hC) m1
  have q3 : prime^(j.val*b) ≤ V := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (pow_pos (by have := hq; omega) _) hC)) fC
  have q4 : prime^((N-1-j.val)*b) ≤ V := le_trans (Nat.le_mul_of_pos_right _ hE) fE
  have k1 := lt_pow (i.val*b)
  have k2 := lt_pow ((N-1-i.val)*b)
  have k3 := lt_pow (j.val*b)
  have k4 := lt_pow ((N-1-j.val)*b)
  have kb := lt_pow b
  have p1 := RuntimePower.cost_le (q := prime) i.val b
  have p2 := RuntimePower.cost_le (q := prime) (N-1-i.val) b
  have p3 := RuntimePower.cost_le (q := prime) j.val b
  have p4 := RuntimePower.cost_le (q := prime) (N-1-j.val) b
  have l1 := prefix_len (V := V) i.val b q1
  have l2 := prefix_len (V := V) (N-1-i.val) b q2
  have l3 := prefix_len (V := V) j.val b q3
  have l4 := prefix_len (V := V) (N-1-j.val) b q4
  have l5 := product_len _ _ V m1
  have lw : (bits b).length ≤ V+1 := by
    have := len_le _ (FlatCoordinateSchedule.bits_canonical b)
    rw [FlatCoordinateSchedule.bits_value] at this; omega
  have lh := header_len v hp hs hv 1
  have hold (z : Fin 6) := header_len v hp hs hv z
  have hnew (z : Fin 6) : (RecursiveChildDimensions.childHeaders (q := prime) v hs (words b (.cross i j) 0)
      (hs 1) b i j z).length ≤ 2*V := by
    have := header_len _ hwp _ hch z; rwa [he] at this
  have hpush := RecursiveViewFrame.pushCost_le hs (2*V) hold
  have hrest := RecursiveViewFrame.restoreCost_le hs _ (2*V) hold hnew
  have hhand := RecursiveChildHeaderHandoff.cost_le hs _ (2*V) hold hnew
  have hact := action_le act _ (by rw [he]; exact hV)
  rw [he] at hact
  unfold RuntimeCross.cost RuntimeCross.constructCost RuntimeCross.cleanCost constant
  simp only [RecursiveChildDimensions.prefixBits, RadixPowerMultipleDescriptor.bits,
    RecursiveChildDimensions.middleBits, words, Matrix.cons_val_zero] at *
  nlinarith

/-- **The bounded within-field step.** -/
theorem within_le {N b : ℕ} (hb0 : 0 < b) (g : RecursiveAffineDimensions.Group) (j i : Fin N)
    (hji : j < i) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes u prime)
    (data : RecursiveViewedAction.Data t v) :
    HoareTime (machine (u := u) (.within g j i hji) act).program
      (fun x => x = raw (bank (roles data) hs (SharedBank.empty 1 prime)
        ((AtomView.counters (words b (.within g j i hji))).append aux))
        (machine (u := u) (.within g j i hji) act).tapes)
      (fun x => x = raw (bank (roles (RecursiveViewedAction.array (.within g j i hji) act b v hw data)) hs
        (SharedBank.empty 1 prime) ((AtomView.counters (words b (.within g j i hji))).append aux))
        (machine (u := u) (.within g j i hji) act).tapes) (constant act * volume prime v) := by
  have hc := AtomStep.words_canonical b (.within g j i hji)
  obtain ⟨hch, c, hprep, hceq⟩ := RuntimeWithin.prepares hq v hs (words b (.within g j i hji)) b j i g hb0
    (FlatCoordinateSchedule.bits_value b) hc (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_value _) hv hp
  have he := RecursiveViewRoleBank.layout_volume (.within g j i hji) b v hw
  have hwp := AtomStep.layout_positive (.within g j i hji) b v hp
  have hh := AtomView.realizes (u := u) (RuntimeWithin.program hq g) act he hs _
    (words b (.within g j i hji)) aux hch hwp c hprep data
  refine hh.consequence (fun _ h => h) (fun _ h => h) ?_
  set V := volume prime v with hVdef
  have hV : 0 < V := RecursiveAffinePrepare.volume_positive hq v hp
  obtain ⟨fB, fC, fE, fQ, -⟩ := factors_le _ hwp
  rw [he] at fB fC fE fQ
  have hp' := hp
  rcases hp' with ⟨-, -, hB, hC, hE⟩
  have hq0 : ∀ n, 0 < prime^n := fun n => pow_pos (by have := hq; omega) n
  have k1 := lt_pow (j.val*b)
  have k2 := lt_pow ((i.val-j.val-1)*b)
  have k3 := lt_pow ((N-1-i.val)*b)
  have k4 := lt_pow (N*b)
  have kb := lt_pow b
  have p1 := RuntimePower.cost_le (q := prime) j.val b
  have p2 := RuntimePower.cost_le (q := prime) (i.val-j.val-1) b
  have p3 := RuntimePower.cost_le (q := prime) (N-1-i.val) b
  have p4 := RuntimePower.cost_le (q := prime) N b
  have lwb : (bits b).length ≤ b+1 := by
    have := len_le _ (FlatCoordinateSchedule.bits_canonical b)
    rwa [FlatCoordinateSchedule.bits_value] at this
  have hold (z : Fin 6) := header_len v hp hs hv z
  have lh := hold 1
  have hnew (z : Fin 6) : (RuntimeWithin.headers hq v hs (words b (.within g j i hji)) b j i g z).length ≤ 2*V := by
    have := header_len _ hwp _ hch z; rwa [he] at this
  have hpush := RecursiveViewFrame.pushCost_le hs (2*V) hold
  have hrest := RecursiveViewFrame.restoreCost_le hs _ (2*V) hold hnew
  have hhand := RecursiveChildHeaderHandoff.cost_le hs _ (2*V) hold hnew
  have hact := action_le act _ (by rw [he]; exact hV)
  rw [he] at hact
  rw [hceq]
  cases g with
  | h =>
    change v.beforeH * prime^(j.val*b) ≤ V at fB
    change prime^((i.val-j.val-1)*b) ≤ V at fC
    change prime^((N-1-i.val)*b) * v.between * prime^(N*b) * v.afterD ≤ V at fE
    change prime^b ≤ V at fQ
    have q1 : prime^(j.val*b) ≤ V := le_trans (Nat.le_mul_of_pos_left _ hB) fB
    have t2 : prime^((N-1-i.val)*b) * v.between * prime^(N*b) ≤ V :=
      le_trans (Nat.le_mul_of_pos_right _ hE) fE
    have t1 : prime^((N-1-i.val)*b) * v.between ≤ V := le_trans (Nat.le_mul_of_pos_right _ (hq0 _)) t2
    have q3 : prime^((N-1-i.val)*b) ≤ V := le_trans (Nat.le_mul_of_pos_right _ hC) t1
    have q4 : prime^(N*b) ≤ V := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (hq0 _) hC)) t2
    have l1 := prefix_len (V := V) j.val b q1
    have l3 := prefix_len (V := V) (N-1-i.val) b q3
    have l4 := prefix_len (V := V) N b q4
    have l5 := product_len _ _ V t1
    have l6 := product_len _ _ V t2
    unfold RuntimeWithin.cleanCost RuntimeWithin.erased RuntimeWithin.powerCost constant
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val,
      Matrix.vecHead, Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one, words] at *
    linarith
  | d =>
    change v.beforeH * prime^(N*b) * v.between * prime^(j.val*b) ≤ V at fB
    change prime^((i.val-j.val-1)*b) ≤ V at fC
    change prime^((N-1-i.val)*b) * v.afterD ≤ V at fE
    change prime^b ≤ V at fQ
    have u2 : v.beforeH * prime^(N*b) * v.between ≤ V := le_trans (Nat.le_mul_of_pos_right _ (hq0 _)) fB
    have u1 : v.beforeH * prime^(N*b) ≤ V := le_trans (Nat.le_mul_of_pos_right _ hC) u2
    have q1 : prime^(j.val*b) ≤ V :=
      le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hB (hq0 _)) hC)) fB
    have q4 : prime^(N*b) ≤ V := le_trans (Nat.le_mul_of_pos_left _ hB) u1
    have q3 : prime^((N-1-i.val)*b) ≤ V := le_trans (Nat.le_mul_of_pos_right _ hE) fE
    have l1 := prefix_len (V := V) j.val b q1
    have l3 := prefix_len (V := V) (N-1-i.val) b q3
    have l4 := prefix_len (V := V) N b q4
    have l5 := product_len _ _ V u1
    have l6 := product_len _ _ V u2
    unfold RuntimeWithin.cleanCost RuntimeWithin.erased RuntimeWithin.powerCost constant
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val,
      Matrix.vecHead, Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one, words] at *
    linarith

/-- **One refined atom operation within a constant times the volume.** -/
theorem realizes_le {N b : ℕ} (hb0 : 0 < b) (s : Selection N) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes u prime)
    (data : RecursiveViewedAction.Data t v) :
    HoareTime (machine (u := u) s act).program
      (fun x => x = raw (bank (roles data) hs (SharedBank.empty 1 prime)
        ((AtomView.counters (words b s)).append aux)) (machine (u := u) s act).tapes)
      (fun x => x = raw (bank (roles (RecursiveViewedAction.array s act b v hw data)) hs
        (SharedBank.empty 1 prime) ((AtomView.counters (words b s)).append aux))
        (machine (u := u) s act).tapes) (constant act * volume prime v) := by
  cases s with
  | cross i j => exact cross_le hb0 i j act v hw hp hs hv aux data
  | within g j i hji => exact within_le hb0 g j i hji act v hw hp hs hv aux data

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomStepCost
