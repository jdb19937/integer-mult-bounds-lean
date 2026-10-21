module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleInstall
public import IntegerMultBounds.Machine.ExactFrame

/-!
# One atom operation on the common role bank

The common bank of a segment is the role bank padded to `T` tapes, with zero position counters,
the atom count and a clock on its auxiliary tapes, and the loop count `f - 1` on its two last
tapes. One atom operation installs its first-level counters (`plan_words`), runs its level family
padded to `T` tapes, and resets the counters (`run_hoare`): the role data moves by the family's
refined operations and the rest of the bank is restored.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRun

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection)
open RecursiveViewFrameRoleBank (count)
open FlatCoordinateSchedule (bits)
open AtomRoleLoop (levelBank datas)
open AtomRoleOp (crossFamily withinFamily revFamily loopCost tapes_ge)
open AtomRolePlan (Kind Fits kind)
open AtomRoleInstall (fAux rest target)
open AtomSegment (planValue)
open AtomStep (words)
variable {t : ℕ}
noncomputable section

/-! ### The level loop of a family -/

section Loops

/-- The form of a level family: the kind of its selections and of its counter steps. A family's
machines depend on its form and action only. -/
inductive Form where
  | cross
  | within (g : RecursiveAffineDimensions.Group)
  | rev

/-- The machine of a form's refined operations. -/
def fmachine (F : Form) (act : RecursiveViewedAction.Action t) :
    SharedBankSkeleton.Skeleton (count t (5+2)) prime :=
  match F with
  | .cross => AtomView.machine (u := 2) (RuntimeCross.program AtomStep.hq) act
  | .within g => AtomView.machine (u := 2) (RuntimeWithin.program AtomStep.hq g) act
  | .rev => AtomView.machine (u := 2) (RuntimeCross.program AtomStep.hq) act

/-- The tapes of a form's refined operations. -/
def ftapes (F : Form) (act : RecursiveViewedAction.Action t) : ℕ := (fmachine F act).tapes

theorem ftapes_ge (F : Form) (act : RecursiveViewedAction.Action t) :
    count t (5+2) + 2 ≤ ftapes F act := by
  cases F <;> simp [ftapes, fmachine, AtomView.machine, SharedBankSkeleton.compose,
    AtomView.viewSkeleton] <;> omega

/-- The level loop of a form: one fixed program for every atom count and every position. -/
def fprogram : (F : Form) → (act : RecursiveViewedAction.Action t) →
    (q : ℕ) × Program (ftapes F act + 2) q prime
  | .cross, act => ⟨_, LevelLoop.program (seq (fmachine .cross act).program
      (AtomRoleSteps.crossSteps _ (ftapes_ge .cross act))) (fmachine .cross act).program⟩
  | .within g, act => ⟨_, LevelLoop.program (seq (fmachine (.within g) act).program
      (AtomRoleSteps.withinSteps _ (ftapes_ge (.within g) act))) (fmachine (.within g) act).program⟩
  | .rev, act => ⟨_, LevelLoop.program (seq (fmachine .rev act).program
      (AtomRoleSteps.revSteps _ (ftapes_ge .rev act))) (fmachine .rev act).program⟩

variable {f N : ℕ}

/-- The form of a level family. -/
def kform : Kind f N → Form
  | .cross .. => .cross
  | .within g .. => .within g
  | .rev .. => .rev

theorem kloop_hoare {b : ℕ} (hb0 : 0 < b) (K : Kind f N) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes 2 prime) (hf : 0 < f)
    (data : RecursiveViewedAction.Data t v) :
    HoareTime (fprogram (kform K) act).2
      (fun x => x = LevelLoop.bank (levelBank (ftapes (kform K) act) hs aux data (words b (K.sel 0))) f)
      (fun x => x = LevelLoop.bank (levelBank (ftapes (kform K) act) hs aux (datas K.sel act v hw data f)
        (words b (K.sel (f-1)))) f)
      (loopCost (N := N) f act (volume prime v)) := by
  cases K with
  | cross i₀ j₀ hi hj => exact AtomRoleOp.cross_loop f hb0 act v hw hp hs hv aux hf data i₀ j₀ hi hj
  | within g j₀ i₀ hji hi => exact AtomRoleOp.within_loop f hb0 act v hw hp hs hv aux hf data g j₀ i₀ hji hi
  | rev i₀ j₀ hi0 hi hj => exact AtomRoleOp.rev_loop f hb0 act v hw hp hs hv aux hf data i₀ j₀ hi0 hi hj

end Loops

/-! ### Counters as values -/

/-- The four positions of a selection's counters. -/
def vals {N : ℕ} : Selection N → Fin 4 → ℕ
  | .cross i j => ![i.val, N-1-i.val, j.val, N-1-j.val]
  | .within _ j i _ => ![j.val, i.val-j.val-1, N-1-i.val, N]

theorem words_target {N : ℕ} (b : ℕ) (s : Selection N) : words b s = target b (vals s) := by
  cases s <;> funext z <;> fin_cases z <;> rfl

/-! ### The plan of an atom operation's first level -/

variable {m f : ℕ}

/-- The first-level counters of an atom operation, as multiples of `f`, less one or not. -/
def plan : AtomOps.AtomOp (m+m) ℚ → Fin 4 → ℕ × Bool
  | .scale tt _ =>
    if tt.val < m then ![(tt.val, false), (m-tt.val, true), (tt.val, false), (m-tt.val, true)]
    else ![(tt.val-m, false), (m+m-tt.val, true), (tt.val-m, false), (m+m-tt.val, true)]
  | .shift tt k _ =>
    if tt.val < m then ![(k.val, false), (tt.val-k.val, true), (m-tt.val, true), (m, false)]
    else if k.val < m then ![(k.val, false), (m-k.val, true), (tt.val-m, false), (m+m-tt.val, true)]
    else ![(k.val-m, false), (tt.val-k.val, true), (m+m-tt.val, true), (m, false)]
  | .revShift tt k _ => ![(k.val+1, true), (m-k.val-1, false), (tt.val-m, false), (m+m-tt.val, true)]

theorem plan_words (b : ℕ) (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) :
    words b ((kind hf op hop).sel 0) = target b (fun j => planValue f (plan op j)) := by
  rw [words_target]
  congr 1
  funext z
  have hsub (x y : ℕ) : (x - y) * f = x*f - y*f := Nat.sub_mul x y f
  cases op with
  | scale tt c =>
    have htt := tt.isLt
    by_cases h : tt.val < m
    · have := AtomRolePlan.pos_lt h hf
      simp only [kind, h, dite_true, Kind.sel, crossFamily, vals, plan, ite_true]
      fin_cases z <;> simp [planValue, hsub] <;> omega
    · have hd := AtomRolePlan.d_val (f := f) tt (by omega)
      have := AtomRolePlan.pos_lt_d tt (by omega) hf
      simp only [kind, h, dite_false, Kind.sel, crossFamily, vals, plan, ite_false]
      fin_cases z <;> simp [planValue, hsub, Nat.add_mul] <;> omega
  | shift tt k c =>
    have htt := tt.isLt
    have hk : k.val < tt.val := hop.1
    have hkf := Nat.mul_le_mul_right f hk.le
    by_cases ht : tt.val < m
    · have := AtomRolePlan.pos_lt ht hf
      simp only [kind, ht, dite_true, Kind.sel, withinFamily, vals, plan, ite_true]
      fin_cases z <;> simp [planValue, hsub]
      all_goals omega
    · have hd := AtomRolePlan.d_val (f := f) tt (by omega)
      have := AtomRolePlan.pos_lt_d tt (by omega) hf
      by_cases hkm : k.val < m
      · have := AtomRolePlan.pos_lt hkm hf
        simp only [kind, ht, hkm, dite_true, dite_false, Kind.sel, crossFamily, vals, plan, ite_true, ite_false]
        fin_cases z <;> simp [planValue, hsub, Nat.add_mul] <;> omega
      · have hd' := AtomRolePlan.d_val (f := f) k (by omega)
        simp only [kind, ht, hkm, dite_false, Kind.sel, withinFamily, vals, plan, ite_false]
        fin_cases z <;> simp [planValue, hsub, Nat.add_mul] <;> omega
  | revShift tt k c =>
    have htt := tt.isLt
    have hd := AtomRolePlan.d_val (f := f) tt hop.2.1
    have := AtomRolePlan.pos_lt_d tt hop.2.1 hf
    have := AtomRolePlan.pos_lt hop.1 hf
    simp only [kind, Kind.sel, revFamily, vals, plan]
    fin_cases z <;> simp [planValue, hsub, Nat.add_mul] <;> omega

theorem plan_dec (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (j : Fin 4) :
    (if (plan op j).2 then 1 else 0) ≤ (plan op j).1 * f := by
  have hpos (c : ℕ) (hc : 1 ≤ c) : 1 ≤ c * f := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  cases op with
  | scale tt c =>
    have htt := tt.isLt
    by_cases h : tt.val < m <;> fin_cases j <;> simp [plan, h] <;> apply hpos <;> omega
  | shift tt k c =>
    have htt := tt.isLt
    have hk : k.val < tt.val := hop.1
    by_cases ht : tt.val < m
    · fin_cases j <;> simp [plan, ht] <;> apply hpos <;> omega
    · by_cases hkm : k.val < m <;> fin_cases j <;> simp [plan, ht, hkm] <;> apply hpos <;> omega
  | revShift tt k c =>
    have htt := tt.isLt
    fin_cases j <;> simp [plan] <;> apply hpos <;> omega

/-! ### One atom operation -/

/-- The common bank of a segment. -/
def common (T : ℕ) {v : Descriptor} (hs : Fin 6 → List Bool) (f b : ℕ) (data : RecursiveViewedAction.Data t v) :
    Tapes (T+2) prime :=
  LevelLoop.bank (levelBank T hs (fAux f) data (rest b)) f

/-- The form of an atom operation's level family; it does not depend on the atom count. -/
def opForm : (op : AtomOps.AtomOp (m+m) ℚ) → Fits m op → Form
  | .scale _ _, _ => .cross
  | .shift tt k _, _ =>
    if tt.val < m then .within .h else if k.val < m then .cross else .within .d
  | .revShift _ _ _, _ => .rev

theorem kind_form (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) :
    kform (kind hf op hop) = opForm op hop := by
  cases op with
  | scale tt c => by_cases h : tt.val < m <;> simp [kind, h, kform, opForm]
  | shift tt k c =>
    by_cases ht : tt.val < m
    · simp [kind, ht, kform, opForm]
    · by_cases hk : k.val < m <;> simp [kind, ht, hk, kform, opForm]
  | revShift tt k c => rfl

theorem run_tapes (T : ℕ) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (wire : Fin t)
    (hle : ftapes (opForm op hop) (AtomRolePlan.act wire op hop) ≤ T) : count t (5+2) + 2 ≤ T :=
  (ftapes_ge (opForm op hop) _).trans hle

/-- **One atom operation on the common bank.** The program depends on the operation and the
wire only: the atom count and the positions are on the tapes. -/
def opRun (T : ℕ) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (wire : Fin t)
    (hle : ftapes (opForm op hop) (AtomRolePlan.act wire op hop) ≤ T) :=
  seq (seq (extend (AtomRoleInstall.setup T (run_tapes T op hop wire hle) (plan op)) 2)
    (Placement.placed (fprogram (opForm op hop) (AtomRolePlan.act wire op hop)).2
      (AtomRolePad.placement _ T hle)))
    (extend (AtomRoleInstall.eraseAll T (run_tapes T op hop wire hle)) 2)

/-- The cost of one atom operation. -/
def runCost (f : ℕ) (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (wire : Fin t) (V : ℕ) : ℕ :=
  AtomRoleInstall.setupCost f (plan op) + 1 + loopCost (N := m*f) f (AtomRolePlan.act wire op hop) V + 1 +
    AtomRoleInstall.eraseCost (vals ((kind hf op hop).sel (f-1)))

theorem run_hoare {b : ℕ} (hb0 : 0 < b) (T : ℕ) (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op)
    (wire : Fin t) (hle : ftapes (opForm op hop) (AtomRolePlan.act wire op hop) ≤ T)
    (v : Descriptor) (hw : v.width = (m*f)*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (data : RecursiveViewedAction.Data t v) :
    HoareTime (opRun T op hop wire hle) (fun x => x = common T hs f b data)
      (fun x => x = common T hs f b (datas (kind hf op hop).sel (AtomRolePlan.act wire op hop) v hw data f))
      (runCost f hf op hop wire (volume prime v)) := by
  have hT := run_tapes T op hop wire hle
  have h1 := hoare_extend_eq
    (AtomRoleInstall.setup_hoare T hT hs data f b (plan op) (plan_dec hf op hop))
    (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary (bits (f-1))) 1 1)
  have hL := kloop_hoare hb0 (kind hf op hop) (AtomRolePlan.act wire op hop) v hw hp hs hv (fAux f) hf data
  rw [kind_form hf op hop] at hL
  have hk := ftapes_ge (opForm op hop) (AtomRolePlan.act wire op hop)
  have h2 := AtomRolePad.pad_hoare (k := count t (5+2)) hle (by omega) _ _ _ f hL
  rw [plan_words b hf op hop, words_target] at h2
  have h3 := hoare_extend_eq
    (AtomRoleInstall.eraseAll_hoare T hT hs (datas (kind hf op hop).sel (AtomRolePlan.act wire op hop) v hw data f)
      f b (vals ((kind hf op hop).sel (f-1))))
    (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary (bits (f-1))) 1 1)
  exact (h1.seq h2).seq h3

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRun
