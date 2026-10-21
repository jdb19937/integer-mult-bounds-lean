module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomView
public import IntegerMultBounds.Machine.RecursiveScalarSchedule

/-!
# One refined atom operation on the role bank

A refined atom operation is an ordinary ordered-affine operation on the `N + N` atoms of the two
fields, each atom a coordinate of the atom width `b`. Stage 1 compiles such an operation to a view
selection and a scalar action (`RecursiveScalarSelection.compile`) and proves the semantics of the
viewed action at every coordinate count (`RecursiveScalarTransport.compile_entry`). Its physical
view preparation has the coordinate positions as program constants; here the positions are
counters (`words`), and the machine depends only on the kind of selection and on the action
(`machine`). `realizes`: with the counters of the selection on the first five auxiliary tapes, the
machine has exactly the stage-1 transformation of the role data (`RecursiveViewedAction.array`), so
`compile_entry` gives its semantics.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomStep

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection layout)
open RecursiveViewFrameRoleBank (count bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
variable {t u : ℕ}
noncomputable section

theorem hq : 2 ≤ prime := RecursiveViewRoleBank.prime_ge

/-- The counters of a selection: the atom width and four positions. -/
def words {N : ℕ} (b : ℕ) : Selection N → Fin 5 → List Bool
  | .cross i j => ![bits b, bits i.val, bits (N-1-i.val), bits j.val, bits (N-1-j.val)]
  | .within _ j i _ => ![bits b, bits j.val, bits (i.val-j.val-1), bits (N-1-i.val), bits N]

/-- The machine of one refined operation: it depends on the kind of selection only. -/
def machine {N : ℕ} (s : Selection N) (act : RecursiveViewedAction.Action t) :
    SharedBankSkeleton.Skeleton (count t (5+u)) prime :=
  match s with
  | .cross _ _ => AtomView.machine (u := u) (RuntimeCross.program hq) act
  | .within g _ _ _ => AtomView.machine (u := u) (RuntimeWithin.program hq g) act

theorem words_canonical {N : ℕ} (b : ℕ) (s : Selection N) (z : Fin 5) :
    GrowingCounterData.Canonical (words b s z) := by
  cases s <;> fin_cases z <;> exact FlatCoordinateSchedule.bits_canonical _

theorem layout_positive {N : ℕ} (s : Selection N) (b : ℕ) (v : Descriptor) (hp : v.Positive) :
    (layout s b v).Positive := by
  have hq' : 0 < prime := Networks.Shared50ModularControl.prime_prime.pos
  cases s with
  | cross i j =>
    exact RecursiveInterchangeLayout.child_positive prime 1 b v i j hq' one_pos (one_dvd _) hp
  | within g j i hj =>
    cases g
    · exact RecursiveAffineViews.withinH_positive prime b hq' v hp j i
    · exact RecursiveAffineViews.withinD_positive prime b hq' v hp j i

/-- **One refined atom operation.** With the counters of its selection on the first five
auxiliary tapes, the position-free machine transforms the role data exactly as stage 1's viewed
action. -/
theorem realizes {N b : ℕ} (hb0 : 0 < b) (s : Selection N) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes u prime)
    (data : RecursiveViewedAction.Data t v) :
    ∃ c, HoareTime (machine (u := u) s act).program
      (fun x => x = raw (bank (roles data) hs (SharedBank.empty 1 prime)
        ((AtomView.counters (words b s)).append aux)) (machine (u := u) s act).tapes)
      (fun x => x = raw (bank (roles (RecursiveViewedAction.array s act b v hw data)) hs
        (SharedBank.empty 1 prime) ((AtomView.counters (words b s)).append aux))
        (machine (u := u) s act).tapes) c := by
  have hc := words_canonical b s
  cases s with
  | cross i j =>
    obtain ⟨hch, hprep⟩ := RuntimeCross.prepares hq v hs (words b (.cross i j)) b i j hb0
      (FlatCoordinateSchedule.bits_value b) hc (FlatCoordinateSchedule.bits_value _)
      (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
      (FlatCoordinateSchedule.bits_value _) hv hp
    exact ⟨_, AtomView.realizes (RuntimeCross.program hq) act
      (RecursiveViewRoleBank.layout_volume (.cross i j) b v hw) hs _ (words b (.cross i j)) aux hch
      (layout_positive (.cross i j) b v hp) _ hprep data⟩
  | within g j i hji =>
    obtain ⟨hch, c, hprep, -⟩ := RuntimeWithin.prepares hq v hs (words b (.within g j i hji)) b j i g hb0
      (FlatCoordinateSchedule.bits_value b) hc (FlatCoordinateSchedule.bits_value _)
      (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
      (FlatCoordinateSchedule.bits_value _) hv hp
    exact ⟨_, AtomView.realizes (RuntimeWithin.program hq g) act
      (RecursiveViewRoleBank.layout_volume (.within g j i hji) b v hw) hs _ (words b (.within g j i hji))
      aux hch (layout_positive (.within g j i hji) b v hp) c hprep data⟩

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomStep
