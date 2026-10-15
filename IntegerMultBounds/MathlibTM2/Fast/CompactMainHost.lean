module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainEntryTable
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainCleanup
public import IntegerMultBounds.MathlibTM2.Fast.CompactRetunedMainBound

/-! Close the actual expanded procedure table after a verified multiplication prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Computability
noncomputable section

/-- Append cleanup and reset to the arithmetic prefix. -/
def compactCompletedMain (p : CompactMnPr CompactMainProc (prime+mnKa)) :
    CompactMnPr CompactMainProc (prime+mnKa) :=
  .seq p (.seq compactMainClear compactMainReset)

def compactCompletedTable (p : CompactMnPr CompactMainProc (prime+mnKa)) :=
  compactMainEntryTable (compactCompletedMain p)

/-- One finite constant bounds pushes in both the prefix and every procedure body. -/
def compactCompletedPush (p : CompactMnPr CompactMainProc (prime+mnKa)) : ℕ :=
  max (mnProgPush p) (mnPushC (compactCompletedTable p))

def compactRetunedPreTime (extra n : ℕ) : ℕ :=
  compactMainPreCost compactRetunedDist
    (fun n => compactMainRuns compactRetunedDist compactRetunedCF compactRetunedCO n + extra) n

/-- A prefix with exact output and cleared left stacks gives the clean host contract. -/
theorem compactCompleted_hostMul
    (p : CompactMnPr CompactMainProc (prime+mnKa)) (extra x y : ℕ)
    {m : ℕ} {v : HS compactMnT compactMnQ (prime+mnKa) Unit}
    {S : Stacks compactMnT (prime+mnKa)}
    (he : Exec (compactCompletedTable p) p
      (Store.only compactMainV₀ .inp (pairEnc (x,y))) m (mk v S))
    (hm : m ≤ compactRetunedPreTime extra (pairEnc (x,y)).length)
    (hi : S.inp=[]) (ho : S.out=encodingNatBool.encode (x*y)) (hL : ∀ k,S.L k=[]) :
    HostMulWithin (compactCompletedTable p) (compactMainOldProc .main) compactMainV₀
      (compactRetunedTime (compactCompletedPush p) extra) x y := by
  have hp : mnProgPush p ≤ compactCompletedPush p := le_max_left _ _
  have hb : ∀ f,mnProgPush (compactCompletedTable p f) ≤ compactCompletedPush p :=
    fun f => (mn_progPush_le_pushC (compactCompletedTable p) f).trans (le_max_right _ _)
  obtain ⟨m',hm',he'⟩ := compactMain_finish (compactCompletedTable p) hb p hp
    (pairEnc (x,y)) (encodingNatBool.encode (x*y)) he hi ho hL
  refine ⟨m',?_,he'⟩
  change m'+2 ≤ compactRetunedPreTime extra (pairEnc (x,y)).length +
    2*((pairEnc (x,y)).length+compactCompletedPush p*compactRetunedPreTime extra (pairEnc (x,y)).length)+
    2*compactMnT+4
  have hc := Nat.mul_le_mul_left (compactCompletedPush p) hm
  omega

/-- The only remaining obligation is the actual arithmetic prefix execution. -/
theorem compactCompleted_mulInTime
    (p : CompactMnPr CompactMainProc (prime+mnKa)) (extra : ℕ)
    (hexec : ∀ᶠ n in atTop, ∀ x y, (pairEnc (x,y)).length=n →
      ∃ m v S, m ≤ compactRetunedPreTime extra n ∧
        Exec (compactCompletedTable p) p (Store.only compactMainV₀ .inp (pairEnc (x,y))) m (mk v S) ∧
        S.inp=[] ∧ S.out=encodingNatBool.encode (x*y) ∧ ∀ k,S.L k=[]) :
    MulInTime ((2^35:ℝ)⁻¹) := by
  apply compactRetuned_mulInTime_of_exec (compactCompletedTable p) (compactMainOldProc .main)
    compactMainV₀ (compactCompletedPush p) extra
  filter_upwards [hexec] with n hn x y hxy
  obtain ⟨m,v,S,hm,he,hi,ho,hL⟩ := hn x y hxy
  exact compactCompleted_hostMul p extra x y he (hxy ▸ hm) hi ho hL

end
end IntegerMultBounds.MathlibTM2.Fast.Main
