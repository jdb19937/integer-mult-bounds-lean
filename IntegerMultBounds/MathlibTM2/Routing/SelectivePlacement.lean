module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveProgram

/-!
# A concrete finite register bank for selective routing

Distinct roles receive distinct physical registers. The callback target alone
aliases its live field counter. Configuration inputs and both swap banks have
separate roles, so the full setup and execution separation contracts are inhabited.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

instance : Fintype Off :=
  Fintype.ofList [.A, .Z, .Y, .YZ, .X] (by intro off; cases off <;> simp)
deriving instance Fintype for PatternReg
instance : Fintype SetupKey := Fintype.ofList setupKeys setupKeys_mem

inductive SelectiveReg where
  | field (f : Fin 5)
  | callback (off : Off) (r : PatternReg 2)
  | src | out | ctr | tmp | cnt | ctmp
  | dst (d : Fin 2)
  | aux (d : Fin 2)
  | swap (c : Fin 2) (j : Fin (swapT 6))
  | config (key : SetupKey)
  deriving DecidableEq, Fintype

abbrev selectiveT : ℕ := Fintype.card SelectiveReg

noncomputable def selectiveReg : SelectiveReg → Fin selectiveT := Fintype.equivFin _

@[simp] theorem selectiveReg_inj {a b : SelectiveReg} :
    selectiveReg a = selectiveReg b ↔ a = b := (Fintype.equivFin SelectiveReg).injective.eq_iff

noncomputable def placedSelectiveHost : SelectiveHost selectiveT where
  cf f := selectiveReg (.field f)
  cb off r := if r = .fld 1 then selectiveReg (.field (selectiveTgt off))
    else selectiveReg (.callback off r)
  src := selectiveReg .src
  dst d := selectiveReg (.dst d)
  aux d := selectiveReg (.aux d)
  out := selectiveReg .out
  ctr := selectiveReg .ctr
  tmp := selectiveReg .tmp
  cnt := selectiveReg .cnt
  ctmp := selectiveReg .ctmp
  swaps c j := selectiveReg (.swap c j)

noncomputable def placedSelectiveConfig (key : SetupKey) : Fin selectiveT :=
  selectiveReg (.config key)

theorem placedSelectiveHost_valid : placedSelectiveHost.Valid := by
  constructor
  · intro off
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro f g he
      simpa [placedSelectiveHost] using he
    · intro r s he
      by_cases hr : r = PatternReg.fld 1 <;> by_cases hs : s = PatternReg.fld 1
      · exact hr.trans hs.symm
      · simp [placedSelectiveHost, hr, hs] at he
      · simp [placedSelectiveHost, hr, hs] at he
      · simpa [placedSelectiveHost, hr, hs] using he
    · simp [placedSelectiveHost]
    · intro r hr f
      simp [placedSelectiveHost, hr]
  · intro off
    constructor
    · simp [placedSelectiveHost]
    · intro d; simp [placedSelectiveHost]
    · intro d; simp [placedSelectiveHost]
    · intro d e; simp [placedSelectiveHost]
    · intro d e he; simpa [placedSelectiveHost] using he
    · intro d e he; simpa [placedSelectiveHost] using he
    · intro k hk
      rcases hk with ⟨f, rfl⟩ | ⟨r, rfl⟩
      · simp [placedSelectiveHost]
      · by_cases hr : r = PatternReg.fld 1 <;> simp [placedSelectiveHost, hr]
    · intro d hk
      rcases hk with ⟨f, he⟩ | ⟨r, he⟩
      · simp [placedSelectiveHost] at he
      · by_cases hr : r = PatternReg.fld 1 <;> simp [placedSelectiveHost, hr] at he
    · intro d hk
      rcases hk with ⟨f, he⟩ | ⟨r, he⟩
      · simp [placedSelectiveHost] at he
      · by_cases hr : r = PatternReg.fld 1 <;> simp [placedSelectiveHost, hr] at he
  · intro c i j he; simpa [placedSelectiveHost] using he
  · intro c j; simp [placedSelectiveHost]
  · intro c j; simp [placedSelectiveHost]

noncomputable def placedSetupRole : SetupKey → SelectiveReg
  | .field f => .field f
  | .desc off k => .callback off (.desc k)
  | .block => .ctr
  | .records => .cnt
  | .header c k => .swap c (reg (selectiveSwapHd k))

theorem placedSetup_target (key : SetupKey) :
    key.target placedSelectiveHost = selectiveReg (placedSetupRole key) := by
  cases key <;> simp [SetupKey.target, placedSelectiveHost, placedSetupRole]

theorem placedSetupRole_injective : Function.Injective placedSetupRole := by
  intro key other he
  cases key <;> cases other <;> simp_all [placedSetupRole]
  rename_i c k d j
  obtain ⟨rfl, he⟩ := he
  have hk := selectiveSwapHd_inj (swapReg_injective he)
  exact hk

theorem placedSelectiveHost_setup : SetupLayout placedSelectiveHost placedSelectiveConfig := by
  constructor
  · intro key other he
    simp only [placedSetup_target, selectiveReg_inj] at he
    exact placedSetupRole_injective he
  · intro key
    cases key <;> simp [placedSelectiveConfig, SetupKey.target, placedSelectiveHost]
  · intro key other
    cases other <;> simp [placedSelectiveConfig, SetupKey.target, placedSelectiveHost]
  · intro key k hk
    rcases hk with hk | ⟨d, rfl⟩ | ⟨d, rfl⟩ | ⟨off, r, hr, hd, rfl⟩ | ⟨c, j, hj, rfl⟩
    · simp only [placedSelectiveHost, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;>
        cases key <;> simp [SetupKey.target, placedSelectiveHost]
    · cases key <;> simp [SetupKey.target, placedSelectiveHost]
    · cases key <;> simp [SetupKey.target, placedSelectiveHost]
    · rw [placedSetup_target]
      simp only [placedSelectiveHost, hr, ↓reduceIte]
      intro he
      have he := selectiveReg_inj.mp he
      cases key with
      | desc off' d => exact hd d (SelectiveReg.callback.inj he).2.symm
      | field f => cases he
      | block => cases he
      | records => cases he
      | header c k => cases he
    · rw [placedSetup_target]
      simp only [placedSelectiveHost]
      intro he
      have he := selectiveReg_inj.mp he
      cases key with
      | field f => cases he
      | desc off d => cases he
      | block => cases he
      | records => cases he
      | header d h =>
        have hv := congrArg Fin.val (SelectiveReg.swap.inj he).2
        rcases hj with hj | hj
        · rw [hj] at hv
          simp only [reg_val, selectiveSwapHd, selectiveSwapPay] at hv
          omega
        · simp only [reg_val, selectiveSwapHd] at hv
          omega

  · intro key
    simp [placedSelectiveConfig, placedSelectiveHost]

theorem placedSelectiveHost_swapT : swapT 6 ≤ selectiveT := by
  have h := Fintype.card_le_of_injective (SelectiveReg.swap 0)
    (fun _ _ he => (SelectiveReg.swap.inj he).2)
  simpa using h

end
end IntegerMultBounds.MathlibTM2.Routing
