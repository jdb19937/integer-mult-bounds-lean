module

public import IntegerMultBounds.MathlibTM2.Fast.DistWid
public import IntegerMultBounds.MathlibTM2.Fast.DistSpec
public import IntegerMultBounds.MathlibTM2.Fast.DistCostSrc

/-!
# The parameter distribution machine, assembled

`dsMain rg g = dsWid rg g; dsSrc rg g` is one fixed program running after the parameter
machine (`Fast/ParamMachine.lean`) on its table layout `rg : TblR pmNV → Fin T` and on the
registers `g = dsGY M.rg io` of the source transform (`M : SrcMach`, `Fast/SrcPhase.lean`) and
of the converter (`io : DsX → Fin T`, `Fast/DistSrcBase.lean`). It reads the parameters
`pmVals n` from the layout, computes the pipeline widths `w = dsW n`, `W = dsWW n`
(`Fast/DistWid.lean`), and writes the register file between runs of the source transform
(`dsSrcE`, `Fast/DistSpec.lean`) onto the registers of `M.rg`.

* `ds_main_runs`: from the layout carrying `pmVals n` and every register of the family empty,
  `dsMain` ends with the family holding `dsFinal n` (the source-transform file `dsSrcE` on
  `M.rg`, the unary widths and the layout-stage parameters on `io`), the layout as it started,
  within `dsMainCost n` steps (`Fast/DistCostSrc.lean`).
* `dsAll rg uN oT oS us g = pmParams rg uN oT oS us; dsMain rg g`, `dsAll_exec`: from `n`
  symbols on `uN` and the layout and family registers empty, the register file of the source
  transform is `dsSrcE n (dsW n) (dsWW n) _` on `M.rg`, which is a register file between runs
  (`dsAll_base`: `SrcBase`, `SrcCrtBase`, `a .ln`, `c .str`, `x .sb` empty), at widths meeting
  every hypothesis of `srcP_runs`/`srcOpp_runs` (`ds_src_widths`, `Fast/DistWid.lean`); the
  parameter machine's own outputs (the layout, the streams on `oT`, `oS`, the unary copies `us`)
  are kept, and every other register ends as it started.
* `dsAllCost n = pmCost n [] + dsMainCost n`, `dsAll_cost_le`: eventually
  `dsAllCost n ≤ 2·10^10 n + 2·10^10 (b n + 1)^5`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section Main

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- **The distribution machine**: the widths, then the converter. -/
def dsMain (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Pr P T Q A U :=
  .seq (dsWid rg g) (dsSrc rg g)

/-- The final family file: the source-transform file on `.s`, the widths and the layout-stage
parameters on `.o`. -/
noncomputable def dsFinal (n : ℕ) (hd0 : 0 < d n) : DsY t₀ → List (Fin (A + 4))
  | .s r => (dsSrcE n (dsW n) (dsWW n) hd0).get r
  | .o .uW => List.replicate (dsWW n) tick
  | .o .uw => List.replicate (dsW n) tick
  | .o x => dsSrcO n (dsW n) x

theorem dsF_rg (h : DsLay rg g) (R : Regs T A) (X : DsY t₀ → List (Fin (A + 4))) (W : ℕ) (wl)
    (σ : Fin pmNV → ℕ) (r : TblR pmNV) :
    dsF rg g R X W wl σ (rg r) = tblRho W wl wl ⟨σ, []⟩ r := by
  unfold dsF; rw [dsOv_rg h.irg]

theorem dsF_off (R : Regs T A) (X : DsY t₀ → List (Fin (A + 4))) (W : ℕ) (wl)
    (σ : Fin pmNV → ℕ) {k : Fin T} (hk : ∀ r, rg r ≠ k) (hg : ∀ y, g y ≠ k) :
    dsF rg g R X W wl σ k = R k := by
  unfold dsF; rw [dsOv_off _ _ hk, dsOv_off _ _ hg]

variable (h : DsLay rg g)
include h

/-- **The distribution machine** (register-file form). -/
theorem ds_main_runs (R : Regs T A) {n : ℕ} (hbig : Big n) (wl : List (Fin (A + 4)))
    (hwl : wl.length = pmW n) :
    dsRuns body (dsMain rg g) (dsF rg g R (fun _ => []) (pmW n) wl (pmVals n))
      (dsF rg g R (dsFinal n (srcHd0 hbig)) (pmW n) wl (pmVals n)) (dsMainCost n) := by
  obtain ⟨-, c2, -, -, -, -, c7, c8, c9, c10, c11, c12, c13⟩ := ds_src_widths hbig
  have s1 := ds_wid_runs (body := body) h R hbig.1 wl hwl (fun _ => []) rfl rfl
  set X₁ : DsY t₀ → List (Fin (A + 4)) := Function.update (Function.update (fun _ => [])
    (.o .uw) (List.replicate (dsW n) tick)) (.o .uW) (List.replicate (dsWW n) tick) with hX₁
  have hX₁W : X₁ (.o .uW) = List.replicate (dsWW n) tick := by simp [hX₁]
  have hX₁w : X₁ (.o .uw) = List.replicate (dsW n) tick := by
    simp [hX₁, Function.update_of_ne (show (DsY.o DsX.uw : DsY t₀) ≠ .o .uW by simp)]
  have hX₁0 : ∀ y, y ≠ .o .uW → y ≠ .o .uw → X₁ y = [] := fun y h1 h2 => by
    simp [hX₁, Function.update_of_ne h1, Function.update_of_ne h2]
  obtain ⟨X', hv, ho, s2⟩ := ds_src_runs (body := body) h R hbig (srcHd0 hbig) c7 c8 c9 c10 c11
    c12 c2 c13 wl hwl X₁ (by rw [hX₁W, List.length_replicate]) (by rw [hX₁w, List.length_replicate])
    hX₁0
  have hX' : X' = dsFinal n (srcHd0 hbig) := by
    funext y
    cases y with
    | s r => exact ds_srcE_get hv ho hX₁0 r
    | o x =>
      obtain ⟨hW, hw⟩ := ds_srcE_in hv ho hX₁0
      cases x
      all_goals first
        | (rw [hW, hX₁W]; rfl)
        | (rw [hw, hX₁w]; rfl)
        | (rw [ds_srcO_get hv ho hX₁0 _ (by simp) (by simp)]; rfl)
  rw [hX'] at s2
  refine (s1.seq s2).mono ?_
  unfold dsMainCost dsWidCost dsWidCost₀ dsStepCost
  omega

end Main

/-! ### After the parameter machine -/

section All

variable {T Q t₀ K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- **The parameter machine and the distribution machine.** -/
noncomputable def dsAll (rg : TblR pmNV → Fin T) (uN oT oS : Fin T) (us : List (Fin pmNV × Fin T))
    (g : DsY t₀ → Fin T) : Pr P T Q (prime + K) U :=
  .seq (pmParams rg uN oT oS us) (dsMain rg g)

/-- The register maps of the source transform and of the converter form a layout. -/
theorem ds_lay (M : SrcMach t₀ T Q) {rg : TblR pmNV → Fin T} (hrg : Function.Injective rg)
    {io : DsX → Fin T} (hio : Function.Injective io) (hMio : ∀ r x, M.rg r ≠ io x)
    (hdisj : ∀ r y, rg r ≠ dsGY M.rg io y) : DsLay rg (dsGY M.rg io) where
  irg := hrg
  ig := by
    intro y₁ y₂ e
    cases y₁ with
    | s r₁ =>
      cases y₂ with
      | s r₂ => exact congrArg DsY.s (M.hrg e)
      | o x₂ => exact absurd e (hMio r₁ x₂)
    | o x₁ =>
      cases y₂ with
      | s r₂ => exact absurd e.symm (hMio r₂ x₁)
      | o x₂ => exact congrArg DsY.o (hio e)
  disj := hdisj

/-- **The register file between runs**, as the distribution machine leaves it. -/
theorem dsAll_base (M : SrcMach t₀ T Q) {n : ℕ} (hbig : Big n) :
    SrcBase M (dsSrcE (A := prime + K) (t₀ := t₀) n (dsW n) (dsWW n) (srcHd0 hbig)) n (dsW n) (dsWW n)
      (srcHd0 hbig) (dsV₀ (t₀ := t₀) n (dsW n) (dsWW n) (srcHd0 hbig)) (dsσ₀ (t₀ := t₀) n (dsW n) (dsWW n) (srcHd0 hbig))
      (dsRestA n (dsWW n) (srcHd0 hbig)) (dsRestB n (dsWW n) (srcHd0 hbig)) (dsAxs n) (dsAxs n) ∧
    SrcCrtBase (dsSrcE (A := prime + K) (t₀ := t₀) n (dsW n) (dsWW n) (srcHd0 hbig)).c
      (dsSrcE (A := prime + K) (t₀ := t₀) n (dsW n) (dsWW n) (srcHd0 hbig)).cb n (dsW n) ∧
    (dsSrcE (A := prime + K) (t₀ := t₀) n (dsW n) (dsWW n) (srcHd0 hbig)).a .ln = [] ∧
    (dsSrcE (A := prime + K) (t₀ := t₀) n (dsW n) (dsWW n) (srcHd0 hbig)).c .str = [] ∧
    (dsSrcE (A := prime + K) (t₀ := t₀) n (dsW n) (dsWW n) (srcHd0 hbig)).x .sb = [] :=
  ⟨ds_srcE_base M hbig.1 (srcHd0 hbig), ds_srcE_crt, ds_srcE_ln, ds_srcE_str, ds_srcE_sb⟩

/-- **The distribution machine after the parameter machine.** From `n` symbols on `uN`, the
parameter layout and the registers of the source transform and of the converter empty, `dsAll`
leaves the register file `dsSrcE n (dsW n) (dsWW n) _` of the source transform on `M.rg`
(`dsAll_base`: a register file between runs), `dsFinal` on `io`, the parameter machine's outputs
on the layout, `oT`, `oS`, `us`, and every other register as it started, within
`pmCost n us + dsMainCost n` steps. -/
theorem dsAll_exec (M : SrcMach t₀ T Q) (hA : 4 ≤ prime + K) {rg : TblR pmNV → Fin T}
    (hrg : Function.Injective rg) {io : DsX → Fin T} (hio : Function.Injective io)
    (hMio : ∀ r x, M.rg r ≠ io x) (hdisj : ∀ r y, rg r ≠ dsGY M.rg io y) {uN oT oS : Fin T}
    (huN : ∀ r, rg r ≠ uN) (hoT : ∀ r, rg r ≠ oT) (hoS : ∀ r, rg r ≠ oS) (hTS : oT ≠ oS)
    (us : List (Fin pmNV × Fin T)) (hus : ∀ x ∈ us, ∀ r, rg r ≠ x.2)
    (husT : ∀ x ∈ us, x.2 ≠ oT) (husS : ∀ x ∈ us, x.2 ≠ oS) (hnd : (us.map Prod.snd).Nodup)
    (hgT : ∀ y, dsGY M.rg io y ≠ oT) (hgS : ∀ y, dsGY M.rg io y ≠ oS)
    (hgus : ∀ x ∈ us, ∀ y, x.2 ≠ dsGY M.rg io y)
    {n : ℕ} (hbig : Big n) (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hlen : (S.R uN).length = n) (hS : ∀ r, S.R (rg r) = [])
    (hg : ∀ y, S.R (dsGY M.rg io y) = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ pmCost n us + dsMainCost n ∧
      Exec body (dsAll rg uN oT oS us (dsGY M.rg io)) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r, S'.R (M.rg r) = (dsSrcE n (dsW n) (dsWW n) (srcHd0 hbig)).get r) ∧
      (∀ x, S'.R (io x) = dsFinal (t₀ := t₀) n (srcHd0 hbig) (.o x)) ∧
      (∀ i, S'.R (rg (.v i)) = binSyms (pmW n) (pmVals n i)) ∧
      S'.R (rg .wr) = pmTicks (prime + K) (pmW n) ∧ S'.R (rg .wn) = pmTicks (prime + K) (pmW n) ∧
      S'.R (rg .acc) = [] ∧ (∀ j, S'.R (rg (.z j)) = []) ∧
      S'.R oT = pmTStream (prime + K) (pmW n) n ++ S.R oT ∧
      S'.R oS = pmSStream (prime + K) (pmW n) n ++ S.R oS ∧
      (∀ x ∈ us, S'.R x.2 = List.replicate (pmVals n x.1) tick ++ S.R x.2) ∧
      (∀ k, (∀ r, rg r ≠ k) → k ≠ oT → k ≠ oS → (∀ x ∈ us, x.2 ≠ k) →
        (∀ y, dsGY M.rg io y ≠ k) → S'.R k = S.R k) := by
  have hlay := ds_lay M hrg hio hMio hdisj
  set g := dsGY M.rg io with hgdef
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hi₁, ho₁, hL₁, hv₁, hwr₁, hwn₁, hacc₁, hz₁, hT₁, hS₁, hus₁,
    hk₁⟩ := pmParams_exec (body := body) hA hrg huN hoT hoS hTS us hus husT husS hnd hbig.1 v S
    hlen hS
  have hg₁ : ∀ y, S₁.R (g y) = [] := fun y => by
    rw [hk₁ _ (fun r => hdisj r y) (hgT y) (hgS y) (fun x hx => hgus x hx y)]
    exact hg y
  have hwl : (pmTicks (prime + K) (pmW n)).length = pmW n := by simp [pmTicks]
  have hR₁ : S₁.R = dsF rg g S₁.R (fun _ => []) (pmW n) (pmTicks (prime + K) (pmW n))
      (pmVals n) := by
    funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [dsF_rg hlay]
      cases r with
      | v i => simp [hv₁]
      | wr => simp [hwr₁]
      | wn => simp [hwn₁]
      | acc => simp [hacc₁]
      | z j => simp [hz₁]
    · by_cases hk' : ∃ y, g y = k
      · obtain ⟨y, rfl⟩ := hk'
        rw [dsF_g hlay, hg₁]
      · push Not at hk hk'
        rw [dsF_off _ _ _ _ _ hk hk']
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ds_main_runs (body := body) hlay S₁.R hbig
    (pmTicks (prime + K) (pmW n)) hwl v₁ S₁ hR₁
  refine ⟨v₂, _, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hi₁, ho₁, hL₁,
    fun r => ?_, fun x => ?_, fun i => ?_, ?_, ?_, ?_, fun j => ?_, ?_, ?_, fun x hx => ?_,
    fun k hk hkT hkS hkus hkg => ?_⟩
  · exact dsF_g hlay _ _ _ _ _ (.s r)
  · exact dsF_g hlay _ _ _ _ _ (.o x)
  · dsimp only; rw [dsF_rg hlay]; simp
  · dsimp only; rw [dsF_rg hlay]; simp
  · dsimp only; rw [dsF_rg hlay]; simp
  · dsimp only; rw [dsF_rg hlay]; simp
  · dsimp only; rw [dsF_rg hlay]; simp
  · dsimp only; rw [dsF_off _ _ _ _ _ hoT hgT]; exact hT₁
  · dsimp only; rw [dsF_off _ _ _ _ _ hoS hgS]; exact hS₁
  · dsimp only; rw [dsF_off _ _ _ _ _ (fun r => (hus x hx r)) (fun y => (hgus x hx y).symm)]
    exact hus₁ x hx
  · dsimp only; rw [dsF_off _ _ _ _ _ hk hkg]; exact hk₁ k hk hkT hkS hkus

/-- The step bound of `dsAll` without unary copies. -/
noncomputable def dsAllCost (n : ℕ) : ℕ := pmCost n ([] : List (Fin pmNV × Unit)) + dsMainCost n

theorem pmCost_nil {α : Type} (n : ℕ) :
    pmCost n ([] : List (Fin pmNV × α)) = pmCost n ([] : List (Fin pmNV × Unit)) := rfl

/-- **The cost of `dsAll`**: eventually `dsAllCost n ≤ 2·10^10 n + 2·10^10 (b n + 1)^5`. -/
theorem dsAll_cost_le :
    ∀ᶠ n in Filter.atTop, dsAllCost n ≤ 2 * 10 ^ 10 * n + 2 * 10 ^ 10 * (b n + 1) ^ 5 := by
  filter_upwards [ds_mainCost_le, Filter.eventually_ge_atTop 2] with n hm hn
  have h1 := pmCost_le hn ([] : List (Fin pmNV × Unit))
  have h2 : Nat.size n ≤ b n + 1 := pm_size_le
  have h3 : (Nat.size n + 5) ^ 4 ≤ (6 * (b n + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h4 : (6 * (b n + 1)) ^ 4 = 1296 * (b n + 1) ^ 4 := by ring
  have h5 : (b n + 1) ^ 4 ≤ (b n + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h7 : 1 ≤ (b n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  simp only [pmUnaryCost, List.map_nil, List.sum_nil, zero_add] at h1
  unfold dsAllCost
  omega

end All

end IntegerMultBounds.MathlibTM2.Fast.TableVM
