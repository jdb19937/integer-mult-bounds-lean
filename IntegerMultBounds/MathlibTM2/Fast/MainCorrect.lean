module

public import IntegerMultBounds.MathlibTM2.Fast.MainChain
public import IntegerMultBounds.MathlibTM2.Fast.MainPush

/-!
# Correctness of the fast multiplier

`mnFast_hostMul`: given the synthetic transforms (`MnSyn`) and the parameter distribution
(`MnDist`), for every input length `n` beyond an eventual threshold and every pair `x`, `y` with
`|pairEnc (x, y)| = n`, the procedure table `mnTable D Y` started at `.main` in the local state
`mnV₀` turns the input store of `(x, y)` into the output store of `x * y` within
`mnTime D Y (mnC D Y) n` steps (`HostMulWithin`).

The threshold is the intersection of `Sizes.eventually_big`, `Sizes.eventually_small`,
`Sizes.eventually_margins`, `Pipeline.pipeline_correct`, `n ≥ 2` and the eventual clauses of
`D` (contract, base files, CRT base, empty box, CRT and result registers, widths) and of `Y`
(contracts); `mnN₀ D Y` is a threshold beyond which the conclusion holds (`mn_hostMul_ge`).

**Stages.** Each stage is one lemma on the register file, stated through the facts the next
stage reads:

* `mn_front_exec`: F1 and the unary length, from the input store to a store `MnFront` (the
  operand bits on `rx`, `ry`, `n` symbols on `uN`, everything else empty), `8 n + 14` steps;
* `mn_params_exec`: F2, to `MnPostParam` (read by the distribution) and `MnMid` (the registers
  the distribution keeps: the operand bits, the unary copies of `mnUs`, every other kept register
  empty), at most `pmCost n mnUs` steps;
* the distribution (`MnDistSpec`), keeping `MnMid` (`mn_mid_keep`);
* `mn_chain_exec`: F3 to F10 (`mn_chain_runs`), leaving the words of the rounded coefficients on
  `out .dat`;
* F11 (`carryOut_exec`), pushing `encodingNatBool.encode (evalBase (2^b) c)` with
  `evalBase (2^b) c = x y` by `mn_pipelineCoeffs_eq` and `pipeline_correct`;
* `mn_finish`: the cleanup and the reset after any execution of a program pushing at most `c`
  symbols per action (`mn_exec_size`): the registers hold at most `n + c m` symbols after `m`
  steps, so the cleanup takes at most `2 (n + c m) + 2 mnT + 1` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Schoenhage.Schedule (topN)
open Computability

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

attribute [local irreducible] mnT mnQ

noncomputable section

/-! ### Stores -/

section Stores

variable {A : ℕ}

/-- The stacks with `l` on the input stack and every other stack empty. -/
def mnIn (l : List (Bool ⊕ Bool)) : Stacks mnT A := ⟨l, [], fun _ => [], fun _ => []⟩

lemma mn_only_inp (v : HS mnT mnQ A Unit) (l : List (Bool ⊕ Bool)) :
    (Store.only v .inp l : Store (HΓ (T := mnT) A) (HS mnT mnQ A Unit)) = mk v (mnIn l) := by
  refine Store.ext rfl (funext fun k => ?_)
  cases k <;> rfl

lemma mn_only_out (v : HS mnT mnQ A Unit) (l : List Bool) :
    (Store.only v .out l : Store (HΓ (T := mnT) A) (HS mnT mnQ A Unit)) =
      mk v ⟨[], l, fun _ => [], fun _ => []⟩ := by
  refine Store.ext rfl (funext fun k => ?_)
  cases k <;> rfl

lemma mn_size_in (v : HS mnT mnQ A Unit) (l : List (Bool ⊕ Bool)) :
    mnSize (mk v (mnIn (A := A) l)) = l.length := by
  unfold mnSize
  rw [Finset.sum_eq_single HK.inp]
  · rfl
  · intro k _ hk
    cases k with
    | inp => exact absurd rfl hk
    | _ => rfl
  · simp

end Stores

/-! ### Registers -/

lemma mn_rg_ne {r r' : MnR} (h : r ≠ r') : mnRg r ≠ mnRg r' := fun e => h (mnRg_inj e)

/-- Two stage registers, the names decided by `simp`. -/
lemma mn_rg_ne' (r r' : MnR) (h : r ≠ r' := by simp) : mnRg r ≠ mnRg r' := mn_rg_ne h

/-- Two glue registers, the names decided by `decide`. -/
lemma mn_io_ne' (a b : MnIO) (h : a ≠ b := by decide) : mnIo a ≠ mnIo b :=
  mn_rg_ne fun e => h (MnR.io.inj e)

lemma mn_nodup_map {l : List MnR} (h : l.Nodup) : (l.map mnRg).Nodup := h.map mnRg_inj

/-- The registers holding the operand bits and the unary copies of `mnUs`. -/
def mnUsRegs : List MnR :=
  [.io .rx, .io .ry, .io .dbn, .io .dpn, .io .dsn, .rnd .bn, .rnd .pn, .out .br]

/-- A register off the copies of `mnUs`. -/
lemma mn_us_off {k : Fin mnT} (h : ∀ r, mnRg r ≠ k) :
    ∀ z ∈ (mnUs : List (Fin pmNV × Fin mnT)), z.2 ≠ k := by
  intro z hz
  simp only [mnUs, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> exact h _

lemma mn_pmVals_b (n : ℕ) : pmVals n pmIb = b n := rfl
lemma mn_pmVals_p (n : ℕ) : pmVals n pmIp = p n := rfl
lemma mn_pmVals_S (n : ℕ) : pmVals n pmIS = S n := rfl

/-! ### F1 and the unary length -/

section Front

variable {A : ℕ} {body : MnProc → MnPr A}

/-- The store after F1 and the length: the operand bits on `rx`, `ry`, `N` symbols on `uN`,
every other stack empty. -/
structure MnFront (St : Stacks mnT A) (x y N : ℕ) : Prop where
  inp : St.inp = []
  out : St.out = []
  L : ∀ k, St.L k = []
  rx : St.R (mnIo .rx) = (encodingNatBool.encode x).map bitSymbol
  ry : St.R (mnIo .ry) = (encodingNatBool.encode y).map bitSymbol
  uN : (St.R (mnIo .uN)).length = N
  rest : ∀ k, k ≠ mnIo .rx → k ≠ mnIo .ry → k ≠ mnIo .uN → St.R k = []

/-- **F1 and the unary length.** -/
theorem mn_front_exec (x y : ℕ) :
    ∃ (v : HS mnT mnQ A Unit) (St : Stacks mnT A) (m : ℕ),
      m ≤ 8 * (pairEnc (x, y)).length + 14 ∧
      Exec body (.seq mnRead mnLen) (mk mnV₀ (mnIn (pairEnc (x, y)))) m (mk v St) ∧
      MnFront St x y (pairEnc (x, y)).length := by
  obtain ⟨v₁, -, e₁⟩ := readInput_exec (body := body) (mnIo .tx) (mnIo .ty) (mnIo .rx)
    (mnIo .ry) (mn_nodup_map (l := [.io .tx, .io .ty, .io .rx, .io .ry]) (by simp)) x y mnV₀
    (mnIn _) rfl rfl rfl
  set bx : List (Fin (A + 4)) := (encodingNatBool.encode x).map bitSymbol with hbx
  set cy : List (Fin (A + 4)) := (encodingNatBool.encode y).map bitSymbol with hcy
  set R₁ : Fin mnT → List (Fin (A + 4)) :=
    Function.update (Function.update (fun _ => []) (mnIo .rx) bx) (mnIo .ry) cy with hR₁
  replace e₁ : Exec body mnRead (mk mnV₀ (mnIn (pairEnc (x, y))))
      (4 * (pairEnc (x, y)).length + 6) (mk v₁ ⟨[], [], fun _ => [], R₁⟩) := by
    refine Exec.cast e₁ rfl ?_
    congr 1
    refine Stacks.ext rfl rfl rfl ?_
    simp only [mnIn, hR₁, List.append_nil]
  have hct₁ : R₁ (mnIo .ct) = [] := by
    rw [hR₁, Function.update_of_ne (mn_io_ne' .ct .ry), Function.update_of_ne (mn_io_ne' .ct .rx)]
  have hrx₁ : R₁ (mnIo .rx) = bx := by
    rw [hR₁, Function.update_of_ne (mn_io_ne' .rx .ry), Function.update_self]
  have huN₁ : R₁ (mnIo .uN) = [] := by
    rw [hR₁, Function.update_of_ne (mn_io_ne' .uN .ry), Function.update_of_ne (mn_io_ne' .uN .rx)]
  -- the first copy
  obtain ⟨v₂, -, e₂⟩ := copyR_exec (body := body) (mnIo .rx) (mnIo .uN) (mnIo .ct)
    (mn_io_ne' .rx .uN) (mn_io_ne' .rx .ct) (mn_io_ne' .uN .ct) id v₁ ⟨[], [], fun _ => [], R₁⟩ hct₁
  set R₂ : Fin mnT → List (Fin (A + 4)) := Function.update R₁ (mnIo .uN) bx.reverse with hR₂
  replace e₂ : Exec body (copyR (mnIo .rx) (mnIo .uN) (mnIo .ct) id)
      (mk v₁ ⟨[], [], fun _ => [], R₁⟩) (4 * bx.length + 4) (mk v₂ ⟨[], [], fun _ => [], R₂⟩) := by
    refine Exec.cast e₂ ?_ ?_
    · show 4 * (R₁ (mnIo .rx)).length + 4 = 4 * bx.length + 4
      rw [hrx₁]
    · congr 1
      refine Stacks.ext rfl rfl rfl ?_
      show Function.update R₁ (mnIo .uN) (((R₁ (mnIo .rx)).map id).reverse ++ R₁ (mnIo .uN)) = R₂
      rw [hrx₁, huN₁, List.map_id, List.append_nil]
  have hct₂ : R₂ (mnIo .ct) = [] := by
    rw [hR₂, Function.update_of_ne (mn_io_ne' .ct .uN)]; exact hct₁
  have hry₂ : R₂ (mnIo .ry) = cy := by
    rw [hR₂, Function.update_of_ne (mn_io_ne' .ry .uN), hR₁, Function.update_self]
  have huN₂ : R₂ (mnIo .uN) = bx.reverse := by rw [hR₂, Function.update_self]
  -- the second copy
  obtain ⟨v₃, -, e₃⟩ := copyR_exec (body := body) (mnIo .ry) (mnIo .uN) (mnIo .ct)
    (mn_io_ne' .ry .uN) (mn_io_ne' .ry .ct) (mn_io_ne' .uN .ct) id v₂ ⟨[], [], fun _ => [], R₂⟩ hct₂
  set R₃ : Fin mnT → List (Fin (A + 4)) :=
    Function.update R₂ (mnIo .uN) (cy.reverse ++ bx.reverse) with hR₃
  replace e₃ : Exec body (copyR (mnIo .ry) (mnIo .uN) (mnIo .ct) id)
      (mk v₂ ⟨[], [], fun _ => [], R₂⟩) (4 * cy.length + 4) (mk v₃ ⟨[], [], fun _ => [], R₃⟩) := by
    refine Exec.cast e₃ ?_ ?_
    · show 4 * (R₂ (mnIo .ry)).length + 4 = 4 * cy.length + 4
      rw [hry₂]
    · congr 1
      refine Stacks.ext rfl rfl rfl ?_
      show Function.update R₂ (mnIo .uN) (((R₂ (mnIo .ry)).map id).reverse ++ R₂ (mnIo .uN)) = R₃
      rw [hry₂, huN₂, List.map_id]
  have hN := length_pairEnc_encode x y
  refine ⟨v₃, _, _, ?_, Exec.seq e₁ (Exec.seq e₂ e₃), ?_⟩
  · simp only [hbx, hcy, List.length_map]; omega
  · refine ⟨rfl, rfl, fun _ => rfl, ?_, ?_, ?_, ?_⟩
    · show R₃ (mnIo .rx) = bx
      rw [hR₃, Function.update_of_ne (mn_io_ne' .rx .uN), hR₂,
        Function.update_of_ne (mn_io_ne' .rx .uN), hrx₁]
    · show R₃ (mnIo .ry) = cy
      rw [hR₃, Function.update_of_ne (mn_io_ne' .ry .uN), hry₂]
    · show (R₃ (mnIo .uN)).length = (pairEnc (x, y)).length
      rw [hR₃, Function.update_self, List.length_append, List.length_reverse, List.length_reverse,
        hN]
      simp only [hbx, hcy, List.length_map]
      omega
    · intro k h1 h2 h3
      show R₃ k = []
      rw [hR₃, Function.update_of_ne h3, hR₂, Function.update_of_ne h3, hR₁,
        Function.update_of_ne h2, Function.update_of_ne h1]

end Front

/-! ### F2 -/

section Params

variable {A : ℕ} {body : MnProc → MnPr A}

/-- The registers the distribution keeps, after F2: the operand bits, the unary copies of `mnUs`,
every other kept register empty. -/
structure MnMid (St : Stacks mnT A) (x y N : ℕ) : Prop where
  rx : St.R (mnIo .rx) = (encodingNatBool.encode x).map bitSymbol
  ry : St.R (mnIo .ry) = (encodingNatBool.encode y).map bitSymbol
  dbn : St.R (mnIo .dbn) = List.replicate (pmVals N pmIb) tick
  dpn : St.R (mnIo .dpn) = List.replicate (pmVals N pmIp) tick
  dsn : St.R (mnIo .dsn) = List.replicate (pmVals N pmIS) tick
  rbn : St.R (mnRnd .bn) = List.replicate (pmVals N pmIb) tick
  rpn : St.R (mnRnd .pn) = List.replicate (pmVals N pmIp) tick
  obr : St.R (mnOutR .br) = List.replicate (pmVals N pmIb) tick
  rest : ∀ r : MnR, mnDistKeep r → r ∉ mnUsRegs → St.R (mnRg r) = []

/-- A register the parameter machine leaves unchanged. -/
def MnPmOff (r : MnR) : Prop :=
  (∀ q, r ≠ .pm q) ∧ r ≠ .io .oT ∧ r ≠ .io .oS ∧ r ≠ .io .dbn ∧ r ≠ .io .dpn ∧ r ≠ .io .dsn ∧
    r ≠ .rnd .bn ∧ r ≠ .rnd .pn ∧ r ≠ .out .br

lemma mn_pmOff_of_keep {r : MnR} (hk : mnDistKeep r) (hr : r ∉ mnUsRegs) : MnPmOff r := by
  simp only [mnUsRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8⟩ := hr
  cases r with
  | src _ => exact hk.elim
  | pm _ => exact hk.elim
  | io r' =>
      simp only [mnDistKeep] at hk
      exact ⟨fun q => by simp, fun e => hk.2.2.2.2.1 (MnR.io.inj e),
        fun e => hk.2.2.2.2.2.1 (MnR.io.inj e), h3, h4, h5, by simp, by simp, by simp⟩
  | rnd _ => exact ⟨fun q => by simp, by simp, by simp, by simp, by simp, by simp, h6, h7, by simp⟩
  | out _ => exact ⟨fun q => by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, h8⟩

/-- **F2.** -/
theorem mn_params_exec {x y N : ℕ} (hN : 2 ≤ N) (hA : 4 ≤ A) (v : HS mnT mnQ A Unit)
    (St : Stacks mnT A) (hS : MnFront St x y N) :
    ∃ (v' : HS mnT mnQ A Unit) (St' : Stacks mnT A) (m : ℕ), m ≤ pmCost N mnUs ∧
      Exec body mnParams (mk v St) m (mk v' St') ∧ St'.inp = [] ∧ St'.out = [] ∧
      (∀ k, St'.L k = []) ∧ (∀ j, St'.R (mnι j) = []) ∧ MnPostParam St'.R N ∧ MnMid St' x y N := by
  have hus : ∀ z ∈ (mnUs : List (Fin pmNV × Fin mnT)), ∀ r, mnPm r ≠ z.2 := by simp [mnUs]
  have husT : ∀ z ∈ (mnUs : List (Fin pmNV × Fin mnT)), z.2 ≠ mnIo .oT := by simp [mnUs]
  have husS : ∀ z ∈ (mnUs : List (Fin pmNV × Fin mnT)), z.2 ≠ mnIo .oS := by simp [mnUs]
  have hnd : ((mnUs : List (Fin pmNV × Fin mnT)).map Prod.snd).Nodup := by
    have := mn_nodup_map (l := [.io .dbn, .io .dpn, .io .dsn, .rnd .bn, .rnd .pn, .out .br])
      (by simp)
    simpa [mnUs] using this
  obtain ⟨v', St', m, -, hm, e, hinp, hout, hL, hvar, hwr, hwn, hacc, hz, hoT, hoS, hus', hfr⟩ :=
    pmParams_exec (body := body) (rg := mnPm) hA (fun _ _ h => MnR.pm.inj (mnRg_inj h))
      (fun r => mn_rg_ne' _ _) (fun r => mn_rg_ne' _ _) (fun r => mn_rg_ne' _ _) (mn_rg_ne' _ _)
      mnUs hus husT husS hnd hN v St hS.uN
      (fun r => hS.rest _ (mn_rg_ne' _ _) (mn_rg_ne' _ _) (mn_rg_ne' _ _))
  -- the frame
  have fr : ∀ r : MnR, MnPmOff r → St'.R (mnRg r) = St.R (mnRg r) := by
    intro r ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine hfr _ (fun q h => h1 q (mnRg_inj h).symm) (mn_rg_ne h2) (mn_rg_ne h3) ?_
    intro z hz
    simp only [mnUs, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [(mn_rg_ne h4).symm, (mn_rg_ne h5).symm, (mn_rg_ne h6).symm, (mn_rg_ne h7).symm,
      (mn_rg_ne h8).symm, (mn_rg_ne h9).symm]
  have hι' : ∀ j, St'.R (mnι j) = [] := by
    intro j
    rw [hfr _ (fun r => mnRg_ne_ι _ j) (mnRg_ne_ι _ j).symm (mnRg_ne_ι _ j).symm
      (mn_us_off fun r => mnRg_ne_ι r j)]
    exact hS.rest _ (mnRg_ne_ι _ j).symm (mnRg_ne_ι _ j).symm (mnRg_ne_ι _ j).symm
  have hcopy : ∀ (i : Fin pmNV) (r : MnR), (i, mnRg r) ∈ (mnUs : List (Fin pmNV × Fin mnT)) →
      r ≠ .io .rx → r ≠ .io .ry → r ≠ .io .uN →
      St'.R (mnRg r) = List.replicate (pmVals N i) tick := by
    intro i r hm h1 h2 h3
    have h := hus' (i, mnRg r) hm
    simp only at h
    rw [h, hS.rest _ (mn_rg_ne h1) (mn_rg_ne h2) (mn_rg_ne h3), List.append_nil]
  refine ⟨v', St', m, hm, e, by rw [hinp]; exact hS.inp, by rw [hout]; exact hS.out,
    fun k => by rw [hL]; exact hS.L k, hι', ?_, ?_⟩
  · refine ⟨hvar, hwr, hwn, hacc, hz, ?_, ?_, ?_, fun r => ?_, fun z => ?_, fun r hr => ?_⟩
    · rw [hoT, hS.rest _ (mn_rg_ne' _ _) (mn_rg_ne' _ _) (mn_rg_ne' _ _), List.append_nil]
    · rw [hoS, hS.rest _ (mn_rg_ne' _ _) (mn_rg_ne' _ _) (mn_rg_ne' _ _), List.append_nil]
    · rw [fr (.io .uN) (by simp [MnPmOff])]; exact hS.uN
    · rw [fr (.src r) (by simp [MnPmOff])]
      exact hS.rest _ (mn_rg_ne' _ _) (mn_rg_ne' _ _) (mn_rg_ne' _ _)
    · rw [hfr _ (fun r => mnRg_ne_lay _ z) (mnRg_ne_lay _ z).symm (mnRg_ne_lay _ z).symm
        (mn_us_off fun r => mnRg_ne_lay r z)]
      exact hS.rest _ (mnRg_ne_lay _ z).symm (mnRg_ne_lay _ z).symm (mnRg_ne_lay _ z).symm
    · simp only [mnRndRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [fr _ (by simp [MnPmOff])]; exact hS.rest _ (mn_rg_ne' _ _) (mn_rg_ne' _ _) (mn_rg_ne' _ _))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fr (.io .rx) (by simp [MnPmOff])]; exact hS.rx
    · rw [fr (.io .ry) (by simp [MnPmOff])]; exact hS.ry
    · exact hcopy pmIb (.io .dbn) (by simp [mnUs]) (by simp) (by simp) (by simp)
    · exact hcopy pmIp (.io .dpn) (by simp [mnUs]) (by simp) (by simp) (by simp)
    · exact hcopy pmIS (.io .dsn) (by simp [mnUs]) (by simp) (by simp) (by simp)
    · exact hcopy pmIb (.rnd .bn) (by simp [mnUs]) (by simp) (by simp) (by simp)
    · exact hcopy pmIp (.rnd .pn) (by simp [mnUs]) (by simp) (by simp) (by simp)
    · exact hcopy pmIb (.out .br) (by simp [mnUs]) (by simp) (by simp) (by simp)
    · intro r hk hr
      rw [fr r (mn_pmOff_of_keep hk hr)]
      simp only [mnUsRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      have hU : r ≠ .io .uN := fun e => by subst e; simp [mnDistKeep] at hk
      exact hS.rest _ (mn_rg_ne hr.1) (mn_rg_ne hr.2.1) (mn_rg_ne hU)

/-- `MnMid` survives the distribution, which keeps every register of `mnDistKeep`. -/
lemma mn_mid_keep {x y N : ℕ} {St St' : Stacks mnT A} (h : MnMid St x y N)
    (hk : ∀ r, mnDistKeep r → St'.R (mnRg r) = St.R (mnRg r)) : MnMid St' x y N where
  rx := by rw [hk _ (by simp [mnDistKeep])]; exact h.rx
  ry := by rw [hk _ (by simp [mnDistKeep])]; exact h.ry
  dbn := by rw [hk _ (by simp [mnDistKeep])]; exact h.dbn
  dpn := by rw [hk _ (by simp [mnDistKeep])]; exact h.dpn
  dsn := by rw [hk _ (by simp [mnDistKeep])]; exact h.dsn
  rbn := by rw [hk _ (by simp [mnDistKeep])]; exact h.rbn
  rpn := by rw [hk _ (by simp [mnDistKeep])]; exact h.rpn
  obr := by rw [hk _ (by simp [mnDistKeep])]; exact h.obr
  rest := fun r hr hu => by rw [hk r hr]; exact h.rest r hr hu

end Params

/-! ### F3 to F10 -/

section Chain

variable {K : ℕ} {body : MnProc → MnPr (prime + K)}

/-- The step bounds of the three source-transform runs at `n`, coefficient width `w`, table word
size `W`, transform bounds `cF`, `cO`, base files `V₀`, `σ₀`, remaining records `restA`,
`restB`. -/
def mnRunsAt (n w W cF cO : ℕ) (hd0 : 0 < d n) (V₀ : RsaV (RsaX 6) (prime + K))
    (σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4))) (restA restB : List (Fin (prime + K + 4))) :
    ℕ :=
  srcPCost mnM n w W cF cO hd0 V₀ σ₀
      (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
      (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) +
    srcPCost mnM n w W cF cO hd0
      (preCfgA V₀ crtHd n w W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1))
      (preCfgB σ₀ crtHd n w W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1))
      (preRecsA n W hd0 0 ++ restA) (preRecsB n W hd0 0 ++ restB) +
    oppPCost mnM n w W cF cO hd0
      (preCfgA (preCfgA V₀ crtHd n w W hd0
        (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1))
        crtHd n w W hd0 (preRecsA n W hd0 0 ++ restA) (d n - 1))
      (preCfgB (preCfgB σ₀ crtHd n w W hd0
        (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1))
        crtHd n w W hd0 (preRecsB n W hd0 0 ++ restB) (d n - 1))
      restA restB

lemma mn_runs_eq {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg CReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (Y : MnSyn K Lb w σ) {n : ℕ} (hd0 : 0 < d n) :
    mnRuns D Y n = mnRunsAt n (w n) (D.Wt n) (Y.cF n) (Y.cO n) hd0 (D.V₀ n) (D.σ₀ n) (D.restA n)
      (D.restB n) := by
  unfold mnRuns
  rw [dif_pos hd0]
  rfl

/-- **F3 to F10** on the store the distribution leaves. -/
theorem mn_chain_exec (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : MnPr (prime + K)} {w W cF cO : ℕ} {π : ℕ → ℕ}
    {σ : LReg CReg → List (Fin (prime + K + 4))}
    (hF : SynFwdSpec body fwdP (mnSrc (.v .io)) (mnSynPre σ) w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (mnSrc (.v .io)) (mnSynPre σ) w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n)))
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (hWB : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (13 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX 6) (prime + K)} {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF 6 (prime + K))
    (hE : SrcBase mnM E n w W (srcHd0 hbig) V₀ σ₀
      (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA))
      (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = []) (hstr : E.c .str = [])
    (hsb : E.x .sb = []) (x y : ℕ) (hsx : Nat.size x ≤ n) (hsy : Nat.size y ≤ n)
    (v : HS mnT mnQ (prime + K) Unit) (St : Stacks mnT (prime + K))
    (hL : ∀ k, St.L k = []) (hι : ∀ j, St.R (mnι j) = []) (hlay : ∀ z, St.R (mnLay z) = σ z)
    (hsrc : ∀ r, St.R (mnSrc r) = E.get r) (hM : MnMid St x y n)
    (hdwn : (St.R (mnIo .dwn)).length = w) (hrwn : (St.R (mnRnd .wn)).length = w)
    (hrmn : (St.R (mnRnd .mn)).length = mnMw n w)
    (hrnn : (St.R (mnRnd .nn)).length = topN (mnMw n w))
    (hrsq : St.R (mnRnd .sq) = binSyms (mnMw n w) (S n * S n))
    (hrwo : (St.R (mnRnd .wo)).length = mnWo n) :
    ∃ (v' : HS mnT mnQ (prime + K) Unit) (St' : Stacks mnT (prime + K)) (m : ℕ),
      m ≤ mnChainCost n w (mnRunsAt n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) ∧
      Exec body (mnChain fwdP oppP) (mk v St) m (mk v' St') ∧
      St'.inp = St.inp ∧ St'.out = St.out ∧ St'.L = St.L ∧
      St'.R (mnOutR .dat) = mnWords K n x y ∧
      ∀ r, r ≠ .dat → St'.R (mnOutR r) = St.R (mnOutR r) := by
  have he : ∀ r : MnR, mnDistKeep r → r ∉ mnUsRegs → St.R (mnRg r) = [] := hM.rest
  obtain ⟨F', g', hrun, hdat, hout⟩ := mn_chain_runs (body := body) hA hbig hsmall hEs hF hO hπ
    hw hwW hWA hWB hWs hWk E hE hC hln hstr hsb (fun r => St.R (mnRg r)) x y hsx hsy hM.rx hM.ry
    (by simp only [hM.dbn, List.length_replicate, mn_pmVals_b])
    (by simp only [hM.dpn, List.length_replicate, mn_pmVals_p])
    hdwn
    (by simp only [hM.dsn, List.length_replicate, mn_pmVals_S])
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    hrwn hrmn hrnn hrsq
    (by simp only [hM.rbn, List.length_replicate, mn_pmVals_b])
    (by simp only [hM.rpn, List.length_replicate, mn_pmVals_p])
    hrwo
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs])) (he _ (by simp [mnDistKeep]) (by simp [mnUsRegs]))
  obtain ⟨v', St', m, -, hm, e, hS', hfr⟩ := hrun v St ⟨hL, hι⟩ ⟨hL, hι, hlay⟩
    (fun r => by cases r <;> first | rfl | exact hsrc _)
  refine ⟨v', St', m, hm, e, hfr.1, hfr.2.1, hfr.2.2.1, ?_, fun r hr => ?_⟩
  · rw [show St'.R (mnOutR .dat) = g' (.out .dat) from hS' (.out .dat), hdat]
  · rw [show St'.R (mnOutR r) = g' (.out r) from hS' (.out r), hout r hr]

end Chain

/-! ### The cleanup and the reset -/

section Finish

variable {A : ℕ}

/-- **The cleanup and the reset** after an execution of `P` from the input store: at most
`2 (n + c m) + 2 mnT + 2` further steps, where `c` bounds the pushes per action. -/
theorem mn_finish {c : ℕ} (body : MnProc → MnPr A) (hb : ∀ f, mnProgPush (body f) ≤ c)
    (P : MnPr A) (hP : mnProgPush P ≤ c) (l : List (Bool ⊕ Bool)) (o : List Bool) {m : ℕ}
    {v : HS mnT mnQ A Unit} {St : Stacks mnT A}
    (e : Exec body P (mk mnV₀ (mnIn l)) m (mk v St)) (hinp : St.inp = []) (hout : St.out = o)
    (hL : ∀ k, St.L k = []) :
    ∃ m', m' ≤ m + 2 * (l.length + c * m) + 2 * mnT + 2 ∧
      Exec body (.seq P (.seq mnClear mnReset)) (Store.only mnV₀ .inp l) m'
        (Store.only mnV₀ .out o) := by
  obtain ⟨v', e₇⟩ := mn_clear_exec body v St
  have e₈ := mn_reset_exec body v' { St with R := fun _ => [] }
  have hz := mn_exec_size e hP hb
  rw [mn_size_in] at hz
  have hR := mn_sumR_le_size v St
  have hfin : ({ St with R := fun _ => [] } : Stacks mnT A) = ⟨[], o, fun _ => [], fun _ => []⟩ :=
    Stacks.ext hinp hout (funext hL) rfl
  refine ⟨m + (2 * ∑ i, (St.R i).length + 2 * mnT + 1 + 1), ?_, ?_⟩
  · have : ∑ i, (St.R i).length ≤ l.length + c * m := hR.trans hz
    omega
  · rw [mn_only_inp, mn_only_out, ← hfin]
    exact Exec.seq e (Exec.seq e₇ e₈)

end Finish

/-! ### The fast multiplier -/

section Main

variable {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
  {σ : ℕ → LReg CReg → List (Fin (prime + K + 4))}

/-- The pushes of the stages before the cleanup are bounded by the push constant. -/
lemma mn_push_pre (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) :
    mnProgPush (mnPre D.distP Y.fwdP Y.oppP) ≤ mnC D Y := by
  have h := mn_progPush_le_pushC (mnTable D Y) .main
  have e : mnProgPush (mnTable D Y .main) = max (mnProgPush (mnPre D.distP Y.fwdP Y.oppP))
      (mnProgPush (.seq mnClear mnReset : MnPr (prime + K))) := rfl
  rw [e, max_le_iff] at h
  exact h.1

/-- **Correctness of the fast multiplier** for all large input lengths. -/
theorem mnFast_hostMul (hA : 96 ≤ prime + K) (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) :
    ∀ᶠ N in Filter.atTop, ∀ x y : ℕ, (pairEnc (x, y)).length = N →
      HostMulWithin (mnTable D Y) .main mnV₀ (mnTime D Y (mnC D Y)) x y := by
  filter_upwards [eventually_big, eventually_small, eventually_margins, pipeline_correct, D.spec,
    D.base, D.crt, D.ln, D.str, D.sb, D.widths, Y.spec, Filter.eventually_ge_atTop 2]
    with N hbig hsmall hmarg hpipe hdist hbase hcrt hln hstr hsb hwid hsyn hN2
  intro x y hxy
  obtain ⟨hEs, -⟩ := hmarg
  obtain ⟨hw, hwW, hWA, hWB, hWs, hWk⟩ := hwid
  obtain ⟨hF, hO, hπ⟩ := hsyn (mnFast D.distP Y.fwdP Y.oppP)
  have hd0 := srcHd0 hbig
  have hA4 : 4 ≤ prime + K := by omega
  have hb1 : 1 ≤ b N := one_le_b hbig.1
  have hsx : Nat.size x ≤ N := by rw [← hxy, length_pairEnc]; omega
  have hsy : Nat.size y ≤ N := by rw [← hxy, length_pairEnc]; omega
  -- F1 and the length
  obtain ⟨v₂, S₂, m₂, hm₂, e₂, hF₂⟩ := mn_front_exec (body := mnTable D Y) x y
  rw [hxy] at hm₂ hF₂
  -- F2
  obtain ⟨v₃, S₃, m₃, hm₃, e₃, hinp₃, hout₃, hL₃, hι₃, hpost, hmid₃⟩ :=
    mn_params_exec (body := mnTable D Y) hN2 hA4 v₂ S₂ hF₂
  -- the distribution
  obtain ⟨v₄, S₄, m₄, hm₄, e₄, hinp₄, hout₄, hL₄, hι₄, hdo, hkeep⟩ :=
    hdist (mnFast D.distP Y.fwdP Y.oppP) v₃ S₃ hL₃ hι₃ hpost
  have hL₄' : ∀ k, S₄.L k = [] := fun k => by rw [hL₄]; exact hL₃ k
  have hmid₄ := mn_mid_keep hmid₃ hkeep
  -- F3 to F10
  obtain ⟨v₅, S₅, m₅, hm₅, e₅, hinp₅, hout₅, hL₅, hdat₅, hfr₅⟩ :=
    mn_chain_exec (body := mnTable D Y) hA hbig hsmall hEs hF hO hπ hw hwW hWA hWB hWs hWk
      (D.E N) (hbase hd0) hcrt hln hstr hsb x y hsx hsy v₄ S₄ hL₄' hι₄ hdo.lay hdo.src hmid₄
      hdo.dwn hdo.rwn hdo.rmn hdo.rnn hdo.rsq hdo.rwo
  -- F11
  set cs : List ℕ := List.ofFn fun i : Fin (∏ i, s N i) => rndCoeff (b N) (∏ i, s N i) (p N)
    (numer (p N) (oppMap N (mnY N x y) ((i : ℕ) : ZMod (∏ i, s N i)))).re with hcs
  have hY1 : ‖mnY N x y‖ ≤ 1 / 2 := mn_rdV_norm _
    (mn_srcMap_norm hbig hsmall hEs (mn_scaledDigits_norm hb1 _))
    (mn_srcMap_norm hbig hsmall hEs (mn_scaledDigits_norm hb1 _))
  have hWo1 : 1 ≤ mnWo N := by unfold mnWo; omega
  have hcsb : ∀ z ∈ cs, z < 2 ^ mnWo N := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    exact mn_rndCoeff_lt ((norm_le_pi_norm _ _).trans (mn_oppMap_norm hbig hsmall hEs hY1))
  have hcsl : cs.length = S N := by rw [hcs, List.length_ofFn]; rfl
  have hobr : S₅.R (mnOutR .br) = List.replicate (b N) tick := by
    rw [hfr₅ .br (by simp), hmid₄.obr, mn_pmVals_b]
  have hoe : ∀ r : OReg, r ≠ .dat → mnDistKeep (.out r) → MnR.out r ∉ mnUsRegs →
      S₅.R (mnOutR r) = [] := fun r hr hk hu => by
    rw [hfr₅ r hr]; exact hmid₄.rest _ hk hu
  obtain ⟨v₆, -, e₆⟩ := carryOut_exec (body := mnTable D Y) (oreg := mnOutR)
    (fun _ _ h => MnR.out.inj (mnRg_inj h)) hb1 hWo1 hcsb (lw := S₅.R (mnOutR .wr))
    (lb := S₅.R (mnOutR .br)) (by rw [hfr₅ .wr (by simp)]; exact hdo.owr)
    (by rw [hobr, List.length_replicate]) v₅ S₅ (by rw [hdat₅]; rfl) rfl rfl
    (hoe .ct (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .cr (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .sm (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
    (hoe .acc (by simp) (by simp [mnDistKeep]) (by simp [mnUsRegs]))
  have hev : evalBase (2 ^ b N) cs = x * y := by
    rw [hcs, ← mn_pipelineCoeffs_eq hd0 x y]; exact hpipe x y hsx hsy
  -- the stages before the cleanup
  have e := Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))
  generalize hM : m₂ + (m₃ + (m₄ + (m₅ + carryOutCost (mnWo N) (b N) cs.length))) = M at e
  have hpre : M ≤ mnPreCost D Y N := by
    rw [← hM, hcsl]
    unfold mnPreCost mnTail
    rw [mn_runs_eq D Y hd0]
    unfold mnChainCost at hm₅
    omega
  obtain ⟨m', hm', e'⟩ := mn_finish (c := mnC D Y) (mnTable D Y) (mn_progPush_le_pushC _)
    (mnPre D.distP Y.fwdP Y.oppP) (mn_push_pre D Y) (pairEnc (x, y))
    (encodingNatBool.encode (x * y)) e
    (by show S₅.inp = []; rw [hinp₅, hinp₄, hinp₃])
    (by
      show encodingNatBool.encode (evalBase (2 ^ b N) cs) ++ S₅.out = _
      rw [hout₅, hout₄, hout₃, List.append_nil, hev])
    (fun k => by show S₅.L k = []; rw [hL₅]; exact hL₄' k)
  refine ⟨m', ?_, e'⟩
  rw [hxy] at hm' ⊢
  have := Nat.mul_le_mul_left (mnC D Y) hpre
  unfold mnTime
  omega

/-- A threshold beyond which the fast multiplier is correct. -/
def mnN₀ (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) : ℕ :=
  Classical.choose (Filter.eventually_atTop.1 (mnFast_hostMul Y.alpha D Y))

/-- **Correctness beyond the threshold `mnN₀`.** -/
theorem mn_hostMul_ge (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) (x y : ℕ)
    (h : mnN₀ D Y ≤ (pairEnc (x, y)).length) :
    HostMulWithin (mnTable D Y) .main mnV₀ (mnTime D Y (mnC D Y)) x y :=
  Classical.choose_spec (Filter.eventually_atTop.1 (mnFast_hostMul Y.alpha D Y)) _ h x y rfl

end Main

end

end IntegerMultBounds.MathlibTM2.Fast.Main
