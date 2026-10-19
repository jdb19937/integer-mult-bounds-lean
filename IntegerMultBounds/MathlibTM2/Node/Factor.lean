module

public import IntegerMultBounds.MathlibTM2.Node.Body
public import IntegerMultBounds.MathlibTM2.Node.Basis
import Mathlib.Tactic.Positivity.Finset

/-!
# The factor programs of the layer machine

`factorProg hQ cp ds fw g` implements the scaled factor `(fw, g)`, `g = (q, v)`, of the node at
level `j + 1` (`facM`, `execM` of `Layer/NodeZ.lean`) on the bank of wire registers, with the
program `cp` for the call of the child:

* no pivot (`v = 0`): `shiftTc allW` multiplies every wire by `2 ^ |Tc|` (`shiftInto` with the
  shift counters `Tc` and `sc 0`, which holds `w - |Tc|` symbols);
* pivot `s = Fin.find (v · = 1)`: `saveDiv NW .rows` and `saveDiv m .L` put the child's row count
  and slot width on `rows` and `L` (the parent's contents go onto `park`); `basisW v s` on
  `wire fw` (`basisProg` with `BReg = SXReg`, registers `bc x`); `condConj q fw` (conjugation
  unless `q = 1`); `childCall`; `condConj q fw`; `basisW v s`; `restoreMul m .L` and
  `restoreMul NW .rows` bring the parent's contents back from `park`; `shiftTc` on the other wires.

`childCall fw s G F cp`: `parkW` moves every other wire onto `park` (static order `otherW fw`),
`wire fw` moves onto `io` (forward order, through `wtmp fw`), `callCore` runs `callPre` (the top
symbol of `lev` and the contents of `Tc` onto `park`, `s |L|` ticks onto `a₀`), the call `cp` and
`callPost` (`a₀` loses the ticks, `Tc` returns from `park` by a counted move of
`expSeq G F |u| |lev|` symbols, the top symbol returns to `lev`); `io` moves back onto `wire fw`
while `ucopy` builds its length on `lenctr`, and `unparkW` restores the other wires in reverse
order by counted moves (`cmove`, a one-destination `xferBlock`). Every register the factor changes
ends with its exact initial contents.

**Specifications.** `CallSpec body cp bcRest ds R₀ j u K ρ a₀ L n r w hfit cc`: from the parameters
of level `j` (slot width `L`, `rowsAt R₀ j` rows, `rw = r w`), every register at rest, every left
stack empty and `io` holding the stream of `Z`, the program `cp` ends with `io` holding the stream
of `layerZ u ds R₀ j (actMap a₀ ρ K (bits u j) n hfit) Z`, every other register and `user` as
before, within `cc` steps. `FactorSpecL` is `FactorSpec` (`Node/Regs.lean`) on register files whose
left stacks are all empty: the slot XORs of `basisProg_exec` run multitape machines on the left
stacks and are specified from empty left stacks.

**Main theorem** (`factorProg_spec`). At a node of level `j + 1` (`L = K · bits u (j + 1)`,
`rows = rowsAt R₀ (j + 1)`) with `ρ < K`, `a₀ + K · bits u (j + 1) ≤ n`, `expZ u ds j ≤ w`,
`14 ≤ A`, `1 ≤ u, r, w, R₀`, and `CallSpec` for the child of the pivot (offset
`a₀ + s · K · bits u j`, slot width `K · bits u j`) within `cc` steps, `factorProg` satisfies
`FactorSpecL` with the step bound `factorCost (nT SXReg) ds j u K ρ a₀ R₀ n r w g cc`: the sum of
the bounds of its stages (`basisCostN` rounds the real bound of `basisProg_exec` up, `childCost`
contains `cc`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.LayerMachine

open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


section Counted

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Move `|ctr|` symbols from `src` onto `dst` (reversed), counted by `ctr` through the empty
`tmp`; `ctr` is restored. The scan slot `cs` serves `xferBlock` as a one-value block counter. -/
noncomputable def cmove (src dst ctr tmp cs : Fin T) : Pr P T Q A U :=
  xferBlock (nd := 1) (fun _ => src) (fun _ => dst) ctr tmp cs 1 (fun _ => 0) .done

/-- `cmove`: the top `|ctr|` symbols `ys` of `src` move onto `dst` (reversed), in
`4 |ys| + 5` steps; every other register ends as it started. -/
theorem cmove_exec {src dst ctr tmp : Fin T} (cs : Fin T) (h1 : src ≠ ctr) (h2 : src ≠ tmp)
    (h3 : ctr ≠ tmp) (h4 : dst ≠ src) (h5 : dst ≠ ctr) (h6 : dst ≠ tmp)
    (ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : (S.R ctr).length = ys.length) (ht : S.R tmp = []) (hs : S.R src = ys ++ rest) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (cmove src dst ctr tmp cs) (mk v S) (4 * ys.length + 5)
        (mk v' { S with
          R := Function.update (Function.update S.R src rest) dst (ys.reverse ++ S.R dst) }) := by
  obtain ⟨v', R', hu, -, he, hctr, htmp, hsrc, hdst, hoth⟩ := xferBlock_exec body (nd := 1)
    (fun _ => src) (fun _ => dst) ctr tmp cs 1 (fun _ => 0) .done 0 h1 h2 h3 h4 h5 h6 (S.R ctr) ys
    rest v S hlen rfl ht hs (Subsingleton.elim _ _)
  refine ⟨{ v' with scan := Function.update v.scan cs (nextC 1 (v.scan cs)) }, hu,
    Exec.cast he (by rw [hlen]) ?_⟩
  rw [run_done]
  congr 2
  funext k
  by_cases hk4 : k = dst
  · subst hk4; rw [Function.update_self]; exact hdst
  rw [Function.update_of_ne hk4]
  by_cases hk1 : k = src
  · subst hk1; rw [Function.update_self]; exact hsrc
  rw [Function.update_of_ne hk1]
  by_cases hk2 : k = ctr
  · subst hk2; exact hctr
  by_cases hk3 : k = tmp
  · subst hk3; rw [htmp, ht]
  exact hoth k hk1 hk2 hk3 hk4

end Counted

/-! ### Saving and restoring a parameter register -/

/-- Evaluate register updates at register names. -/
local macro "fupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj, reduceCtorEq,
  ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.wire.injEq, LReg.wtmp.injEq, LReg.bc.injEq,
  LReg.ph.injEq, LReg.lf.injEq, Fin.reduceEq, Fin.isValue, movedR, List.map_id, id]) <;> try rfl)

section Save

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- Save register `X` on `park` and replace it by `|X| / c` ticks. -/
noncomputable def saveDiv (c : ℕ) (X : LReg BReg) : Pr P (nT BReg) Q A U :=
  .seq (udiv c (reg X) (reg (.sc 0)) (reg (.sc 1)))
    (.seq (moveR (reg X) (reg .park) id) (moveR (reg (.sc 0)) (reg X) id))

/-- `saveDiv`: `X` ends holding `|X| / c` ticks, `park` gains the reversed contents of `X`; every
other register ends as it started. -/
theorem saveDiv_exec {c : ℕ} (hc : 1 ≤ c) {X : LReg BReg} (hX0 : X ≠ .sc 0) (hX1 : X ≠ .sc 1)
    (hXp : X ≠ .park) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hs0 : S.R (reg (.sc 0)) = []) (hs1 : S.R (reg (.sc 1)) = []) :
    ∃ (v' : HS (nT BReg) Q A U) (k : ℕ), v'.user = v.user ∧ k ≤ 8 * (S.R (reg X)).length + 8 ∧
      Exec body (saveDiv c X) (mk v S) k
        (mk v' { S with
          R := Function.update (Function.update S.R (reg .park)
            ((S.R (reg X)).reverse ++ S.R (reg .park))) (reg X)
            (List.replicate ((S.R (reg X)).length / c) tick) }) := by
  have e1 : reg X ≠ reg (BReg := BReg) (.sc 0) := reg_ne hX0
  have e2 : reg X ≠ reg (BReg := BReg) (.sc 1) := reg_ne hX1
  have e3 : reg X ≠ reg (BReg := BReg) .park := reg_ne hXp
  have e4 : reg (BReg := BReg) (.sc 0) ≠ reg (.sc 1) := reg_ne (by simp)
  set q := (S.R (reg X)).length / c with hq
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := udiv_exec body hc e1 e2 e4 v S hs1
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate q tick ++ S.R (reg (.sc 0)))
    with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg X) (reg .park) e3 id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ (reg X) (reg .park) id (R₁ (reg X)) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (reg (.sc 0)) (reg X) e1.symm id v₂
    { S with R := R₂ }
  have e5 : reg (BReg := BReg) (.sc 0) ≠ reg .park := reg_ne (by simp)
  have h1 : R₁ (reg X) = S.R (reg X) := by rw [hR₁, Function.update_of_ne e1]
  have h2 : R₂ (reg (.sc 0)) = List.replicate q tick := by
    rw [hR₂, movedR, Function.update_of_ne e5, Function.update_of_ne e1.symm, hR₁,
      Function.update_self, hs0, List.append_nil]
  have h2X : R₂ (reg X) = [] := by
    rw [hR₂, movedR, Function.update_of_ne e3, Function.update_self]
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · dsimp only
    rw [h1, h2, List.length_replicate]
    have : q ≤ (S.R (reg X)).length := Nat.div_le_self _ _
    omega
  · congr 2
    funext k
    dsimp only
    rw [h2, movedR]
    by_cases ha : k = reg X
    · subst ha; rw [Function.update_self, Function.update_self, h2X, List.map_id,
        List.reverse_replicate, List.append_nil]
    rw [Function.update_of_ne ha, Function.update_of_ne ha]
    by_cases hb : k = reg (.sc 0)
    · subst hb
      rw [Function.update_self, Function.update_of_ne e5, hs0]
    rw [Function.update_of_ne hb, hR₂, movedR]
    by_cases hc' : k = reg .park
    · subst hc'
      rw [Function.update_self, Function.update_self, h1, hR₁, Function.update_of_ne e5.symm,
        List.map_id]
    rw [Function.update_of_ne hc', Function.update_of_ne hc', Function.update_of_ne ha, hR₁,
      Function.update_of_ne hb]

/-- Restore register `X` from `park`: `c |X|` symbols, counted by `lenctr`. -/
noncomputable def restoreMul (c : ℕ) (X : LReg BReg) : Pr P (nT BReg) Q A U :=
  .seq (umul c (reg X) (reg .lenctr) (reg (.sc 1)))
    (.seq (uclear (reg X))
      (.seq (cmove (reg .park) (reg X) (reg .lenctr) (reg (.sc 1)) (reg .cs))
        (uclear (reg .lenctr))))

/-- `restoreMul`: with `park` holding `ys ++ rest`, `|ys| = c |X|`, the register `X` ends holding
`ys` reversed and `park` holding `rest`; every other register ends as it started. -/
theorem restoreMul_exec {c : ℕ} {X : LReg BReg} (hXl : X ≠ .lenctr) (hX1 : X ≠ .sc 1)
    (hXp : X ≠ .park) (ys rest : List (Fin (A + 4))) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hl : S.R (reg .lenctr) = []) (hs1 : S.R (reg (.sc 1)) = [])
    (hys : ys.length = c * (S.R (reg X)).length) (hpark : S.R (reg .park) = ys ++ rest) :
    ∃ (v' : HS (nT BReg) Q A U) (k : ℕ), v'.user = v.user ∧
      k ≤ 6 * (S.R (reg X)).length + 6 * ys.length + 13 ∧
      Exec body (restoreMul c X) (mk v S) k
        (mk v' { S with
          R := Function.update (Function.update S.R (reg .park) rest) (reg X) ys.reverse }) := by
  have e1 : reg X ≠ reg (BReg := BReg) .lenctr := reg_ne hXl
  have e2 : reg X ≠ reg (BReg := BReg) (.sc 1) := reg_ne hX1
  have e3 : reg X ≠ reg (BReg := BReg) .park := reg_ne hXp
  have e4 : reg (BReg := BReg) .lenctr ≠ reg (.sc 1) := reg_ne (by simp)
  have e5 : reg (BReg := BReg) .park ≠ reg .lenctr := reg_ne (by simp)
  have e6 : reg (BReg := BReg) .park ≠ reg (.sc 1) := reg_ne (by simp)
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec body c e1 e2 e4 v S hs1
  set R₁ := Function.update S.R (reg .lenctr)
    (List.replicate (c * (S.R (reg X)).length) tick ++ S.R (reg .lenctr)) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body (reg X) v₁ { S with R := R₁ }
  set R₂ := Function.update R₁ (reg X) [] with hR₂
  have h2l : R₂ (reg .lenctr) = List.replicate ys.length tick := by
    rw [hR₂, Function.update_of_ne e1.symm, hR₁, Function.update_self, hl, List.append_nil, hys]
  have h2s : R₂ (reg (.sc 1)) = [] := by
    rw [hR₂, Function.update_of_ne e2.symm, hR₁, Function.update_of_ne e4.symm, hs1]
  have h2p : R₂ (reg .park) = ys ++ rest := by
    rw [hR₂, Function.update_of_ne e3.symm, hR₁, Function.update_of_ne e5, hpark]
  obtain ⟨v₃, hu₃, he₃⟩ := cmove_exec body (src := reg .park) (dst := reg X) (ctr := reg .lenctr)
    (tmp := reg (.sc 1)) (reg .cs) e5 e6 e4 e3 e1 e2 ys rest v₂ { S with R := R₂ }
    (by dsimp only; rw [h2l, List.length_replicate]) h2s h2p
  set R₃ := Function.update (Function.update R₂ (reg .park) rest) (reg X)
    (ys.reverse ++ R₂ (reg X)) with hR₃
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body (reg .lenctr) v₃ { S with R := R₃ }
  have h3l : R₃ (reg .lenctr) = List.replicate ys.length tick := by
    rw [hR₃, Function.update_of_ne e1.symm, Function.update_of_ne e5.symm, h2l]
  have h1X : R₁ (reg X) = S.R (reg X) := by rw [hR₁, Function.update_of_ne e1]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) rfl ?_⟩
  · dsimp only
    rw [h3l, h1X, List.length_replicate]
    omega
  · congr 2
    funext k
    dsimp only
    by_cases ha : k = reg .lenctr
    · subst ha; rw [Function.update_self, Function.update_of_ne e1.symm,
        Function.update_of_ne e5.symm, hl]
    rw [Function.update_of_ne ha, hR₃]
    by_cases hb : k = reg X
    · subst hb; rw [Function.update_self, Function.update_self, hR₂, Function.update_self,
        List.append_nil]
    rw [Function.update_of_ne hb, Function.update_of_ne hb]
    by_cases hc' : k = reg .park
    · subst hc'; rw [Function.update_self, Function.update_self]
    rw [Function.update_of_ne hc', Function.update_of_ne hc', hR₂, Function.update_of_ne hb, hR₁,
      Function.update_of_ne ha]

end Save

/-! ### Conjugation, shifts and parking on the bank -/

section Bank

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- The stream of the conjugate of `Z` is the stream of `Z` conjugated coefficientwise. -/
lemma encZ_conjZ {R r n w : ℕ} (Z : ZArr (Fin R × Fin r) n) :
    encZ A w (conjZ Z) = ((coeffList w Z).map GR.conj).flatMap (coeffSyms A w) := by
  rw [encZ, ← coeffList_map star GR.conj (fun z => red_star w z) Z]
  rfl

/-- The stream of `2 ^ s Z` is the stream of `Z` shifted by `s` bits coefficientwise. -/
lemma encZ_two_pow_smul {R r n w : ℕ} (s : ℕ) (Z : ZArr (Fin R × Fin r) n) :
    encZ A w ((2 ^ s : GaussianInt) • Z) = ((coeffList w Z).map fun z =>
      ((2 ^ s : ZMod (2 ^ w)) * z.1, (2 ^ s : ZMod (2 ^ w)) * z.2)).flatMap (coeffSyms A w) := by
  have h2 : (2 ^ s : GaussianInt) = ((2 ^ s : ℤ) : GaussianInt) := by push_cast; rfl
  have hre : ((2 : GaussianInt) ^ s).re = 2 ^ s := by rw [h2]; exact Zsqrtd.re_intCast _
  have him : ((2 : GaussianInt) ^ s).im = 0 := by rw [h2]; exact Zsqrtd.im_intCast _
  rw [encZ, ← coeffList_map (fun z => (2 ^ s : GaussianInt) * z) _ (fun z => ?_) Z]
  · rfl
  · simp only [red, Zsqrtd.re_mul, Zsqrtd.im_mul, hre, him, Prod.mk.injEq]
    push_cast
    constructor <;> ring

/-- Conjugate wire `x` through its temporary. -/
noncomputable def conjW (x : NWire) : Pr P (nT BReg) Q A U :=
  .seq (autoWords (fun _ : Fin 1 => reg (.wire x)) (fun _ => reg (.wtmp x)) (reg .st) (reg .ctr)
      (reg .tmp) (gaussAuto A ![![(0, -1)]] 1 true))
    (moveR (reg (.wtmp x)) (reg (.wire x)) id)

/-- The step bound of `conjW` on a wire of `R` rows. -/
def conjCost (R n r w : ℕ) : ℕ := R * 2 ^ n * r * (5 * w + 6) + 2 + (2 * (R * 2 ^ n * (r * w)) + 2)

/-- `conjW`: wire `x` goes from the stream of `Z` to the stream of `conjZ Z`; every other register
ends as it started. -/
theorem conjW_exec (hA : 5 ≤ A) {R r n w : ℕ} (hw : 1 ≤ w) (x : NWire)
    (Z : ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hctr : (S.R (reg .ctr)).length = w) (htmp : S.R (reg .tmp) = [])
    (hwt : S.R (reg (.wtmp x)) = []) (hx : S.R (reg (.wire x)) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ conjCost R n r w ∧
      Exec body (conjW x) (mk v S) c
        (mk v' { S with R := Function.update S.R (reg (.wire x)) (encZ A w (conjZ Z)) }) := by
  obtain ⟨v₁, m₁, S₁, hu₁, hm₁, he₁, hi₁, ho₁, hl₁, hX₁, hT₁, hoth₁⟩ :=
    conj_exec body (autoLayout_one (x := .wire x) (y := .wtmp x)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) (by norm_num; omega) hw hctr
      (coeffList w Z) v S rfl htmp hx
  have hS₁ : S₁ = { S with R := S₁.R } := Stacks.ext hi₁ ho₁ hl₁ rfl
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg (.wtmp x)) (reg (.wire x)) (reg_ne (by simp)) id
    v₁ S₁
  have hT₁' : S₁.R (reg (.wtmp x)) = (encZ A w (conjZ Z)).reverse := by
    rw [hT₁, hwt, List.append_nil, encZ_conjZ]
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
  · rw [hT₁', List.length_reverse, length_encZ]
    rw [length_coeffList] at hm₁
    unfold conjCost
    omega
  · rw [hS₁]
    congr 2
    funext k
    simp only [movedR, List.map_id]
    by_cases ha : k = reg (.wire x)
    · subst ha
      rw [Function.update_self, Function.update_self, hT₁', List.reverse_reverse, hX₁,
        List.append_nil]
    rw [Function.update_of_ne ha, Function.update_of_ne ha]
    by_cases hb : k = reg (.wtmp x)
    · subst hb; rw [Function.update_self, hwt]
    rw [Function.update_of_ne hb, hoth₁ k ha hb]

/-- Complex conjugation unless `q = 1`. -/
noncomputable def cconj {Y : Type} {n : ℕ} (q : ZMod 4) (Z : ZArr Y n) : ZArr Y n :=
  if q = 1 then Z else conjZ Z

/-- Conjugate wire `x` unless `q = 1`. -/
noncomputable def condConj (q : ZMod 4) (x : NWire) : Pr P (nT BReg) Q A U :=
  if q = 1 then .act .done else conjW x

/-- `condConj`: wire `x` goes from the stream of `Z` to the stream of `cconj q Z`. -/
theorem condConj_exec (hA : 5 ≤ A) {R r n w : ℕ} (hw : 1 ≤ w) (q : ZMod 4) (x : NWire)
    (Z : ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hctr : (S.R (reg .ctr)).length = w) (htmp : S.R (reg .tmp) = [])
    (hwt : S.R (reg (.wtmp x)) = []) (hx : S.R (reg (.wire x)) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ conjCost R n r w + 1 ∧
      Exec body (condConj q x) (mk v S) c
        (mk v' { S with R := Function.update S.R (reg (.wire x)) (encZ A w (cconj q Z)) }) := by
  by_cases hq : q = 1
  · refine ⟨v, 1, rfl, by omega, ?_⟩
    have he := Exec.act (body := body) (.done : Act (nT BReg) Q A U) (mk v S)
    rw [run_done] at he
    simp only [condConj, cconj, hq, ↓reduceIte]
    refine Exec.cast he rfl ?_
    rw [← hx, Function.update_eq_self]
  · obtain ⟨v', c, hu, hc, he⟩ := conjW_exec body hA hw x Z v S hctr htmp hwt hx
    refine ⟨v', c, hu, by omega, ?_⟩
    simp only [condConj, cconj, hq, ↓reduceIte]
    exact he

/-- Multiply the wires `x ∈ ws`, each through its temporary, by `2 ^ s`, with the shift counters
`cS = Tc` (`s` symbols) and `cR = sc 0` (`w - s` symbols). -/
theorem shiftListTc_exec {w s : ℕ} (hw : 1 ≤ w) (hs : s ≤ w) (N : ℕ) (zs : NWire → List (GR w))
    (hzs : ∀ x, (zs x).length = N) :
    ∀ (ws : List NWire), ws.Nodup → ∀ (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
      (∀ x ∈ ws, S.R (reg (.wire x)) = (zs x).flatMap (coeffSyms A w)) →
      (∀ x ∈ ws, S.R (reg (.wtmp x)) = []) →
      (S.R (reg .Tc)).length = s → (S.R (reg (.sc 0))).length = w - s →
      S.R (reg .tS) = [] → S.R (reg .tR) = [] →
      ∃ (v' : HS (nT BReg) Q A U) (R' : Fin (nT BReg) → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (Prog.seqList (ws.map fun x =>
            shiftInto (reg (.wire x)) (reg (.wtmp x)) (reg (.wire x)) (reg .Tc) (reg (.sc 0))
              (reg .tS) (reg .tR) (pairSym A false false)))
          (mk v S) (ws.length * (N * (6 * w + 4 * s + 14) + 4) + 1) (mk v' { S with R := R' }) ∧
        (∀ x ∈ ws, R' (reg (.wire x)) = ((zs x).map fun z =>
          ((2 ^ s : ZMod (2 ^ w)) * z.1, (2 ^ s : ZMod (2 ^ w)) * z.2)).flatMap (coeffSyms A w)) ∧
        ∀ k, (∀ x ∈ ws, k ≠ reg (.wire x)) → R' k = S.R k := by
  intro ws
  induction ws with
  | nil =>
      intro _ v S _ _ _ _ _ _
      exact ⟨v, S.R, rfl, by simpa [Prog.seqList] using Exec.act (body := body) .done (mk v S),
        by simp, fun _ _ => rfl⟩
  | cons u ws ih =>
      intro hnd v S hsrc hdst hcS hcR htS htR
      rw [List.nodup_cons] at hnd
      have hreg : [reg (BReg := BReg) (.wire u), reg (.wtmp u), reg .Tc, reg (.sc 0), reg .tS,
          reg .tR].Nodup :=
        nodup_map_reg (l := [.wire u, .wtmp u, .Tc, .sc 0, .tS, .tR]) (by simp)
      obtain ⟨v₁, R₁, hu₁, -, he₁, hout₁, -, hoth₁⟩ := shiftInto_exec body (reg (.wire u))
        (reg (.wtmp u)) (reg (.wire u)) (reg .Tc) (reg (.sc 0)) (reg .tS) (reg .tR) hreg
        (reg_ne (by simp)) hw hs (zs u) v S (hsrc u List.mem_cons_self) hcS hcR htS htR
        (hdst u List.mem_cons_self)
      have hfr : ∀ k, k ≠ reg (.wire u) → R₁ k = S.R k := fun k hk => hoth₁ k hk hk
      have hne : ∀ u' ∈ ws, reg (BReg := BReg) (.wire u') ≠ reg (.wire u) := fun u' hu' e =>
        hnd.1 (by rw [reg_inj, LReg.wire.injEq] at e; exact e ▸ hu')
      obtain ⟨v', R', hu', he', hρ', hoth'⟩ := ih hnd.2 v₁ { S with R := R₁ }
        (fun u' hu' => (hfr _ (hne u' hu')).trans (hsrc u' (List.mem_cons_of_mem _ hu')))
        (fun u' hu' => (hfr _ (reg_ne (by simp))).trans (hdst u' (List.mem_cons_of_mem _ hu')))
        ((congrArg List.length (hfr _ (reg_ne (by simp)))).trans hcS)
        ((congrArg List.length (hfr _ (reg_ne (by simp)))).trans hcR)
        ((hfr _ (reg_ne (by simp))).trans htS) ((hfr _ (reg_ne (by simp))).trans htR)
      refine ⟨v', R', hu'.trans hu₁, Exec.cast (Exec.seq he₁ he') ?_ rfl, ?_, ?_⟩
      · rw [hzs u, List.length_cons]
        ring
      · intro u' hu'
        rcases List.mem_cons.1 hu' with rfl | hu'
        · rw [hoth' _ (fun u'' hu'' => (hne u'' hu'').symm)]
          simpa using hout₁
        · exact hρ' u' hu'
      · intro k hk
        rw [hoth' k (fun u' hu' => hk u' (List.mem_cons_of_mem _ hu'))]
        exact hfr k (hk u List.mem_cons_self)

/-- Multiply the wires `x ∈ ws` by `2 ^ |Tc|`: build `w - |Tc|` symbols on `sc 0`, shift every wire
in place, clear `sc 0`. -/
noncomputable def shiftTc (ws : List NWire) : Pr P (nT BReg) Q A U :=
  .seq (ucopy (reg .w) (reg (.sc 0)) (reg (.sc 1)))
    (.seq (usub (reg .Tc) (reg (.sc 0)) (reg (.sc 1)))
      (.seq (Prog.seqList (ws.map fun x =>
          shiftInto (reg (.wire x)) (reg (.wtmp x)) (reg (.wire x)) (reg .Tc) (reg (.sc 0))
            (reg .tS) (reg .tR) (pairSym A false false)))
        (uclear (reg (.sc 0)))))

/-- The step bound of `shiftTc` on `F` wires of `R` rows, with shift `s`. -/
def shiftCost (F R n r w s : ℕ) : ℕ :=
  (4 * w + 4) + (4 * s + 4) + (F * (R * 2 ^ n * r * (6 * w + 4 * s + 14) + 4) + 1) + (2 * w + 2)

/-- `shiftTc`: every wire `x ∈ ws` goes from the stream of `B x` to the stream of `2 ^ s B x`,
`s = |Tc| ≤ w`; every other register ends as it started. -/
theorem shiftTc_exec {R r n w s : ℕ} (hw : 1 ≤ w) (hs : s ≤ w) (ws : List NWire)
    (hws : ws.Nodup) (B : NWire → ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hwr : (S.R (reg .w)).length = w) (hTc : (S.R (reg .Tc)).length = s)
    (hs0 : S.R (reg (.sc 0)) = []) (hs1 : S.R (reg (.sc 1)) = []) (htS : S.R (reg .tS) = [])
    (htR : S.R (reg .tR) = []) (hwt : ∀ x ∈ ws, S.R (reg (.wtmp x)) = [])
    (hB : ∀ x ∈ ws, S.R (reg (.wire x)) = encZ A w (B x)) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧ c ≤ shiftCost ws.length R n r w s ∧
      Exec body (shiftTc ws) (mk v S) c (mk v' { S with R := R' }) ∧
      (∀ x ∈ ws, R' (reg (.wire x)) = encZ A w ((2 ^ s : GaussianInt) • B x)) ∧
      ∀ k, (∀ x ∈ ws, k ≠ reg (.wire x)) → R' k = S.R k := by
  have e1 : reg (BReg := BReg) .w ≠ reg (.sc 0) := reg_ne (by simp)
  have e2 : reg (BReg := BReg) .w ≠ reg (.sc 1) := reg_ne (by simp)
  have e3 : reg (BReg := BReg) (.sc 0) ≠ reg (.sc 1) := reg_ne (by simp)
  have e4 : reg (BReg := BReg) .Tc ≠ reg (.sc 0) := reg_ne (by simp)
  have e5 : reg (BReg := BReg) .Tc ≠ reg (.sc 1) := reg_ne (by simp)
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body e1 e2 e3 v S hs1
  set R₁ := Function.update S.R (reg (.sc 0))
    (List.replicate (S.R (reg .w)).length tick ++ S.R (reg (.sc 0))) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := usub_exec body e4 e5 e3 v₁ { S with R := R₁ }
    (by dsimp only; rw [hR₁, Function.update_of_ne e3.symm, hs1])
  set R₂ := Function.update R₁ (reg (.sc 0)) ((R₁ (reg (.sc 0))).drop (R₁ (reg .Tc)).length)
    with hR₂
  have hR₂o : ∀ k, k ≠ reg (.sc 0) → R₂ k = S.R k := fun k hk => by
    rw [hR₂, Function.update_of_ne hk, hR₁, Function.update_of_ne hk]
  have hR₂s : R₂ (reg (.sc 0)) = List.replicate (w - s) tick := by
    rw [hR₂, Function.update_self, hR₁, Function.update_self, Function.update_of_ne e4, hs0,
      List.append_nil, hwr, hTc, List.drop_replicate]
  have hzs : ∀ x, (coeffList w (B x)).length = R * 2 ^ n * r := fun x => length_coeffList _
  obtain ⟨v₃, R₃, hu₃, he₃, hw₃, ho₃⟩ := shiftListTc_exec body hw hs (R * 2 ^ n * r)
    (fun x => coeffList w (B x)) hzs ws hws v₂ { S with R := R₂ }
    (fun x hx => (hR₂o _ (reg_ne (by simp))).trans (hB x hx))
    (fun x hx => (hR₂o _ (reg_ne (by simp))).trans (hwt x hx))
    (by dsimp only; rw [hR₂o _ e4, hTc])
    (by dsimp only; rw [hR₂s, List.length_replicate])
    ((hR₂o _ (reg_ne (by simp))).trans htS) ((hR₂o _ (reg_ne (by simp))).trans htR)
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body (reg (.sc 0)) v₃ { S with R := R₃ }
  have h3s : R₃ (reg (.sc 0)) = List.replicate (w - s) tick := by
    rw [ho₃ _ (fun x _ => reg_ne (by simp))]; exact hR₂s
  have h1T : R₁ (reg .Tc) = S.R (reg .Tc) := by rw [hR₁, Function.update_of_ne e4]
  refine ⟨v₄, _, Function.update R₃ (reg (.sc 0)) [], by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), ?_, ?_⟩
  · dsimp only
    rw [h3s, List.length_replicate, hwr, h1T, hTc]
    unfold shiftCost
    have := Nat.sub_le w s
    omega
  · intro x hx
    rw [Function.update_of_ne (reg_ne (by simp)), hw₃ x hx, encZ_two_pow_smul]
  · intro k hk
    by_cases h0 : k = reg (.sc 0)
    · rw [h0, Function.update_self, hs0]
    rw [Function.update_of_ne h0, ho₃ k hk]
    exact hR₂o k h0

/-- Park the wires of `l` on `park`, in order. -/
noncomputable def parkW (l : List NWire) : Pr P (nT BReg) Q A U :=
  Prog.seqList (l.map fun x => moveR (reg (.wire x)) (reg .park) id)

/-- `parkW`: the wires of `l` end empty and `park` gains their reversed contents, the last wire of
`l` on top; every other register ends as it started. -/
theorem parkW_exec (W : NWire → List (Fin (A + 4))) :
    ∀ (l : List NWire), l.Nodup → ∀ (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
      (∀ x ∈ l, S.R (reg (.wire x)) = W x) →
      ∃ (v' : HS (nT BReg) Q A U) (R' : Fin (nT BReg) → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (parkW l) (mk v S) ((l.map fun x => 2 * (W x).length + 2).sum + 1)
          (mk v' { S with R := R' }) ∧
        R' (reg .park) = (l.reverse.flatMap fun x => (W x).reverse) ++ S.R (reg .park) ∧
        (∀ x ∈ l, R' (reg (.wire x)) = []) ∧
        ∀ k, k ≠ reg .park → (∀ x ∈ l, k ≠ reg (.wire x)) → R' k = S.R k := by
  intro l
  induction l with
  | nil =>
      intro _ v S _
      have he := Exec.act (body := body) (.done : Act (nT BReg) Q A U) (mk v S)
      exact ⟨v, S.R, rfl, by simpa [parkW, Prog.seqList] using he, by simp, by simp,
        fun _ _ _ => rfl⟩
  | cons x l ih =>
      intro hnd v S hW
      rw [List.nodup_cons] at hnd
      have ep : reg (BReg := BReg) (.wire x) ≠ reg .park := reg_ne (by simp)
      obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body (reg (.wire x)) (reg .park) ep id v S
      set R₁ := movedR S.R (reg (.wire x)) (reg .park) id (S.R (reg (.wire x))) with hR₁
      have hne : ∀ x' ∈ l, reg (BReg := BReg) (.wire x') ≠ reg (.wire x) := fun x' hx' e =>
        hnd.1 (by rw [reg_inj, LReg.wire.injEq] at e; exact e ▸ hx')
      have hR₁o : ∀ k, k ≠ reg .park → k ≠ reg (.wire x) → R₁ k = S.R k := fun k h1 h2 => by
        rw [hR₁, movedR, Function.update_of_ne h1, Function.update_of_ne h2]
      obtain ⟨v₂, R₂, hu₂, he₂, hp₂, hw₂, ho₂⟩ := ih hnd.2 v₁ { S with R := R₁ }
        (fun x' hx' => (hR₁o _ (reg_ne (by simp)) (hne x' hx')).trans (hW x' (by simp [hx'])))
      refine ⟨v₂, R₂, hu₂.trans hu₁, Exec.cast (Exec.seq he₁ he₂) ?_ rfl, ?_, ?_, ?_⟩
      · rw [hW x List.mem_cons_self, List.map_cons, List.sum_cons]
        ring
      · rw [hp₂]
        dsimp only
        rw [hR₁, movedR, Function.update_self, List.map_id, hW x List.mem_cons_self,
          List.reverse_cons, List.flatMap_append, List.append_assoc]
        simp
      · intro x' hx'
        rcases List.mem_cons.1 hx' with rfl | hx'
        · rw [ho₂ _ ep (fun x'' hx'' => (hne x'' hx'').symm)]
          dsimp only
          rw [hR₁, movedR, Function.update_of_ne ep, Function.update_self]
        · exact hw₂ x' hx'
      · intro k hk1 hk2
        exact (ho₂ k hk1 (fun x' hx' => hk2 x' (List.mem_cons_of_mem _ hx'))).trans
          (hR₁o k hk1 (hk2 x List.mem_cons_self))

/-- Unpark the wires of `l`, in order, each by a counted move of `|lenctr|` symbols. -/
noncomputable def unparkW (l : List NWire) : Pr P (nT BReg) Q A U :=
  Prog.seqList (l.map fun x => cmove (reg .park) (reg (.wire x)) (reg .lenctr) (reg (.sc 1))
    (reg .cs))

/-- `unparkW`: with `park` holding the reversed contents `W x` (each of length `|lenctr|`) of the
empty wires `x ∈ l`, the first on top, every wire of `l` ends holding `W x`; every other register
ends as it started, `park` without these contents. -/
theorem unparkW_exec (W : NWire → List (Fin (A + 4))) (N : ℕ) (hWN : ∀ x, (W x).length = N) :
    ∀ (l : List NWire), l.Nodup → ∀ (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
      (p : List (Fin (A + 4))), (S.R (reg .lenctr)).length = N → S.R (reg (.sc 1)) = [] →
      S.R (reg .park) = (l.flatMap fun x => (W x).reverse) ++ p →
      (∀ x ∈ l, S.R (reg (.wire x)) = []) →
      ∃ (v' : HS (nT BReg) Q A U) (R' : Fin (nT BReg) → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (unparkW l) (mk v S) (l.length * (4 * N + 5) + 1) (mk v' { S with R := R' }) ∧
        R' (reg .park) = p ∧ (∀ x ∈ l, R' (reg (.wire x)) = W x) ∧
        ∀ k, k ≠ reg .park → (∀ x ∈ l, k ≠ reg (.wire x)) → R' k = S.R k := by
  intro l
  induction l with
  | nil =>
      intro _ v S p _ _ hp _
      have he := Exec.act (body := body) (.done : Act (nT BReg) Q A U) (mk v S)
      exact ⟨v, S.R, rfl, by simpa [unparkW, Prog.seqList] using he, by simpa using hp, by simp,
        fun _ _ _ => rfl⟩
  | cons x l ih =>
      intro hnd v S p hl hs1 hp hW
      rw [List.nodup_cons] at hnd
      have e1 : reg (BReg := BReg) .park ≠ reg .lenctr := reg_ne (by simp)
      have e2 : reg (BReg := BReg) .park ≠ reg (.sc 1) := reg_ne (by simp)
      have e3 : reg (BReg := BReg) .lenctr ≠ reg (.sc 1) := reg_ne (by simp)
      have e4 : reg (BReg := BReg) (.wire x) ≠ reg .park := reg_ne (by simp)
      have e5 : reg (BReg := BReg) (.wire x) ≠ reg .lenctr := reg_ne (by simp)
      have e6 : reg (BReg := BReg) (.wire x) ≠ reg (.sc 1) := reg_ne (by simp)
      obtain ⟨v₁, hu₁, he₁⟩ := cmove_exec body (reg .cs) e1 e2 e3 e4 e5 e6 (W x).reverse
        ((l.flatMap fun x => (W x).reverse) ++ p) v S
        (by rw [hl, List.length_reverse, hWN]) hs1
        (by rw [hp, List.flatMap_cons, List.append_assoc])
      set R₁ := Function.update (Function.update S.R (reg .park)
        ((l.flatMap fun x => (W x).reverse) ++ p)) (reg (.wire x))
        ((W x).reverse.reverse ++ S.R (reg (.wire x))) with hR₁
      have hne : ∀ x' ∈ l, reg (BReg := BReg) (.wire x') ≠ reg (.wire x) := fun x' hx' e =>
        hnd.1 (by rw [reg_inj, LReg.wire.injEq] at e; exact e ▸ hx')
      have hR₁o : ∀ k, k ≠ reg .park → k ≠ reg (.wire x) → R₁ k = S.R k := fun k h1 h2 => by
        rw [hR₁, Function.update_of_ne h2, Function.update_of_ne h1]
      obtain ⟨v₂, R₂, hu₂, he₂, hp₂, hw₂, ho₂⟩ := ih hnd.2 v₁ { S with R := R₁ } p
        (by dsimp only; rw [hR₁o _ e1.symm (reg_ne (by simp)), hl])
        (by dsimp only; rw [hR₁o _ e2.symm (reg_ne (by simp)), hs1])
        (by dsimp only; rw [hR₁, Function.update_of_ne e4.symm, Function.update_self])
        (fun x' hx' => by
          dsimp only
          rw [hR₁o _ (reg_ne (by simp)) (hne x' hx'), hW x' (List.mem_cons_of_mem _ hx')])
      refine ⟨v₂, R₂, hu₂.trans hu₁, Exec.cast (Exec.seq he₁ he₂) ?_ rfl, hp₂, ?_, ?_⟩
      · rw [List.length_reverse, hWN, List.length_cons]
        ring
      · intro x' hx'
        rcases List.mem_cons.1 hx' with rfl | hx'
        · rw [ho₂ _ e4 (fun x'' hx'' => (hne x'' hx'').symm)]
          dsimp only
          rw [hR₁, Function.update_self, List.reverse_reverse, hW x' List.mem_cons_self,
            List.append_nil]
        · exact hw₂ x' hx'
      · intro k hk1 hk2
        exact (ho₂ k hk1 (fun x' hx' => hk2 x' (List.mem_cons_of_mem _ hx'))).trans
          (hR₁o k hk1 (hk2 x List.mem_cons_self))

end Bank

/-! ### The child call -/

section Call

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}
  (body : P → Pr P (nT BReg) Q A U)

/-- **The child call.** The program `cp` computes the layer at level `j` on `io`: from the
parameters of level `j` (`a₀`, slot width `L`, `rowsAt R₀ j` rows, `rw = r w`), every register at
rest, every left stack empty and `io` holding the stream of `Z`, it ends with `io` holding the
stream of `layerZ u ds R₀ j e Z`, `e i = a₀ + ρ + K i`, every other register and `user` as
before, within `cc` steps. -/
def CallSpec (cp : Pr P (nT BReg) Q A U) (bcRest : BReg → List (Fin (A + 4)) → Prop)
    (ds : ComplexFramedExecution.Directions) (R₀ j u K ρ a₀ L n r w : ℕ)
    (hfit : ∀ i < bits u j, a₀ + ρ + K * i < n) (cc : ℕ) : Prop :=
  ∀ (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
    (∀ y, S.L y = []) → ParState S.R j u K ρ a₀ L (rowsAt R₀ j) n w (r * w) →
    Rest bcRest n r w S.R → S.R (reg .io) = encZ A w Z →
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ cc ∧
      Exec body cp (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io)
          (encZ A w (layerZ u ds R₀ j (actMap a₀ ρ K (bits u j) n hfit) Z)) })

/-- Before the call: the top symbol of `lev` and the contents of `Tc` go onto `park`, `a₀` gains
`s |L|` ticks. -/
noncomputable def callPre (s : ℕ) : Pr P (nT BReg) Q A U :=
  .seq (.act (moveStep (reg .lev) (reg .park) id))
    (.seq (moveR (reg .Tc) (reg .park) id) (umul s (reg .L) (reg .a₀) (reg (.sc 1))))

/-- `callPre`: with `lev` holding `x₀ :: rest`, `lev` ends holding `rest`, `park` gains `x₀` and
then the reversed contents of `Tc`, `Tc` ends empty and `a₀` gains `s |L|` ticks; every other
register ends as it started. -/
theorem callPre_exec (s : ℕ) {x₀ : Fin (A + 4)} {rest : List (Fin (A + 4))}
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hlev : S.R (reg .lev) = x₀ :: rest)
    (hs1 : S.R (reg (.sc 1)) = []) :
    ∃ v' : HS (nT BReg) Q A U, v'.user = v.user ∧
      Exec body (callPre s) (mk v S)
        (1 + (2 * (S.R (reg .Tc)).length + 2) + (4 * (S.R (reg .L)).length + 4))
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update S.R
            (reg .lev) rest) (reg .park) ((S.R (reg .Tc)).reverse ++ x₀ :: S.R (reg .park)))
            (reg .Tc) []) (reg .a₀)
            (List.replicate (s * (S.R (reg .L)).length) tick ++ S.R (reg .a₀)) }) := by
  have e1 : reg (BReg := BReg) .lev ≠ reg .park := reg_ne (by simp)
  have he₁ := Exec.act (body := body) (moveStep (reg .lev) (reg .park) id) (mk v S)
  rw [moveStep_run e1 id v S hlev] at he₁
  set R₁ := Function.update (Function.update S.R (reg .lev) rest) (reg .park)
    (id x₀ :: S.R (reg .park)) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg .Tc) (reg .park) (reg_ne (by simp)) id
    { v with sym := some x₀, flag := rest.head?.isSome } { S with R := R₁ }
  set R₂ := movedR R₁ (reg .Tc) (reg .park) id (R₁ (reg .Tc)) with hR₂
  have h2s : R₂ (reg (.sc 1)) = [] := by
    rw [hR₂, movedR]; simp only [Function.update_apply, reg_inj, reduceCtorEq, ↓reduceIte, hR₁]
    exact hs1
  obtain ⟨v₃, hu₃, he₃⟩ := umul_exec body s (a := reg .L) (b := reg .a₀) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ } h2s
  refine ⟨v₃, by rw [hu₃, hu₂], Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) ?_ ?_⟩
  · simp only [hR₂, hR₁, movedR, Function.update_apply, reg_inj, reduceCtorEq, ↓reduceIte]
    ring
  · congr 2
    funext k
    dsimp only
    by_cases h1 : k = reg .a₀
    · subst h1; simp only [hR₂, hR₁]; fupd
    by_cases h2 : k = reg .Tc
    · subst h2; simp only [hR₂, hR₁]; fupd
    by_cases h3 : k = reg .park
    · subst h3; simp only [hR₂, hR₁]; fupd
    by_cases h4 : k = reg .lev
    · subst h4; simp only [hR₂, hR₁]; fupd
    simp only [hR₂, hR₁, movedR, Function.update_apply, h1, h2, h3, h4, ↓reduceIte]

/-- After the call: `a₀` loses `s |L|` symbols, `Tc` is restored from `park` (counted by
`expSeq G F |u| |lev|` ticks on `lenctr`), and the top symbol of `park` returns to `lev`. -/
noncomputable def callPost (s G F : ℕ) : Pr P (nT BReg) Q A U :=
  .seq (umul s (reg .L) (reg .lenctr) (reg (.sc 1)))
  (.seq (usub (reg .lenctr) (reg .a₀) (reg (.sc 1)))
  (.seq (uclear (reg .lenctr))
  (.seq (expProg G F (reg .u) (reg .lev) (reg .lenctr) (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)))
  (.seq (cmove (reg .park) (reg .Tc) (reg .lenctr) (reg (.sc 1)) (reg .cs))
  (.seq (uclear (reg .lenctr))
    (.act (moveStep (reg .park) (reg .lev) id)))))))

/-- `callPost`: with `a₀` holding `s |L|` ticks on top of `a`, `Tc` empty and `park` holding
`ys ++ x₀ :: p`, `|ys| = expSeq G F |u| |lev|`, the register `a₀` ends holding `a`, `Tc` holding
`ys` reversed, `park` holding `p` and `lev` gains `x₀`; every other register ends as it started. -/
theorem callPost_exec (s G F : ℕ) {x₀ : Fin (A + 4)} {a ys p : List (Fin (A + 4))}
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A) (hl : S.R (reg .lenctr) = [])
    (hs1 : S.R (reg (.sc 1)) = []) (hs2 : S.R (reg (.sc 2)) = []) (hs3 : S.R (reg (.sc 3)) = [])
    (ha : S.R (reg .a₀) = List.replicate (s * (S.R (reg .L)).length) tick ++ a)
    (hTc : S.R (reg .Tc) = [])
    (hys : ys.length = expSeq G F (S.R (reg .u)).length (S.R (reg .lev)).length)
    (hpark : S.R (reg .park) = ys ++ x₀ :: p) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ (4 * (S.R (reg .L)).length + 4) + (4 * (s * (S.R (reg .L)).length) + 4) +
        (2 * (s * (S.R (reg .L)).length) + 2) +
        expCost G F (S.R (reg .u)).length (S.R (reg .lev)).length + (4 * ys.length + 5) +
        (2 * ys.length + 2) + 1 ∧
      Exec body (callPost s G F) (mk v S) c
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update S.R
            (reg .a₀) a) (reg .Tc) ys.reverse) (reg .park) p) (reg .lev)
            (x₀ :: S.R (reg .lev)) }) := by
  set q := s * (S.R (reg .L)).length with hq
  -- `a₀` loses `q` symbols
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec body s (a := reg .L) (b := reg .lenctr) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v S hs1
  set R₁ := Function.update S.R (reg .lenctr) (List.replicate q tick ++ S.R (reg .lenctr))
    with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := usub_exec body (a := reg .lenctr) (b := reg .a₀) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp only [hR₁, Function.update_apply, reg_inj, reduceCtorEq, ↓reduceIte]; exact hs1)
  set R₂ := Function.update R₁ (reg .a₀) ((R₁ (reg .a₀)).drop (R₁ (reg .lenctr)).length)
    with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (reg .lenctr) v₂ { S with R := R₂ }
  set R₃ := Function.update R₂ (reg .lenctr) [] with hR₃
  have h3 : ∀ k, k ≠ reg .a₀ → R₃ k = S.R k := by
    intro k hk
    rw [hR₃, hR₂, Function.update_apply, Function.update_of_ne hk, hR₁, Function.update_apply]
    split_ifs with h
    · rw [h, hl]
    · rfl
  have h3a : R₃ (reg .a₀) = a := by
    rw [hR₃, Function.update_of_ne (reg_ne (by simp)), hR₂, Function.update_self, hR₁,
      Function.update_self, Function.update_of_ne (reg_ne (by simp)), ha, hl, List.append_nil,
      List.length_replicate, List.drop_left' (List.length_replicate ..)]
  -- the counter of `Tc`
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := expProg_exec body G F (uR := reg .u) (jR := reg .lev)
    (eR := reg .lenctr) (t₁ := reg (.sc 1)) (t₂ := reg (.sc 2)) (t₃ := reg (.sc 3))
    (nodup_map_reg (l := [.u, .lev, .lenctr, .sc 1, .sc 2, .sc 3]) (by simp)) v₃
    { S with R := R₃ } (by rw [hR₃]; exact Function.update_self ..)
    ((h3 _ (reg_ne (by simp))).trans hs1) ((h3 _ (reg_ne (by simp))).trans hs2)
    ((h3 _ (reg_ne (by simp))).trans hs3)
  set R₄ := Function.update R₃ (reg .lenctr)
    (List.replicate (expSeq G F (R₃ (reg .u)).length (R₃ (reg .lev)).length) tick) with hR₄
  have h4l : R₄ (reg .lenctr) = List.replicate ys.length tick := by
    rw [hR₄, Function.update_self, h3 _ (reg_ne (by simp)), h3 _ (reg_ne (by simp)), hys]
  have h4 : ∀ k, k ≠ reg .a₀ → k ≠ reg .lenctr → R₄ k = S.R k := fun k h1 h2 => by
    rw [hR₄, Function.update_of_ne h2, h3 k h1]
  -- `Tc` from `park`
  obtain ⟨v₅, hu₅, he₅⟩ := cmove_exec body (src := reg .park) (dst := reg .Tc)
    (ctr := reg .lenctr) (tmp := reg (.sc 1)) (reg .cs) (reg_ne (by simp)) (reg_ne (by simp))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) ys (x₀ :: p) v₄
    { S with R := R₄ } (by dsimp only; rw [h4l, List.length_replicate])
    (by dsimp only; rw [h4 _ (reg_ne (by simp)) (reg_ne (by simp)), hs1])
    (by dsimp only; rw [h4 _ (reg_ne (by simp)) (reg_ne (by simp)), hpark])
  set R₅ := Function.update (Function.update R₄ (reg .park) (x₀ :: p)) (reg .Tc)
    (ys.reverse ++ R₄ (reg .Tc)) with hR₅
  obtain ⟨v₆, hu₆, he₆⟩ := uclear_exec body (reg .lenctr) v₅ { S with R := R₅ }
  set R₆ := Function.update R₅ (reg .lenctr) [] with hR₆
  have h6p : R₆ (reg .park) = x₀ :: p := by
    rw [hR₆, Function.update_of_ne (reg_ne (by simp)), hR₅,
      Function.update_of_ne (reg_ne (by simp)),
      Function.update_self]
  have he₇ := Exec.act (body := body) (moveStep (reg .park) (reg .lev) id)
    (mk v₆ { S with R := R₆ })
  rw [moveStep_run (reg_ne (by simp)) id v₆ { S with R := R₆ } h6p] at he₇
  have h6 : ∀ k, k ≠ reg .park → k ≠ reg .Tc → k ≠ reg .lenctr → k ≠ reg .a₀ → R₆ k = S.R k :=
    fun k g1 g2 g3 g4 => by
      rw [hR₆, Function.update_of_ne g3, hR₅, Function.update_of_ne g2, Function.update_of_ne g1,
        h4 k g4 g3]
  have h6T : R₆ (reg .Tc) = ys.reverse := by
    rw [hR₆, Function.update_of_ne (reg_ne (by simp)), hR₅, Function.update_self,
      h4 _ (reg_ne (by simp)) (reg_ne (by simp)), hTc, List.append_nil]
  have h6a : R₆ (reg .a₀) = a := by
    rw [hR₆, Function.update_of_ne (reg_ne (by simp)), hR₅,
      Function.update_of_ne (reg_ne (by simp)),
      Function.update_of_ne (reg_ne (by simp)), hR₄, Function.update_of_ne (reg_ne (by simp)), h3a]
  have h6l : R₆ (reg .lenctr) = [] := by rw [hR₆, Function.update_self]
  refine ⟨{ v₆ with sym := some x₀, flag := p.head?.isSome }, _,
    by show v₆.user = v.user; rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ he₇)))))) rfl ?_⟩
  · have h1L : R₁ (reg .L) = S.R (reg .L) := by
      rw [hR₁, Function.update_of_ne (reg_ne (by simp))]
    have h1l : (R₁ (reg .lenctr)).length = q := by
      rw [hR₁, Function.update_self, hl, List.append_nil, List.length_replicate]
    have h2l : (R₂ (reg .lenctr)).length = q := by
      rw [hR₂, Function.update_of_ne (reg_ne (by simp)), h1l]
    have h5l : (R₅ (reg .lenctr)).length = ys.length := by
      rw [hR₅, Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp)),
        h4l, List.length_replicate]
    have hm₄' : m₄ ≤ expCost G F (S.R (reg .u)).length (S.R (reg .lev)).length := by
      have := hm₄
      dsimp only at this
      rw [h3 _ (reg_ne (by simp)), h3 _ (reg_ne (by simp))] at this
      exact this
    dsimp only
    rw [h2l, h5l]
    omega
  · congr 2
    funext k
    dsimp only
    by_cases h1 : k = reg .lev
    · subst h1
      rw [Function.update_self, Function.update_self,
        h6 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]
      rfl
    rw [Function.update_of_ne h1, Function.update_of_ne h1]
    by_cases h2 : k = reg .park
    · subst h2
      rw [Function.update_self, Function.update_self]
    rw [Function.update_of_ne h2, Function.update_of_ne h2]
    by_cases h3' : k = reg .lenctr
    · subst h3'
      rw [h6l, Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp)),
        hl]
    by_cases h4' : k = reg .Tc
    · subst h4'
      rw [h6T, Function.update_self]
    rw [Function.update_of_ne h4']
    by_cases h5 : k = reg .a₀
    · subst h5
      rw [h6a, Function.update_self]
    rw [Function.update_of_ne h5, h6 k h2 h4' h3' h5]

/-- The child call proper: `callPre`, the call `cp`, `callPost`. -/
noncomputable def callCore (s G F : ℕ) (cp : Pr P (nT BReg) Q A U) : Pr P (nT BReg) Q A U :=
  .seq (callPre s) (.seq cp (callPost s G F))

/-- The step bound of `callCore`: slot width `Lc`, pivot `s`, child exponent `Tc`, call bound
`cc`. -/
def callCost (G F u j Lc s Tc cc : ℕ) : ℕ :=
  (1 + (2 * Tc + 2) + (4 * Lc + 4)) + cc +
    ((4 * Lc + 4) + (4 * (s * Lc) + 4) + (2 * (s * Lc) + 2) + expCost G F u j + (4 * Tc + 5) +
      (2 * Tc + 2) + 1)

/-- **The child call proper.** From the parameters of level `j + 1` with the child's slot width
`Lc` and row count `rowsAt R₀ j`, every register but `Tc` at rest, `Tc` holding
`expSeq G F u j` symbols and `io` the stream of `Z`, `callCore` leaves on `io` the stream of the
level-`j` layer of `Z` with offset `a₀ + s Lc`; every other register ends as it started. -/
theorem callCore_exec {bcRest : BReg → List (Fin (A + 4)) → Prop}
    (ds : ComplexFramedExecution.Directions) {R₀ j u K ρ a₀ Lc n r w s cc : ℕ} (G F : ℕ)
    (cp : Pr P (nT BReg) Q A U) (hfit : ∀ i < bits u j, a₀ + s * Lc + ρ + K * i < n)
    (hcall : CallSpec body cp bcRest ds R₀ j u K ρ (a₀ + s * Lc) Lc n r w hfit cc)
    (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y, S.L y = [])
    (hpar : ParState S.R (j + 1) u K ρ a₀ Lc (rowsAt R₀ j) n w (r * w))
    (hrest : RestBut bcRest n r w (· = .Tc) S.R)
    (hTc : (S.R (reg .Tc)).length = expSeq G F u j) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ callCost G F u j Lc s (expSeq G F u j) cc ∧
      Exec body (callCore s G F cp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg .io)
          (encZ A w (layerZ u ds R₀ j (actMap (a₀ + s * Lc) ρ K (bits u j) n hfit) Z)) }) := by
  have hlev : (S.R (reg .lev)).length = j + 1 := hpar .lev
  obtain ⟨x₀, rest, hl⟩ : ∃ x₀ rest, S.R (reg .lev) = x₀ :: rest := by
    cases h : S.R (reg .lev) with
    | nil => rw [h] at hlev; simp at hlev
    | cons x rest => exact ⟨x, rest, rfl⟩
  have hrl : rest.length = j := by rw [hl] at hlev; simpa using hlev
  have hs : ∀ i, S.R (reg (.sc i)) = [] := fun i => hrest (.sc i) (by simp)
  have hLc : (S.R (reg .L)).length = Lc := hpar .L
  obtain ⟨v₁, hu₁, he₁⟩ := callPre_exec body s v S hl (hs 1)
  set Rp := Function.update (Function.update (Function.update (Function.update S.R
    (reg .lev) rest) (reg .park) ((S.R (reg .Tc)).reverse ++ x₀ :: S.R (reg .park)))
    (reg .Tc) []) (reg .a₀) (List.replicate (s * (S.R (reg .L)).length) tick ++ S.R (reg .a₀))
    with hRp
  have hpf : ∀ k, k ≠ reg .lev → k ≠ reg .park → k ≠ reg .Tc → k ≠ reg .a₀ → Rp k = S.R k :=
    fun k h1 h2 h3 h4 => by
      rw [hRp, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1]
  -- the state of the call
  have hparC : ParState Rp j u K ρ (a₀ + s * Lc) Lc (rowsAt R₀ j) n w (r * w) := by
    intro x
    by_cases hx1 : x = .lev
    · subst hx1
      show (Rp (reg .lev)).length = j
      simp only [hRp]; fupd; exact hrl
    by_cases hx2 : x = .a₀
    · subst hx2
      show (Rp (reg .a₀)).length = a₀ + s * Lc
      simp only [hRp]; fupd
      rw [List.length_append, List.length_replicate, hLc, hpar .a₀]
      ring
    by_cases hx3 : x = .park
    · subst hx3; exact trivial
    by_cases hx4 : x = .Tc
    · subst hx4; exact trivial
    have h := hpar x
    rw [← hpf (reg x) (reg_ne hx1) (reg_ne hx3) (reg_ne hx4) (reg_ne hx2)] at h
    cases x <;> first | exact trivial | exact absurd rfl hx1 | exact absurd rfl hx2 | exact h
  have hrestC : Rest bcRest n r w Rp := by
    intro x
    by_cases hx1 : x = .lev
    · subst hx1; exact trivial
    by_cases hx2 : x = .a₀
    · subst hx2; exact trivial
    by_cases hx3 : x = .park
    · subst hx3; exact trivial
    by_cases hx4 : x = .Tc
    · subst hx4
      show Rp (reg .Tc) = []
      simp only [hRp]; fupd
    rw [hpf (reg x) (reg_ne hx1) (reg_ne hx3) (reg_ne hx4) (reg_ne hx2)]
    exact hrest x hx4
  obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := hcall Z v₁ { S with R := Rp } hL hparC hrestC
    (by dsimp only; rw [hpf _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)), hio])
  set Y := encZ A w (layerZ u ds R₀ j (actMap (a₀ + s * Lc) ρ K (bits u j) n hfit) Z) with hY
  set Rc := Function.update Rp (reg .io) Y with hRc
  have hcf : ∀ k, k ≠ reg .io → k ≠ reg .lev → k ≠ reg .park → k ≠ reg .Tc → k ≠ reg .a₀ →
      Rc k = S.R k := fun k h0 h1 h2 h3 h4 => by
    rw [hRc, Function.update_of_ne h0, hpf k h1 h2 h3 h4]
  have hcfr : ∀ x : LReg BReg, x ≠ .io → x ≠ .lev → x ≠ .park → x ≠ .Tc → x ≠ .a₀ →
      Rc (reg x) = S.R (reg x) := fun x h0 h1 h2 h3 h4 =>
    hcf _ (reg_ne h0) (reg_ne h1) (reg_ne h2) (reg_ne h3) (reg_ne h4)
  obtain ⟨v₃, c₃, hu₃, hc₃, he₃⟩ := callPost_exec body s G F (x₀ := x₀) (a := S.R (reg .a₀))
    (ys := (S.R (reg .Tc)).reverse) (p := S.R (reg .park)) v₂ { S with R := Rc }
    (by dsimp only
        rw [hcfr _ (by simp) (by simp) (by simp) (by simp) (by simp)]
        exact hrest .lenctr (by simp))
    (by dsimp only; rw [hcfr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hs 1)
    (by dsimp only; rw [hcfr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hs 2)
    (by dsimp only; rw [hcfr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hs 3)
    (by dsimp only; rw [hcfr .L (by simp) (by simp) (by simp) (by simp) (by simp)]
        simp only [hRc, hRp]; fupd)
    (by dsimp only; simp only [hRc, hRp]; fupd)
    (by dsimp only; rw [hcfr .u (by simp) (by simp) (by simp) (by simp) (by simp),
          List.length_reverse, hTc, hpar .u]
        simp only [hRc, hRp]; fupd; rw [hrl])
    (by dsimp only; simp only [hRc, hRp]; fupd)
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · have hc₃' := hc₃
    dsimp only at hc₃'
    rw [hcfr .L (by simp) (by simp) (by simp) (by simp) (by simp), hcfr .u (by simp) (by simp)
      (by simp) (by simp) (by simp), List.length_reverse, hTc, hLc, hpar .u] at hc₃'
    have hlv : (Rc (reg .lev)).length = j := by simp only [hRc, hRp]; fupd; exact hrl
    rw [hlv] at hc₃'
    rw [hLc]
    unfold callCost
    omega
  · congr 2
    funext k
    dsimp only
    by_cases h1 : k = reg .lev
    · subst h1; simp only [hRc, hRp]; fupd; exact hl.symm
    by_cases h2 : k = reg .park
    · subst h2; simp only [hRc, hRp]; fupd
    by_cases h3 : k = reg .Tc
    · subst h3; simp only [hRc, hRp]; fupd; exact List.reverse_reverse _
    by_cases h4 : k = reg .a₀
    · subst h4; simp only [hRc, hRp]; fupd
    by_cases h0 : k = reg .io
    · subst h0; simp only [hRc, hRp]; fupd
    rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h0, hcf k h0 h1 h2 h3 h4]

/-- The wires other than `fw`. -/
noncomputable def otherW (fw : NWire) : List NWire := (Finset.univ.erase fw).toList

lemma mem_otherW {fw x : NWire} : x ∈ otherW fw ↔ x ≠ fw := by simp [otherW]

lemma nodup_otherW (fw : NWire) : (otherW fw).Nodup := Finset.nodup_toList _

lemma length_otherW_le (fw : NWire) : (otherW fw).length ≤ NB := by
  rw [otherW, Finset.length_toList, NB_card]
  exact (Finset.card_erase_le).trans (by rw [Finset.card_univ])

/-- **The child call on wire `fw`**: park the other wires, move `fw` onto `io`, `callCore`, move
`io` back onto `fw` while counting its length on `lenctr`, unpark the other wires by counted
moves, clear the counter. -/
noncomputable def childCall (fw : NWire) (s G F : ℕ) (cp : Pr P (nT BReg) Q A U) :
    Pr P (nT BReg) Q A U :=
  .seq (parkW (otherW fw))
  (.seq (moveR (reg (.wire fw)) (reg (.wtmp fw)) id)
  (.seq (moveR (reg (.wtmp fw)) (reg .io) id)
  (.seq (callCore s G F cp)
  (.seq (ucopy (reg .io) (reg .lenctr) (reg (.sc 1)))
  (.seq (moveR (reg .io) (reg (.wtmp fw)) id)
  (.seq (moveR (reg (.wtmp fw)) (reg (.wire fw)) id)
  (.seq (unparkW (otherW fw).reverse)
    (uclear (reg .lenctr)))))))))

/-- The step bound of `childCall` on wires of `N` symbols. -/
noncomputable def childCost (N G F u j Lc s Tc cc : ℕ) : ℕ :=
  (NB * (2 * N + 2) + 1) + (2 * N + 2) + (2 * N + 2) + callCost G F u j Lc s Tc cc + (4 * N + 4) +
    (2 * N + 2) + (2 * N + 2) + (NB * (4 * N + 5) + 1) + (2 * N + 2)

/-- **The child call on a wire.** From the node-internal state at level `j + 1` with the child's
slot width `Lc` and row count, `Tc` holding `expSeq G F u j` symbols and the wires holding the bank
`B`, `childCall` replaces wire `fw` by the level-`j` layer of `B fw` with offset `a₀ + s Lc`; every
other register ends as it started. -/
theorem childCall_exec {bcRest : BReg → List (Fin (A + 4)) → Prop}
    (ds : ComplexFramedExecution.Directions) {R₀ j u K ρ a₀ Lc n r w s cc : ℕ} (G F : ℕ)
    (cp : Pr P (nT BReg) Q A U) (hfit : ∀ i < bits u j, a₀ + s * Lc + ρ + K * i < n)
    (hcall : CallSpec body cp bcRest ds R₀ j u K ρ (a₀ + s * Lc) Lc n r w hfit cc) (fw : NWire)
    (B : NWire → ZArr (Fin (rowsAt R₀ j) × Fin r) n) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hL : ∀ y, S.L y = [])
    (hpar : ParState S.R (j + 1) u K ρ a₀ Lc (rowsAt R₀ j) n w (r * w))
    (hrest : RestBut bcRest n r w (fun x => (∃ y, x = .wire y) ∨ x = .Tc) S.R)
    (hio : S.R (reg .io) = []) (hTc : (S.R (reg .Tc)).length = expSeq G F u j)
    (hB : ∀ x, S.R (reg (.wire x)) = encZ A w (B x)) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ childCost (rowsAt R₀ j * 2 ^ n * (r * w)) G F u j Lc s (expSeq G F u j) cc ∧
      Exec body (childCall fw s G F cp) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg (.wire fw))
          (encZ A w (layerZ u ds R₀ j (actMap (a₀ + s * Lc) ρ K (bits u j) n hfit) (B fw))) }) := by
  set N := rowsAt R₀ j * 2 ^ n * (r * w) with hN
  set W : NWire → List (Fin (A + 4)) := fun x => encZ A w (B x) with hW
  have hWN : ∀ x, (W x).length = N := fun x => length_encZ _
  set Y := encZ A w (layerZ u ds R₀ j (actMap (a₀ + s * Lc) ρ K (bits u j) n hfit) (B fw))
    with hY
  have hYN : Y.length = N := length_encZ _
  have hfwo : fw ∉ otherW fw := fun h => mem_otherW.1 h rfl
  have hwo : ∀ x, x ≠ fw → x ∈ otherW fw := fun x h => mem_otherW.2 h
  -- park the other wires
  obtain ⟨v₁, R₁, hu₁, he₁, hp₁, hw₁, ho₁⟩ := parkW_exec body W (otherW fw) (nodup_otherW fw) v S
    (fun x _ => hB x)
  have hf₁ : ∀ x : LReg BReg, x ≠ .park → (∀ y, x ≠ .wire y) → R₁ (reg x) = S.R (reg x) :=
    fun x h1 h2 => ho₁ _ (reg_ne h1) (fun y _ => reg_ne (h2 y))
  have h1fw : R₁ (reg (.wire fw)) = W fw := by
    rw [ho₁ _ (reg_ne (by simp)) (fun y hy => reg_ne (by
      simp only [ne_eq, LReg.wire.injEq]; rintro rfl; exact hfwo hy))]
    exact hB fw
  -- `fw` onto `io`
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg (.wire fw)) (reg (.wtmp fw)) (reg_ne (by simp)) id
    v₁ { S with R := R₁ }
  set R₂ := movedR R₁ (reg (.wire fw)) (reg (.wtmp fw)) id (R₁ (reg (.wire fw))) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (reg (.wtmp fw)) (reg .io) (reg_ne (by simp)) id
    v₂ { S with R := R₂ }
  set R₃ := movedR R₂ (reg (.wtmp fw)) (reg .io) id (R₂ (reg (.wtmp fw))) with hR₃
  have h2t : R₂ (reg (.wtmp fw)) = (W fw).reverse := by
    rw [hR₂, movedR, Function.update_self, h1fw, List.map_id, hf₁ _ (by simp) (by simp),
      hrest (.wtmp fw) (by simp), List.append_nil]
  have h3 : ∀ k, k ≠ reg .io → k ≠ reg (.wtmp fw) → k ≠ reg (.wire fw) → R₃ k = R₁ k :=
    fun k h1 h2 h3 => by
      rw [hR₃, movedR, Function.update_of_ne h1, Function.update_of_ne h2, hR₂, movedR,
        Function.update_of_ne h2, Function.update_of_ne h3]
  have h3io : R₃ (reg .io) = W fw := by
    rw [hR₃, movedR, Function.update_self, h2t, List.map_id, List.reverse_reverse, hR₂, movedR,
      Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp)),
      hf₁ _ (by simp) (by simp), hio, List.append_nil]
  have h3fw : R₃ (reg (.wire fw)) = [] := by
    rw [hR₃, movedR, Function.update_of_ne (reg_ne (by simp)),
      Function.update_of_ne (reg_ne (by simp)),
      hR₂, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self]
  have h3t : R₃ (reg (.wtmp fw)) = [] := by
    rw [hR₃, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self]
  have h3w : ∀ x, R₃ (reg (.wire x)) = [] := by
    intro x
    by_cases hx : x = fw
    · subst hx; exact h3fw
    rw [h3 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp [hx])), hw₁ x (hwo x hx)]
  have hf₃ : ∀ x : LReg BReg, x ≠ .park → (∀ y, x ≠ .wire y) → x ≠ .io → x ≠ .wtmp fw →
      R₃ (reg x) = S.R (reg x) := fun x h1 h2 h3' h4 =>
    (h3 _ (reg_ne h3') (reg_ne h4) (reg_ne (h2 fw))).trans (hf₁ x h1 h2)
  -- the call
  obtain ⟨v₄, c₄, hu₄, hc₄, he₄⟩ := callCore_exec body ds G F cp hfit hcall (B fw) v₃
    { S with R := R₃ } hL
    (hpar.congr fun x hx => hf₃ x (by
        simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      (parRegs_ne hx).2.1 (parRegs_ne hx).1 (by
        simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    (fun x hx => by
      dsimp only
      by_cases hxw : ∃ y, x = .wire y
      · obtain ⟨y, rfl⟩ := hxw; rw [h3w]; rfl
      push Not at hxw
      by_cases hxp : x = .park
      · subst hxp; exact trivial
      by_cases hxi : x = .io
      · subst hxi; exact trivial
      by_cases hxt : x = .wtmp fw
      · subst hxt; rw [h3t]; rfl
      rw [hf₃ x hxp hxw hxi hxt]
      exact hrest x (by rintro (⟨y, hy⟩ | hy); exacts [hxw y hy, hx hy]))
    (by dsimp only; rw [hf₃ _ (by simp) (by simp) (by simp) (by simp), hTc])
    (by dsimp only; rw [h3io])
  set R₄ := Function.update R₃ (reg .io) Y with hR₄
  -- `io` back onto `fw`, with the length counter
  obtain ⟨v₅, hu₅, he₅⟩ := ucopy_exec body (a := reg .io) (b := reg .lenctr) (t := reg (.sc 1))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄ { S with R := R₄ }
    (by dsimp only; rw [hR₄, Function.update_of_ne (reg_ne (by simp)),
      hf₃ _ (by simp) (by simp) (by simp) (by simp)]; exact hrest (.sc 1) (by simp))
  set R₅ := Function.update R₄ (reg .lenctr)
    (List.replicate (R₄ (reg .io)).length tick ++ R₄ (reg .lenctr)) with hR₅
  obtain ⟨v₆, hu₆, he₆⟩ := moveR_exec body (reg .io) (reg (.wtmp fw)) (reg_ne (by simp)) id
    v₅ { S with R := R₅ }
  set R₆ := movedR R₅ (reg .io) (reg (.wtmp fw)) id (R₅ (reg .io)) with hR₆
  obtain ⟨v₇, hu₇, he₇⟩ := moveR_exec body (reg (.wtmp fw)) (reg (.wire fw)) (reg_ne (by simp)) id
    v₆ { S with R := R₆ }
  set R₇ := movedR R₆ (reg (.wtmp fw)) (reg (.wire fw)) id (R₆ (reg (.wtmp fw))) with hR₇
  have h4io : R₄ (reg .io) = Y := by rw [hR₄, Function.update_self]
  have h5io : R₅ (reg .io) = Y := by rw [hR₅, Function.update_of_ne (reg_ne (by simp)), h4io]
  have h5l : R₅ (reg .lenctr) = List.replicate N tick := by
    rw [hR₅, Function.update_self, h4io, hYN, hR₄, Function.update_of_ne (reg_ne (by simp)),
      hf₃ _ (by simp) (by simp) (by simp) (by simp), hrest .lenctr (by simp), List.append_nil]
  have h5 : ∀ k, k ≠ reg .io → k ≠ reg .lenctr → R₅ k = R₃ k := fun k h1 h2 => by
    rw [hR₅, Function.update_of_ne h2, hR₄, Function.update_of_ne h1]
  have h6t : R₆ (reg (.wtmp fw)) = Y.reverse := by
    rw [hR₆, movedR, Function.update_self, h5io, List.map_id,
      h5 _ (reg_ne (by simp)) (reg_ne (by simp)), h3t, List.append_nil]
  have h7 : ∀ k, k ≠ reg .io → k ≠ reg (.wtmp fw) → k ≠ reg (.wire fw) → k ≠ reg .lenctr →
      R₇ k = R₃ k := fun k h1 h2 h3' h4 => by
    rw [hR₇, movedR, Function.update_of_ne h3', Function.update_of_ne h2, hR₆, movedR,
      Function.update_of_ne h2, Function.update_of_ne h1, h5 k h1 h4]
  have h7fw : R₇ (reg (.wire fw)) = Y := by
    rw [hR₇, movedR, Function.update_self, h6t, List.map_id, List.reverse_reverse, hR₆, movedR,
      Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp)),
      h5 _ (reg_ne (by simp)) (reg_ne (by simp)), h3fw, List.append_nil]
  have h7io : R₇ (reg .io) = [] := by
    rw [hR₇, movedR, Function.update_of_ne (reg_ne (by simp)),
      Function.update_of_ne (reg_ne (by simp)),
      hR₆, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self]
  have h7t : R₇ (reg (.wtmp fw)) = [] := by
    rw [hR₇, movedR, Function.update_of_ne (reg_ne (by simp)), Function.update_self]
  have h7l : R₇ (reg .lenctr) = List.replicate N tick := by
    rw [hR₇, movedR, Function.update_of_ne (reg_ne (by simp)),
      Function.update_of_ne (reg_ne (by simp)), hR₆, movedR,
      Function.update_of_ne (reg_ne (by simp)), Function.update_of_ne (reg_ne (by simp)), h5l]
  -- unpark
  obtain ⟨v₈, R₈, hu₈, he₈, hp₈, hw₈, ho₈⟩ := unparkW_exec body W N hWN (otherW fw).reverse
    (List.nodup_reverse.2 (nodup_otherW fw)) v₇ { S with R := R₇ } (S.R (reg .park))
    (by dsimp only; rw [h7l, List.length_replicate])
    (by dsimp only; rw [h7 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)), hf₃ _ (by simp) (by simp) (by simp) (by simp)]
        exact hrest (.sc 1) (by simp))
    (by dsimp only; rw [h7 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)), h3 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)), hp₁])
    (fun x hx => by
      have hx' : x ≠ fw := mem_otherW.1 (List.mem_reverse.1 hx)
      dsimp only
      rw [h7 _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp [hx'])) (reg_ne (by simp)),
        h3w])
  obtain ⟨v₉, hu₉, he₉⟩ := uclear_exec body (reg .lenctr) v₈ { S with R := R₈ }
  have ho₈' : ∀ k, k ≠ reg .park → (∀ x ∈ (otherW fw).reverse, k ≠ reg (.wire x)) →
      R₈ k = R₇ k := ho₈
  have hlen8 : (R₈ (reg .lenctr)).length = N := by
    rw [ho₈' _ (reg_ne (by simp)) (fun x _ => reg_ne (by simp)), h7l, List.length_replicate]
  refine ⟨v₉, _, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ (Exec.seq he₇ (Exec.seq he₈ he₉)))))))) rfl ?_⟩
  · have hsum : ((otherW fw).map fun x => 2 * (W x).length + 2).sum ≤ NB * (2 * N + 2) := by
      rw [List.map_congr_left (g := fun _ => 2 * N + 2) (fun x _ => by rw [hWN])]
      simp only [List.map_const', List.sum_replicate, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (length_otherW_le fw)
    have hlo : (otherW fw).reverse.length * (4 * N + 5) ≤ NB * (4 * N + 5) := by
      rw [List.length_reverse]; exact Nat.mul_le_mul_right _ (length_otherW_le fw)
    dsimp only
    rw [h1fw, hWN, h2t, List.length_reverse, hWN, h4io, hYN, h5io, hYN, h6t, List.length_reverse,
      hYN, hlen8]
    unfold childCost
    omega
  · congr 2
    funext k
    dsimp only
    by_cases hl : k = reg .lenctr
    · subst hl; rw [Function.update_self, Function.update_of_ne (reg_ne (by simp)),
        hrest .lenctr (by simp)]
    rw [Function.update_of_ne hl]
    by_cases hp : k = reg .park
    · subst hp; rw [hp₈, Function.update_of_ne (reg_ne (by simp))]
    by_cases hwk : ∃ x, k = reg (.wire x)
    · obtain ⟨x, rfl⟩ := hwk
      by_cases hx : x = fw
      · subst hx
        rw [ho₈' _ hp (fun y hy => reg_ne (by
          simp only [ne_eq, LReg.wire.injEq]; rintro rfl; exact hfwo (List.mem_reverse.1 hy))),
          h7fw, Function.update_self]
      · rw [hw₈ x (List.mem_reverse.2 (hwo x hx)), Function.update_of_ne (reg_ne (by simp [hx]))]
        exact (hB x).symm
    push Not at hwk
    rw [ho₈' k hp (fun x _ => hwk x), Function.update_of_ne (hwk fw)]
    by_cases hi : k = reg .io
    · subst hi; rw [h7io, hio]
    by_cases ht : k = reg (.wtmp fw)
    · subst ht; rw [h7t, hrest (.wtmp fw) (by simp)]
    rw [h7 k hi ht (hwk fw) hl]
    obtain ⟨x, rfl⟩ := (regEquiv BReg).surjective k
    exact hf₃ x (fun h => hp (by rw [h]; rfl)) (fun y h => hwk y (by rw [h]; rfl))
      (fun h => hi (by rw [h]; rfl)) (fun h => ht (by rw [h]; rfl))

end Call

/-! ### Factor programs on empty left stacks -/

section Spec

variable {BReg : Type} [Fintype BReg] {Q A : ℕ} {U P : Type}

/-- **Factor programs on empty left stacks.** `FactorSpec` for the register files whose left
stacks are all empty: from the node-internal state with every left stack empty and every wire `x`
holding `encZ A w (B x)`, `prog` ends with every wire `x` holding
`encZ A w (execM e child Tc (.factor fw g) B x)`, every other register and `user` as before,
within `cf` steps. -/
def FactorSpecL (body : P → Pr P (nT BReg) Q A U) (prog : Pr P (nT BReg) Q A U)
    (bcRest : BReg → List (Fin (A + 4)) → Prop) (j u K ρ a₀ L rows n r w : ℕ) {R k : ℕ}
    (e : Fin (m * k) → Fin n)
    (child : Fin m → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n) (Tc : ℕ) (fw : NWire)
    (g : ZMod 4 × BinaryWalsh.Address m) (cf : ℕ) : Prop :=
  ∀ (B : NWire → ZArr (Fin R × Fin r) n) (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A),
    (∀ y, S.L y = []) → NodeRegs bcRest S.R j u K ρ a₀ L rows n r w Tc →
    (∀ x, S.R (reg (.wire x)) = encZ A w (B x)) →
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ) (R' : Fin (nT BReg) → List (Fin (A + 4))),
      v'.user = v.user ∧ c ≤ cf ∧ Exec body prog (mk v S) c (mk v' { S with R := R' }) ∧
      (∀ x, R' (reg (.wire x)) = encZ A w (execM e child Tc (.factor fw g) B x)) ∧
      ∀ i, (∀ x, i ≠ reg (.wire x)) → R' i = S.R i

/-- `FactorSpecL` is monotone in the step bound. -/
lemma FactorSpecL.mono {body : P → Pr P (nT BReg) Q A U} {prog : Pr P (nT BReg) Q A U}
    {bcRest : BReg → List (Fin (A + 4)) → Prop} {j u K ρ a₀ L rows n r w : ℕ} {R k : ℕ}
    {e : Fin (m * k) → Fin n} {child : Fin m → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n}
    {Tc : ℕ} {fw : NWire} {g : ZMod 4 × BinaryWalsh.Address m} {cf cf' : ℕ}
    (h : FactorSpecL body prog bcRest j u K ρ a₀ L rows n r w e child Tc fw g cf)
    (hc : cf ≤ cf') : FactorSpecL body prog bcRest j u K ρ a₀ L rows n r w e child Tc fw g cf' :=
  fun B v S hL hN hB => by
    obtain ⟨v', c, R', hu, hc', he, hw, hfr⟩ := h B v S hL hN hB
    exact ⟨v', c, R', hu, hc'.trans hc, he, hw, hfr⟩

end Spec

/-! ### The basis change on a wire -/

section BasisW

variable {Q Ka : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q (prime + Ka) U)

/-- The rest state of the basis-change registers: empty. -/
def bcEmpty {A : ℕ} : SXReg → List (Fin (A + 4)) → Prop := fun _ l => l = []

/-- The basis-change registers `bc x` of the layer machine. -/
noncomputable def bcReg (x : SXReg) : Fin (nT SXReg) := reg (.bc x)

/-- The layer-machine register of a slot-XOR parameter. -/
def sxParL : SXPar → LReg SXReg
  | .K => .K | .ρ => .ρ | .a₀ => .a₀ | .L => .L | .rows => .rows | .n => .n | .rw => .rw

/-- The host register of a slot-XOR parameter. -/
noncomputable def sxParReg (p : SXPar) : Fin (nT SXReg) := reg (sxParL p)

lemma bcReg_injective : Function.Injective bcReg := fun a b h => by
  simpa [bcReg] using h

/-- The slot-XOR registers of the layer machine. -/
lemma sxEnv_layer : SxEnv bcReg sxParReg where
  hι := bcReg_injective
  hpar := fun a b h => by
    cases a <;> cases b <;> first | rfl | (simp [sxParReg, sxParL] at h)
  hpι := fun x p => by cases p <;> simp [bcReg, sxParReg, sxParL]

/-- The basis change along `vv` at `s` on wire `x`. -/
noncomputable def basisW (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (x : NWire)
    (vv : BinaryWalsh.Address m) (s : Fin m) : Pr P (nT SXReg) Q (prime + Ka) U :=
  basisProg bcReg_injective hQ sxParReg (reg (.wire x)) (reg .st) vv s

/-- The step bound of `basisW` (`basisProg_exec`), rounded up. -/
noncomputable def basisCostN (T a₀ K ρ L R n rw k : ℕ) (vv : BinaryWalsh.Address m) (s : Fin m) :
    ℕ :=
  ⌈((basisTargets vv s).map fun j' => basisCost T (basisData a₀ K ρ L R n rw k s j')).sum + 1⌉₊

/-- **The basis change on a wire.** With every left stack and every `bc` register empty and the
parameter registers holding `K, ρ, a₀, L = K k, R, n, r w`, `basisW` takes wire `x` from the
stream of `Z` to the stream of `pullM e (basisMap vv s) Z`. -/
theorem basisW_exec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (hA : 14 ≤ prime + Ka)
    {a₀ K ρ k L R n r w : ℕ} (hρ : ρ < K) (hLK : L = K * k) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hrw : 1 ≤ r * w) (hfit : a₀ + m * L ≤ n) {e : Fin (m * k) → Fin n}
    (he : ∀ i, (e i : ℕ) = a₀ + ρ + K * i) (x : NWire) (vv : BinaryWalsh.Address m) (s : Fin m)
    (hvs : vv s = 1) (Z : ZArr (Fin R × Fin r) n) (v : HS (nT SXReg) Q (prime + Ka) U)
    (S : Stacks (nT SXReg) (prime + Ka)) (hL : ∀ y, S.L y = [])
    (hx : S.R (reg (.wire x)) = encZ (prime + Ka) w Z)
    (hK : (S.R (reg .K)).length = K) (hρr : (S.R (reg .ρ)).length = ρ)
    (ha₀ : (S.R (reg .a₀)).length = a₀) (hLr : (S.R (reg .L)).length = L)
    (hrows : (S.R (reg .rows)).length = R) (hn : (S.R (reg .n)).length = n)
    (hrwr : (S.R (reg .rw)).length = r * w) (hbc : ∀ y, S.R (reg (.bc y)) = []) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      c ≤ basisCostN (nT SXReg) a₀ K ρ L R n (r * w) k vv s ∧
      Exec body (basisW hQ x vv s) (mk v S) c (mk v' { S with
        R := Function.update S.R (reg (.wire x))
          (encZ (prime + Ka) w (pullM e (basisMap vv s) Z)) }) := by
  obtain ⟨v', c, hu, hc, hex⟩ := basisProg_exec body sxEnv_layer (src := reg (.wire x))
    (st := reg .st) (fun y => reg_ne (by simp))
    (fun p => by cases p <;> exact reg_ne (by simp [sxParL]))
    (fun y => reg_ne (by simp)) hA hQ hρ hLK hk hR hrw hfit he vv s hvs Z v S hL hx
    (fun p => by cases p <;> assumption) hbc
  refine ⟨v', c, hu, ?_, hex⟩
  exact_mod_cast hc.trans (Nat.le_ceil _)

end BasisW

/-! ### The factor program -/

section FactorProg

variable {Q Ka : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q (prime + Ka) U)

/-- All wires, once each. -/
noncomputable def allW : List NWire := Finset.univ.toList

lemma mem_allW (x : NWire) : x ∈ allW := by simp [allW]

lemma nodup_allW : allW.Nodup := Finset.nodup_toList _

lemma length_allW : allW.length = NB := by
  rw [allW, Finset.length_toList, Finset.card_univ, NB_card]

lemma bits_pos {u : ℕ} (hu : 1 ≤ u) : ∀ j, 1 ≤ bits u j
  | 0 => hu
  | j + 1 => Nat.mul_pos (by norm_num [m]) (bits_pos hu j)

lemma rowsAt_pos {R₀ : ℕ} (hR₀ : 1 ≤ R₀) : ∀ j, 1 ≤ rowsAt R₀ j
  | 0 => hR₀
  | j + 1 => Nat.mul_pos one_le_NW (rowsAt_pos hR₀ j)

lemma shiftCost_mono {F F' R n r w s : ℕ} (h : F ≤ F') :
    shiftCost F R n r w s ≤ shiftCost F' R n r w s := by
  unfold shiftCost
  have := Nat.mul_le_mul_right (R * 2 ^ n * r * (6 * w + 4 * s + 14) + 4) h
  omega

/-- A factor with a pivot as conditional conjugations around the child. -/
lemma facM_pivot {Y : Type} {n k : ℕ} (e : Fin (m * k) → Fin n)
    (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ) (g : ZMod 4 × BinaryWalsh.Address m)
    (hpiv : ∃ i, g.2 i = 1) (f : ZArr Y n) :
    facM e child Tc g f = pullM e (basisMap g.2 (Fin.find _ hpiv))
      (cconj g.1 (child (Fin.find _ hpiv)
        (cconj g.1 (pullM e (basisMap g.2 (Fin.find _ hpiv)) f)))) := by
  unfold facM cconj
  simp only [hpiv, ↓reduceDIte]
  split_ifs <;> rfl

/-- **The factor program** of `(fw, (q, v))`. Without a pivot: every wire is multiplied by
`2 ^ Tc`. With the pivot `s = Fin.find (v · = 1)`: save `rows` and `L` on `park` and set them to
the child's values (`rows / NW`, `L / m`); `basisW v s` on `fw`; conjugate unless `q = 1`; the
child call; conjugate unless `q = 1`; `basisW v s`; restore `L` and `rows`; multiply every other
wire by `2 ^ Tc`. -/
noncomputable def factorProg (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (cp : Pr P (nT SXReg) Q (prime + Ka) U) (ds : ComplexFramedExecution.Directions)
    (fw : NWire) (g : ZMod 4 × BinaryWalsh.Address m) : Pr P (nT SXReg) Q (prime + Ka) U :=
  if h : ∃ i, g.2 i = 1 then
    .seq (saveDiv NW .rows)
    (.seq (saveDiv m .L)
    (.seq (basisW hQ fw g.2 (Fin.find _ h))
    (.seq (condConj g.1 fw)
    (.seq (childCall fw (Fin.find _ h) (gateCount (program ds)) (factorCount (program ds)) cp)
    (.seq (condConj g.1 fw)
    (.seq (basisW hQ fw g.2 (Fin.find _ h))
    (.seq (restoreMul m .L)
    (.seq (restoreMul NW .rows)
      (shiftTc (otherW fw))))))))))
  else shiftTc allW

/-- The step bound of the factor program of `(fw, g)` at level `j + 1`, with `T` host registers
and child calls within `cc` steps. -/
noncomputable def factorCost (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (j u K ρ a₀ R₀ n r w : ℕ) (g : ZMod 4 × BinaryWalsh.Address m) (cc : ℕ) : ℕ :=
  if h : ∃ i, g.2 i = 1 then
    (8 * (NW * rowsAt R₀ j) + 8) + (8 * (K * bits u (j + 1)) + 8) +
      basisCostN T a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j) g.2 (Fin.find _ h) +
      (conjCost (rowsAt R₀ j) n r w + 1) +
      childCost (rowsAt R₀ j * 2 ^ n * (r * w)) (gateCount (program ds))
        (factorCount (program ds)) u j (K * bits u j) (Fin.find _ h) (expZ u ds j) cc +
      (conjCost (rowsAt R₀ j) n r w + 1) +
      basisCostN T a₀ K ρ (K * bits u j) (rowsAt R₀ j) n (r * w) (bits u j) g.2 (Fin.find _ h) +
      (6 * (K * bits u j) + 6 * (K * bits u (j + 1)) + 13) +
      (6 * rowsAt R₀ j + 6 * (NW * rowsAt R₀ j) + 13) +
      shiftCost NB (rowsAt R₀ j) n r w (expZ u ds j)
  else shiftCost NB (rowsAt R₀ j) n r w (expZ u ds j)

/-- **The factor program.** At a node of level `j + 1` (`L = K bits u (j + 1)`,
`rows = rowsAt R₀ (j + 1)`) with active bits `e i = a₀ + ρ + K i` inside the address
(`a₀ + K bits u (j + 1) ≤ n`, `ρ < K`), child exponent `expZ u ds j ≤ w`, and the child call `cp`
computing the layer at level `j` for the pivot's offset within `cc` steps (`CallSpec`), the factor
program implements the factor `(fw, g)` on empty left stacks (`FactorSpecL`) within
`factorCost … g cc` steps. -/
theorem factorProg_spec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (cp : Pr P (nT SXReg) Q (prime + Ka) U) (ds : ComplexFramedExecution.Directions)
    (hA : 14 ≤ prime + Ka) {R₀ j u K ρ a₀ n r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hρ : ρ < K)
    (hu : 1 ≤ u) (hR₀ : 1 ≤ R₀) (hfit : ∀ i < bits u (j + 1), a₀ + ρ + K * i < n)
    (hfitL : a₀ + K * bits u (j + 1) ≤ n) (hTw : expZ u ds j ≤ w) (fw : NWire)
    (g : ZMod 4 × BinaryWalsh.Address m) (cc : ℕ)
    (hcall : ∀ (hs : ∃ i, g.2 i = 1)
      (hfit' : ∀ i < bits u j, a₀ + (Fin.find _ hs : ℕ) * (K * bits u j) + ρ + K * i < n),
      CallSpec body cp bcEmpty ds R₀ j u K ρ (a₀ + (Fin.find _ hs : ℕ) * (K * bits u j))
        (K * bits u j) n r w hfit' cc) :
    FactorSpecL body (factorProg hQ cp ds fw g) bcEmpty j u K ρ a₀ (K * bits u (j + 1))
      (rowsAt R₀ (j + 1)) n r w (k := bits u j) (actMap a₀ ρ K (bits u (j + 1)) n hfit)
      (fun s => layerZ u ds R₀ j fun c => actMap a₀ ρ K (bits u (j + 1)) n hfit (bitIdx s c))
      (expZ u ds j) fw g (factorCost (nT SXReg) ds j u K ρ a₀ R₀ n r w g cc) := by
  intro B v S hL hN hB
  set Lc := K * bits u j with hLc
  set Tc := expZ u ds j with hTcd
  set e := actMap a₀ ρ K (bits u (j + 1)) n hfit with he_def
  have hs : ∀ i, S.R (reg (.sc i)) = [] := fun i => hN.rest (.sc i) (by simp)
  have hrs : ∀ x : LReg SXReg, (∀ y, x ≠ .wire y) → x ≠ .Tc →
      restSpec bcEmpty n r w x (S.R (reg x)) := fun x h1 h2 =>
    hN.rest x (by rintro (⟨y, hy⟩ | hy); exacts [h1 y hy, h2 hy])
  have hTcS : (S.R (reg .Tc)).length = Tc := hN.tc
  have hwS : (S.R (reg .w)).length = w := hN.par .w
  by_cases hpiv : ∃ i, g.2 i = 1
  swap
  · -- no pivot: every wire is multiplied by `2 ^ Tc`
    obtain ⟨v₁, c₁, R₁, hu₁, hc₁, he₁, hw₁, ho₁⟩ := shiftTc_exec body hw hTw allW nodup_allW B v S
      hwS hTcS (hs 0) (hs 1) (hrs .tS (by simp) (by simp)) (hrs .tR (by simp) (by simp))
      (fun x _ => hrs (.wtmp x) (by simp) (by simp)) (fun x _ => hB x)
    refine ⟨v₁, c₁, R₁, hu₁, ?_, ?_, ?_, ?_⟩
    · simp only [factorCost, hpiv, ↓reduceDIte]; rw [← length_allW]; exact hc₁
    · simpa only [factorProg, hpiv, ↓reduceDIte] using he₁
    · intro x
      rw [hw₁ x (mem_allW x)]
      congr 1
      by_cases hx : x = fw
      · subst hx; simp only [execM, ↓reduceIte, facM, hpiv, ↓reduceDIte]
      · simp only [execM, hx, ↓reduceIte]
    · intro i hi
      exact ho₁ i (fun x _ => hi x)
  -- the pivot
  set s := Fin.find _ hpiv with hsdef
  have hvs : g.2 s = 1 := Fin.find_spec hpiv
  have hk1 : 1 ≤ bits u j := bits_pos hu j
  have hRw1 : 1 ≤ (rowsAt R₀ j) := rowsAt_pos hR₀ j
  have hrw : 1 ≤ r * w := Nat.mul_pos hr hw
  have hm1 : 1 ≤ m := by norm_num [m]
  have hL₁ : K * bits u (j + 1) = m * Lc := by
    rw [hLc, show bits u (j + 1) = m * bits u j from rfl]; ring
  have hfitm : a₀ + m * Lc ≤ n := by rw [← hL₁]; exact hfitL
  have he : ∀ i : Fin (m * bits u j), (e i : ℕ) = a₀ + ρ + K * i := fun i => rfl
  have hfit' : ∀ i < bits u j, a₀ + (s : ℕ) * Lc + ρ + K * i < n := by
    intro i hi
    have hs' := s.2
    have h1 : i + bits u j * s < bits u (j + 1) := by
      show i + bits u j * s < m * bits u j
      nlinarith
    have := hfit _ h1
    have h2 : K * (i + bits u j * s) = K * i + s * Lc := by rw [hLc]; ring
    omega
  have heS : (fun c => e (bitIdx s c)) = actMap (a₀ + (s : ℕ) * Lc) ρ K (bits u j) n hfit' := by
    funext c
    apply Fin.ext
    simp only [he_def, actMap, bitIdx, finProdFinEquiv_apply_val, hLc]
    ring
  set rows₀ := S.R (reg .rows) with hrows₀
  set L₀ := S.R (reg .L) with hL₀
  set park₀ := S.R (reg .park) with hpark₀
  have hrows₀l : rows₀.length = NW * (rowsAt R₀ j) := hN.par .rows
  have hL₀l : L₀.length = m * Lc := (hN.par .L).trans hL₁
  -- save `rows` and `L`
  obtain ⟨v₁, c₁, hu₁, hc₁, he₁⟩ := saveDiv_exec body one_le_NW (X := .rows) (by simp) (by simp)
    (by simp) v S (hs 0) (hs 1)
  set R₁ := Function.update (Function.update S.R (reg .park) (rows₀.reverse ++ park₀))
    (reg .rows) (List.replicate (rows₀.length / NW) tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, he₂⟩ := saveDiv_exec body hm1 (X := .L) (by simp) (by simp)
    (by simp) v₁ { S with R := R₁ } (by dsimp only; rw [hR₁]; fupd; exact hs 0)
    (by dsimp only; rw [hR₁]; fupd; exact hs 1)
  dsimp only at hc₂ he₂
  have h1L : R₁ (reg .L) = L₀ := by rw [hR₁]; fupd
  have h1p : R₁ (reg .park) = rows₀.reverse ++ park₀ := by rw [hR₁]; fupd
  rw [h1L, h1p] at he₂
  rw [h1L] at hc₂
  set R₂ := Function.update (Function.update R₁ (reg .park) (L₀.reverse ++
    (rows₀.reverse ++ park₀))) (reg .L) (List.replicate (L₀.length / m) tick) with hR₂
  have h2o : ∀ x : LReg SXReg, x ≠ .park → x ≠ .L → x ≠ .rows → R₂ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3
    rw [hR₂, Function.update_of_ne (reg_ne h2), Function.update_of_ne (reg_ne h1), hR₁,
      Function.update_of_ne (reg_ne h3), Function.update_of_ne (reg_ne h1)]
  have h2L : R₂ (reg .L) = List.replicate Lc tick := by
    rw [hR₂, Function.update_self, hL₀l, Nat.mul_div_cancel_left _ (by norm_num [m])]
  have h2r : R₂ (reg .rows) = List.replicate (rowsAt R₀ j) tick := by
    rw [hR₂]; fupd; rw [hR₁]; fupd
    rw [hrows₀l, Nat.mul_div_cancel_left _ (Nat.pos_of_neZero NW)]
  have h2p : R₂ (reg .park) = L₀.reverse ++ (rows₀.reverse ++ park₀) := by rw [hR₂]; fupd
  -- the first basis change
  have hpar2 : ∀ x : LReg SXReg, x ∈ [.K, .ρ, .a₀, .n, .rw, .w, .u, .lev] →
      R₂ (reg x) = S.R (reg x) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply h2o <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨v₃, c₃, hu₃, hc₃, he₃⟩ := basisW_exec body hQ hA (k := bits u j) (R := (rowsAt R₀ j))
    (e := e)
    hρ rfl hk1 hRw1 hrw hfitm he fw g.2 s hvs (B fw) v₂ { S with R := R₂ } hL
    (by dsimp only; rw [h2o _ (by simp) (by simp) (by simp)]; exact hB fw)
    (by dsimp only; rw [hpar2 .K (by simp)]; exact hN.par .K)
    (by dsimp only; rw [hpar2 .ρ (by simp)]; exact hN.par .ρ)
    (by dsimp only; rw [hpar2 .a₀ (by simp)]; exact hN.par .a₀)
    (by dsimp only; rw [h2L, List.length_replicate])
    (by dsimp only; rw [h2r, List.length_replicate])
    (by dsimp only; rw [hpar2 .n (by simp)]; exact hN.par .n)
    (by dsimp only; rw [hpar2 .rw (by simp)]; exact hN.par .rw)
    (fun y => by
      dsimp only; rw [h2o _ (by simp) (by simp) (by simp)]; exact hrs (.bc y) (by simp) (by simp))
  set Z₁ := pullM e (basisMap g.2 s) (B fw) with hZ₁
  set R₃ := Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₁) with hR₃
  have h3o : ∀ x : LReg SXReg, x ≠ .park → x ≠ .L → x ≠ .rows → x ≠ .wire fw →
      R₃ (reg x) = S.R (reg x) := fun x h1 h2 h3 h4 => by
    rw [hR₃, Function.update_of_ne (reg_ne h4), h2o x h1 h2 h3]
  -- the first conjugation
  obtain ⟨v₄, c₄, hu₄, hc₄, he₄⟩ := condConj_exec body (by omega) hw g.1 fw Z₁ v₃
    { S with R := R₃ }
    (by dsimp only; rw [h3o _ (by simp) (by simp) (by simp) (by simp)]
        exact hwS ▸ hrs .ctr (by simp) (by simp))
    (by dsimp only
        rw [h3o _ (by simp) (by simp) (by simp) (by simp)]
        exact hrs .tmp (by simp) (by simp))
    (by dsimp only
        rw [h3o _ (by simp) (by simp) (by simp) (by simp)]
        exact hrs (.wtmp fw) (by simp) (by simp))
    (by dsimp only; rw [hR₃, Function.update_self])
  set Z₂ := cconj g.1 Z₁ with hZ₂
  set R₄ := Function.update R₃ (reg (.wire fw)) (encZ (prime + Ka) w Z₂) with hR₄
  have hR₄' : R₄ = Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₂) := by
    rw [hR₄, hR₃, Function.update_idem]
  have h4o : ∀ x : LReg SXReg, x ≠ .park → x ≠ .L → x ≠ .rows → (∀ y, x ≠ .wire y) →
      R₄ (reg x) = S.R (reg x) := fun x h1 h2 h3 h4 => by
    rw [hR₄', Function.update_of_ne (reg_ne (h4 fw)), h2o x h1 h2 h3]
  -- the child call
  set B' := Function.update B fw Z₂ with hB'
  set G := gateCount (program ds) with hG
  set F := factorCount (program ds) with hF
  obtain ⟨v₅, c₅, hu₅, hc₅, he₅⟩ := childCall_exec body ds G F cp hfit' (hcall hpiv hfit') fw B'
    v₄ { S with R := R₄ } hL
    (by
      intro x
      by_cases hxL : x = .L
      · subst hxL; show (R₄ (reg .L)).length = Lc
        rw [hR₄', Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate]
      by_cases hxr : x = .rows
      · subst hxr; show (R₄ (reg .rows)).length = (rowsAt R₀ j)
        rw [hR₄', Function.update_of_ne (reg_ne (by simp)), h2r, List.length_replicate]
      by_cases hxp : x = .park
      · subst hxp; exact trivial
      by_cases hxw : ∃ y, x = .wire y
      · obtain ⟨y, rfl⟩ := hxw; exact trivial
      push Not at hxw
      have h := hN.par x
      dsimp only
      rw [← h4o x hxp hxL hxr hxw] at h
      cases x <;> first | exact trivial | exact absurd rfl hxL | exact absurd rfl hxr | exact h)
    (by
      intro x hx
      have hxw : ∀ y, x ≠ .wire y := fun y h => hx (Or.inl ⟨y, h⟩)
      have hxT : x ≠ .Tc := fun h => hx (Or.inr h)
      by_cases hxL : x = .L
      · subst hxL; exact trivial
      by_cases hxr : x = .rows
      · subst hxr; exact trivial
      by_cases hxp : x = .park
      · subst hxp; exact trivial
      dsimp only
      rw [h4o x hxp hxL hxr hxw]
      exact hrs x hxw hxT)
    (by dsimp only; rw [h4o _ (by simp) (by simp) (by simp) (by simp)]; exact hN.io)
    (by dsimp only; rw [h4o _ (by simp) (by simp) (by simp) (by simp), hTcS, hTcd,
          expZ_eq_expSeq])
    (fun x => by
      dsimp only
      by_cases hx : x = fw
      · subst hx; rw [hR₄', Function.update_self, hB', Function.update_self]
      · rw [hR₄', Function.update_of_ne (reg_ne (by simp [hx])), h2o _ (by simp) (by simp)
          (by simp), hB x, hB', Function.update_of_ne hx])
  dsimp only at he₅ hc₅
  have hB'fw : B' fw = Z₂ := by rw [hB', Function.update_self]
  rw [hB'fw] at he₅
  set Z₃ := layerZ u ds R₀ j (actMap (a₀ + (s : ℕ) * Lc) ρ K (bits u j) n hfit') Z₂ with hZ₃
  set R₅ := Function.update R₄ (reg (.wire fw)) (encZ (prime + Ka) w Z₃) with hR₅
  have hR₅' : R₅ = Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₃) := by
    rw [hR₅, hR₄', Function.update_idem]
  -- the second conjugation
  obtain ⟨v₆, c₆, hu₆, hc₆, he₆⟩ := condConj_exec body (by omega) hw g.1 fw Z₃ v₅
    { S with R := R₅ }
    (by dsimp only
        rw [hR₅', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hwS ▸ hrs .ctr (by simp) (by simp))
    (by dsimp only
        rw [hR₅', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hrs .tmp (by simp) (by simp))
    (by dsimp only
        rw [hR₅', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hrs (.wtmp fw) (by simp) (by simp))
    (by dsimp only; rw [hR₅', Function.update_self])
  set Z₄ := cconj g.1 Z₃ with hZ₄
  set R₆ := Function.update R₅ (reg (.wire fw)) (encZ (prime + Ka) w Z₄) with hR₆
  have hR₆' : R₆ = Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₄) := by
    rw [hR₆, hR₅', Function.update_idem]
  -- the second basis change
  obtain ⟨v₇, c₇, hu₇, hc₇, he₇⟩ := basisW_exec body hQ hA (k := bits u j) (R := (rowsAt R₀ j))
    (e := e)
    hρ rfl hk1 hRw1 hrw hfitm he fw g.2 s hvs Z₄ v₆ { S with R := R₆ } hL
    (by dsimp only; rw [hR₆', Function.update_self])
    (by dsimp only
        rw [hR₆', Function.update_of_ne (reg_ne (by simp)), hpar2 .K (by simp)]
        exact hN.par .K)
    (by dsimp only
        rw [hR₆', Function.update_of_ne (reg_ne (by simp)), hpar2 .ρ (by simp)]
        exact hN.par .ρ)
    (by dsimp only
        rw [hR₆', Function.update_of_ne (reg_ne (by simp)), hpar2 .a₀ (by simp)]
        exact hN.par .a₀)
    (by dsimp only; rw [hR₆', Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate])
    (by dsimp only; rw [hR₆', Function.update_of_ne (reg_ne (by simp)), h2r, List.length_replicate])
    (by dsimp only
        rw [hR₆', Function.update_of_ne (reg_ne (by simp)), hpar2 .n (by simp)]
        exact hN.par .n)
    (by dsimp only
        rw [hR₆', Function.update_of_ne (reg_ne (by simp)), hpar2 .rw (by simp)]
        exact hN.par .rw)
    (fun y => by
      dsimp only; rw [hR₆', Function.update_of_ne (reg_ne (by simp)),
        h2o _ (by simp) (by simp) (by simp)]; exact hrs (.bc y) (by simp) (by simp))
  set Z₅ := pullM e (basisMap g.2 s) Z₄ with hZ₅
  set R₇ := Function.update R₆ (reg (.wire fw)) (encZ (prime + Ka) w Z₅) with hR₇
  have hR₇' : R₇ = Function.update R₂ (reg (.wire fw)) (encZ (prime + Ka) w Z₅) := by
    rw [hR₇, hR₆', Function.update_idem]
  -- restore `L` and `rows`
  obtain ⟨v₈, c₈, hu₈, hc₈, he₈⟩ := restoreMul_exec body (c := m) (X := .L) (by simp) (by simp)
    (by simp) L₀.reverse (rows₀.reverse ++ park₀) v₇ { S with R := R₇ }
    (by dsimp only
        rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hrs .lenctr (by simp) (by simp))
    (by dsimp only
        rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2o _ (by simp) (by simp) (by simp)]
        exact hs 1)
    (by dsimp only; rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate,
          List.length_reverse, hL₀l])
    (by dsimp only; rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2p])
  dsimp only at he₈ hc₈
  set R₈ := Function.update (Function.update R₇ (reg .park) (rows₀.reverse ++ park₀)) (reg .L)
    L₀.reverse.reverse with hR₈
  obtain ⟨v₉, c₉, hu₉, hc₉, he₉⟩ := restoreMul_exec body (c := NW) (X := .rows) (by simp)
    (by simp) (by simp) rows₀.reverse park₀ v₈ { S with R := R₈ }
    (by dsimp only
        rw [hR₈]
        fupd
        rw [hR₇']
        fupd
        rw [h2o _ (by simp) (by simp) (by simp)]
        exact hrs .lenctr (by simp) (by simp))
    (by dsimp only
        rw [hR₈]
        fupd
        rw [hR₇']
        fupd
        rw [h2o _ (by simp) (by simp) (by simp)]
        exact hs 1)
    (by dsimp only; rw [hR₈]; fupd; rw [hR₇']; fupd; rw [h2r, List.length_replicate,
          List.length_reverse, hrows₀l])
    (by dsimp only; rw [hR₈]; fupd)
  dsimp only at he₉ hc₉
  set R₉ := Function.update (Function.update R₈ (reg .park) park₀) (reg .rows)
    rows₀.reverse.reverse with hR₉
  have hR₉' : R₉ = Function.update S.R (reg (.wire fw)) (encZ (prime + Ka) w Z₅) := by
    funext k
    by_cases h1 : k = reg .rows
    · subst h1; rw [hR₉]; fupd; rw [List.reverse_reverse]
    by_cases h2 : k = reg .park
    · subst h2; rw [hR₉]; fupd
    by_cases h3 : k = reg .L
    · subst h3; rw [hR₉]; fupd; rw [hR₈]; fupd; rw [List.reverse_reverse]
    rw [hR₉, Function.update_of_ne h1, Function.update_of_ne h2, hR₈, Function.update_of_ne h3,
      Function.update_of_ne h2, hR₇', Function.update_apply, Function.update_apply]
    split_ifs with h4
    · rfl
    · obtain ⟨x, rfl⟩ := (regEquiv SXReg).surjective k
      exact h2o x (fun h => h2 (by rw [h]; rfl)) (fun h => h3 (by rw [h]; rfl))
        (fun h => h1 (by rw [h]; rfl))
  -- the other wires
  obtain ⟨v₁₀, c₁₀, R₁₀, hu₁₀, hc₁₀, he₁₀, hw₁₀, ho₁₀⟩ := shiftTc_exec body hw hTw (otherW fw)
    (nodup_otherW fw) B v₉ { S with R := R₉ }
    (by dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]; exact hwS)
    (by dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]; exact hTcS)
    (by dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]; exact hs 0)
    (by dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]; exact hs 1)
    (by dsimp only
        rw [hR₉', Function.update_of_ne (reg_ne (by simp))]
        exact hrs .tS (by simp) (by simp))
    (by dsimp only
        rw [hR₉', Function.update_of_ne (reg_ne (by simp))]
        exact hrs .tR (by simp) (by simp))
    (fun x _ => by
      dsimp only; rw [hR₉', Function.update_of_ne (reg_ne (by simp))]
      exact hrs (.wtmp x) (by simp) (by simp))
    (fun x hx => by
      dsimp only
      rw [hR₉', Function.update_of_ne (reg_ne (by simp [mem_otherW.1 hx])), hB x])
  have ho₁₀' : ∀ k, (∀ x ∈ otherW fw, k ≠ reg (.wire x)) → R₁₀ k = R₉ k := ho₁₀
  have he := Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
    (Exec.seq he₆ (Exec.seq he₇ (Exec.seq he₈ (Exec.seq he₉ he₁₀))))))))
  have he' : Exec body (factorProg hQ cp ds fw g) (mk v S)
      (c₁ + (c₂ + (c₃ + (c₄ + (c₅ + (c₆ + (c₇ + (c₈ + (c₉ + c₁₀)))))))))
      (mk v₁₀ { S with R := R₁₀ }) := by
    simpa only [factorProg, hpiv, ↓reduceDIte] using he
  refine ⟨v₁₀, _, R₁₀, by rw [hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, he', ?_, ?_⟩
  · -- the step bound
    have hc₁₀' := hc₁₀.trans (shiftCost_mono (length_otherW_le fw))
    have hc₅' : c₅ ≤ childCost ((rowsAt R₀ j) * 2 ^ n * (r * w)) G F u j Lc s Tc cc := by
      rw [hTcd, expZ_eq_expSeq]; exact hc₅
    rw [hrows₀l] at hc₁
    rw [hR₇', Function.update_of_ne (reg_ne (by simp)), h2L, List.length_replicate,
      List.length_reverse, hL₀l] at hc₈
    rw [hR₈] at hc₉
    simp only [Function.update_apply, reg_inj, reduceCtorEq, ↓reduceIte, hR₇'] at hc₉
    rw [h2r, List.length_replicate, List.length_reverse, hrows₀l] at hc₉
    have hfc : factorCost (nT SXReg) ds j u K ρ a₀ R₀ n r w g cc =
        (8 * (NW * (rowsAt R₀ j)) + 8) + (8 * (K * bits u (j + 1)) + 8) +
        basisCostN (nT SXReg) a₀ K ρ Lc (rowsAt R₀ j) n (r * w) (bits u j) g.2 s +
        (conjCost (rowsAt R₀ j) n r w + 1) +
        childCost ((rowsAt R₀ j) * 2 ^ n * (r * w)) G F u j Lc s Tc cc +
        (conjCost (rowsAt R₀ j) n r w + 1) +
        basisCostN (nT SXReg) a₀ K ρ Lc (rowsAt R₀ j) n (r * w) (bits u j) g.2 s +
        (6 * Lc + 6 * (K * bits u (j + 1)) + 13) +
        (6 * (rowsAt R₀ j) + 6 * (NW * (rowsAt R₀ j)) + 13) +
        shiftCost NB (rowsAt R₀ j) n r w Tc := by
      simp only [factorCost, hpiv, ↓reduceDIte]; rfl
    rw [hfc, hL₁]
    rw [hL₀l] at hc₂
    rw [← hLc] at hc₃ hc₇
    omega
  · -- the wires
    intro x
    by_cases hx : x = fw
    · have hfw : ∀ y ∈ otherW fw, reg (BReg := SXReg) (.wire x) ≠ reg (.wire y) := by
        intro y hy h
        rw [reg_inj, LReg.wire.injEq] at h
        exact mem_otherW.1 hy (h ▸ hx)
      rw [ho₁₀' _ hfw, hR₉', hx, Function.update_self]
      apply congrArg (encZ (prime + Ka) w)
      simp only [execM, ↓reduceIte]
      rw [facM_pivot e _ Tc g hpiv, ← hsdef]
      simp only [hZ₅, hZ₄, hZ₃, hZ₂, hZ₁, heS]
    · rw [hw₁₀ x (mem_otherW.2 hx)]
      apply congrArg (encZ (prime + Ka) w)
      simp only [execM, hx, ↓reduceIte]
  · intro i hi
    rw [ho₁₀' i (fun x _ => hi x), hR₉', Function.update_of_ne (hi fw)]

end FactorProg

end IntegerMultBounds.MathlibTM2.LayerMachine
