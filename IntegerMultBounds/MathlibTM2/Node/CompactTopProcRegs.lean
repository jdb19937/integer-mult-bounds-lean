module
public import IntegerMultBounds.MathlibTM2.Node.Regs
public import IntegerMultBounds.MathlibTM2.Node.TopRec
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init


/-! Top-stage register contracts for arbitrary basis banks and persistent rest
predicates. The legacy SXReg top machine remains unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {BReg : Type} [Fintype BReg] {A : ℕ}
variable {bc : BReg → List (Fin (A+4)) → Prop}

/-- The registers of the host machine between its stages: every register at rest for `N`
address bits, `r` coefficients and words of `w` symbols; the per-call parameters `lev`, `u`,
`a₀`, `L`, `rows` empty; `n`, `w`, `rw`, `K`, `ρ` holding `N`, `w`, `r w`, `K`, `ρ` symbols. -/
structure CompactTopRegs (bc : BReg → List (Fin (A+4)) → Prop) (Rg : Fin (nT BReg) → List (Fin (A + 4))) (N r w K ρ : ℕ) : Prop where
  rest : Rest bc N r w Rg
  hlev : Rg (reg .lev) = []
  hu : Rg (reg .u) = []
  ha₀ : Rg (reg .a₀) = []
  hL : Rg (reg .L) = []
  hrows : Rg (reg .rows) = []
  hn : (Rg (reg .n)).length = N
  hw : (Rg (reg .w)).length = w
  hrw : (Rg (reg .rw)).length = r * w
  hK : (Rg (reg .K)).length = K
  hρ : (Rg (reg .ρ)).length = ρ

/-- `CompactTopRegs` does not read `io`. -/
lemma CompactTopRegs.update_io {Rg : Fin (nT BReg) → List (Fin (A + 4))} {N r w K ρ : ℕ}
    (h : CompactTopRegs bc Rg N r w K ρ) (l : List (Fin (A + 4))) :
    CompactTopRegs bc (Function.update Rg (reg .io) l) N r w K ρ where
  rest := h.rest.update_io l
  hlev := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hlev
  hu := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hu
  ha₀ := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.ha₀
  hL := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hL
  hrows := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hrows
  hn := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hn
  hw := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hw
  hrw := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hrw
  hK := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hK
  hρ := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hρ

/- Outside `ph .af`, `lf (.k .cf)` and `rowctr`, the rest state does not depend on the number
of address bits. -/
omit [Fintype BReg] in
lemma compactTopRestSpec_bits {bc : BReg → List (Fin (A + 4)) → Prop} {N N' r w : ℕ}
    {x : LReg BReg} {l : List (Fin (A + 4))} (h1 : x ≠ .ph .af) (h2 : x ≠ .lf (.k .cf))
    (h3 : x ≠ .rowctr) : restSpec bc N r w x l ↔ restSpec bc N' r w x l := by
  cases x with
  | ph y => cases y <;> simp_all [restSpec, phRest]
  | lf y =>
    cases y with
    | k z => cases z <;> simp_all [restSpec, lfRest]
    | _ => simp_all [restSpec, lfRest]
  | _ => simp_all [restSpec]

/- The parameter registers are unconstrained at rest. -/
omit [Fintype BReg] in
lemma compactTopRestSpec_par {bc : BReg → List (Fin (A + 4)) → Prop} {N r w : ℕ} {x : LReg BReg}
    (hx : x ∈ parRegs (BReg := BReg)) (l : List (Fin (A + 4))) : restSpec bc N r w x l := by
  simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

/-- The storage registers: `park` holds the configuration record on top of anything, `ph .arr`
holds the piece record, `lf (.k .arr)`, `st` and `cs` are empty. -/
structure CompactTopIn (Rg : Fin (nT BReg) → List (Fin (A + 4))) (cfg pfs : List ℕ) : Prop where
  cf : ∃ rest, Rg (reg .park) = topRec cfg ++ rest
  pl : Rg (reg (.ph .arr)) = topRec pfs
  pb : Rg (reg (.lf (.k .arr))) = []
  x : Rg (reg .st) = []
  y : Rg (reg .cs) = []

lemma CompactTopIn.update_io {Rg : Fin (nT BReg) → List (Fin (A + 4))} {cfg pfs : List ℕ}
    (h : CompactTopIn (BReg := BReg) Rg cfg pfs) (l : List (Fin (A + 4))) :
    CompactTopIn (BReg := BReg) (Function.update Rg (reg .io) l) cfg pfs where
  cf := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.cf
  pl := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.pl
  pb := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.pb
  x := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.x
  y := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.y

lemma compactTopParState {A : ℕ} {Rg : Fin (nT BReg) → List (Fin (A + 4))}
    {j u K ρ a₀ L rows n w rw : ℕ} (h1 : (Rg (reg .lev)).length = j)
    (h2 : (Rg (reg .u)).length = u) (h3 : (Rg (reg .K)).length = K)
    (h4 : (Rg (reg .ρ)).length = ρ) (h5 : (Rg (reg .a₀)).length = a₀)
    (h6 : (Rg (reg .L)).length = L) (h7 : (Rg (reg .rows)).length = rows)
    (h8 : (Rg (reg .n)).length = n) (h9 : (Rg (reg .w)).length = w)
    (h10 : (Rg (reg .rw)).length = rw) : ParState Rg j u K ρ a₀ L rows n w rw := by
  intro x
  cases x <;> first | exact trivial | assumption

/-- A register file agreeing with one at rest outside the parameter registers is at rest. -/
lemma compactTopRest_par {Rg Rg' : Fin (nT BReg) → List (Fin (A + 4))} {N r w : ℕ}
    (h : Rest bc N r w Rg) (hR : ∀ x, x ∉ parRegs (BReg := BReg) → Rg' (reg x) = Rg (reg x)) :
    Rest bc N r w Rg' := by
  intro x
  by_cases hx : x ∈ parRegs (BReg := BReg)
  · exact compactTopRestSpec_par hx _
  · rw [hR x hx]; exact h x

variable {Q : ℕ} {U P : Type} (body : P → Pr P (nT BReg) Q A U)

/-- Read field `i` of the configuration record onto `dst`. -/
noncomputable def compactTopRd (dst : Fin (nT BReg)) (i : ℕ) : Pr P (nT BReg) Q A U :=
  topGet (reg .park) (reg .lenctr) dst i

/-- `compactTopRd`: `dst` gains `cfg[i]` ticks; every other register ends as it started. -/
theorem compactTopRd_exec {x : LReg BReg} (hx1 : x ≠ .park) (hx2 : x ≠ .lenctr) {cfg : List ℕ}
    (i : ℕ) (hi : i < cfg.length) (v : HS (nT BReg) Q A U)
    (S : Stacks (nT BReg) A) (hlc : S.R (reg .lenctr) = [])
    (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topGetCost cfg ∧
      Exec body (compactTopRd (reg x) i) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg x) (List.replicate cfg[i] tick ++ S.R (reg x)) }) := by
  obtain ⟨rest, hcf⟩ := hcf
  exact topGet_exec body (nodup_map_reg (l := [.park, .lenctr, x])
    (by simp [Ne.symm hx1, Ne.symm hx2])) cfg i hi rest v S hcf hlc


end
end IntegerMultBounds.MathlibTM2.LayerMachine
