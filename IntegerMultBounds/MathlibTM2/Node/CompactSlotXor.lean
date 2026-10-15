module

public import IntegerMultBounds.MathlibTM2.Node.SlotXor
public import IntegerMultBounds.MathlibTM2.Node.CompactBadPrep
public import IntegerMultBounds.MathlibTM2.Node.CompactFix
public import IntegerMultBounds.MathlibTM2.Node.CompactSwapBridge
public import IntegerMultBounds.MathlibTM2.Node.CompactRotInst
public import IntegerMultBounds.MathlibTM2.Node.CompactEncBridge

/-!
# The compact slot XOR

The slot XOR of slot `x` into slot `y` by the compact-control program of
`Layer/CompactXor.lean`: the records are keyed with their ideal destinations, moved by the
instructions of `progE` (source above target) or `progL` (source below target) — swaps of the
`nG`-bit control fields `T`, `B`, `U` by the vendored interchange and rotations of `Y` and `B` by
prepared offsets — repaired at the exceptional indices, fixed at the top column, and the
registers cleared.

**Index models.** The instructions, the repair and the fix use the eleven-field tiling `len11`
(below `B`, `B`, gap, lower slot, gap, upper slot, gap, `T`, gap, `U`, above `U`); the key pass
uses the eight-field tiling `len8` (below the lower slot, lower slot, gap, upper slot, above,
the row bits, two empty fields). The interchange uses the three-chunk rectangle of the old
machine with the chunks `B`, `T`, `U` of width `nG`, hence the vendored cost `V (nG)^τ` of one
interchange, with `nG = (k - 1) G` instead of the slot width `L = K k`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor
  IntegerMultBounds.MathlibTM2.Layer.CompactXor

/-! ### The data of one compact slot XOR -/

/-- The data: bit stride `K`, offsets `ρ` and `a₀`, slot width `L = K k`, row count `R`,
address width `n`, record length `rw`, columns `k`, digit width `G`, the position `bB` of the
control field `B`, the chunk distances `pT < pU` of the control fields `T`, `U` above `B`, and
the static slots `x` (source), `y` (target). -/
structure CxD where
  a₀ : ℕ
  K : ℕ
  ρ : ℕ
  L : ℕ
  R : ℕ
  n : ℕ
  rw : ℕ
  k : ℕ
  G : ℕ
  bB : ℕ
  pT : ℕ
  pU : ℕ
  x : ℕ
  y : ℕ

namespace CxD

variable (d : CxD)

/-- The columns handled by the program. -/
def nn : ℕ := d.k - 1
/-- The control field width. -/
def nG : ℕ := d.nn * d.G
/-- The position of `T`. -/
def bT : ℕ := d.bB + d.pT * d.nG
/-- The position of `U`. -/
def bU : ℕ := d.bB + d.pU * d.nG
def lo : ℕ := min d.x d.y
def hi : ℕ := max d.x d.y
/-- The bits of the row field. -/
def rb : ℕ := (sxBits d.R).length
/-- The key length. -/
def kl : ℕ := d.n + d.rb
/-- The keyed record length. -/
def Bk : ℕ := d.rw + d.kl
/-- The record count. -/
def M : ℕ := d.R * 2 ^ d.n

/-- The rectangle data of the interchange: chunks `B` (slot `0`), `T` (slot `pT`), `U`
(slot `pU`) of width `nG` from `bB`. -/
def swapD : SxD := ⟨d.bB, d.nG, 0, d.nG, d.R, d.n, d.rw, 1, d.pU, d.pT, 0⟩

/-- The eleven-field tiling of the instructions. -/
def len11 : Fin 11 → ℕ :=
  ![d.bB, d.nG, d.a₀ + d.lo * d.L - (d.bB + d.nG), d.L, (d.hi - d.lo - 1) * d.L, d.L,
    d.bT - (d.a₀ + (d.hi + 1) * d.L), d.nG, (d.pU - d.pT - 1) * d.nG, d.nG, d.n - (d.bU + d.nG)]

/-- The eight-field tiling of the key pass. -/
def len8 : Fin 8 → ℕ :=
  ![d.a₀ + d.lo * d.L, d.L, (d.hi - d.lo - 1) * d.L, d.L, d.n - (d.a₀ + (d.hi + 1) * d.L), d.rb,
    0, 0]

/-- The fields of the eleven-field tiling. -/
def fB : Fin 11 := 1
def fLo : Fin 11 := 3
def fHi : Fin 11 := 5
def fT : Fin 11 := 7
def fU : Fin 11 := 9
/-- The source slot field: the upper slot when `x > y`. -/
def fX : Fin 11 := if d.x < d.y then 3 else 5
/-- The target slot field. -/
def fY : Fin 11 := if d.x < d.y then 5 else 3
/-- The source field of the key tiling. -/
def kX : Fin 8 := if d.x < d.y then 1 else 3
/-- The target field of the key tiling. -/
def kY : Fin 8 := if d.x < d.y then 3 else 1

/-- The program: the later source when `x < y`, the earlier source otherwise. -/
def prog : List (CInstr 11) :=
  if d.x < d.y then progL d.len11 fU fT d.fX d.fY fB d.K d.ρ d.G d.nn
  else progE d.len11 fT d.fX d.fY fB d.K d.ρ d.G d.nn

/-- The data with only the static slots `x`, `y`: the programs of the machine depend on the
data through these alone (`compactXorProg_ofXY`). -/
def ofXY (x y : ℕ) : CxD := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x, y⟩

/-- The validity conditions. -/
structure Valid : Prop where
  hρ : d.ρ < d.K
  hLK : d.L = d.K * d.k
  hk : 2 ≤ d.k
  hR : 1 ≤ d.R
  hrw : 1 ≤ d.rw
  hxy : d.x ≠ d.y
  hG : 1 ≤ d.G
  hGK : d.G + 3 ≤ d.K
  hpT : 1 ≤ d.pT
  hpTU : d.pT < d.pU
  hBlo : d.bB + d.nG ≤ d.a₀ + d.lo * d.L
  hhiT : d.a₀ + (d.hi + 1) * d.L ≤ d.bT
  hUn : d.bU + d.nG ≤ d.n

end CxD

/-! ### The registers -/

/-- The unary parameter registers given by the caller. -/
inductive CXPar where
  | K | ρ | a₀ | L | rows | n | rw | G | k | bB | pT | pU
  deriving DecidableEq

/-- The pool of unary values of the preparations and of the interchange setup. -/
inductive CXVal where
  | L | nGa | nGb | ρa | ρb | ρc | z1 | z2 | Ka | Kb | Ga | Gb | nn | padKG | padK | padG
  deriving DecidableEq

/-- The registers of the compact slot XOR: the registers of the old machine (interchange banks,
counters, pass scratch), the eleven field registers, the eight key fields, the rotation's
computed register and preparation scratch, the value pool, the indicator registers, the key
mask, the top mask, the two digit masks, the padding count and setup scratch. -/
inductive CXReg where
  | sx (r : SXReg)
  | fld (g : Fin 11)
  | kf (j : Fin 8)
  | comp
  | rscr (s : Fin 8)
  | val (i : CXVal)
  | breg (b : BReg)
  | mselC | mtopC | mD | mG | padR
  | ts (i : Fin 8)

noncomputable instance : DecidableEq CXReg := Classical.decEq _


/-! ### Register maps -/

section Maps

variable {T : ℕ} (ι : CXReg → Fin T) (par : CXPar → Fin T) (src : Fin T)

/-- Distinct registers: `ι` and `par` are injective with disjoint ranges, and the stream
register `src` is outside both. -/
structure CxEnv : Prop where
  hι : Function.Injective ι
  hpar : Function.Injective par
  hpι : ∀ x p, ι x ≠ par p
  hsrc : ∀ x, ι x ≠ src
  hsrcp : ∀ p, par p ≠ src

/-- The old registers. -/
def sxι : SXReg → Fin T := fun r => ι (.sx r)

/-- The parameter registers of the interchange setup: the rectangle of width `nG` from `bB`. -/
def parSx : SXPar → Fin T
  | .K => ι (.val .nGa) | .ρ => ι (.val .z1) | .a₀ => par .bB | .L => ι (.val .nGb)
  | .rows => par .rows | .n => par .n | .rw => par .rw

/-- The value pool of preparation bank `t`: `W, oO, oA, oY, sA, K, G, n, pad`. -/
def bankVal : Fin 7 → Fin 9 → CXVal
  | 0 => ![.L, .ρa, .ρb, .ρc, .Ka, .Kb, .Ga, .nn, .padKG]
  | 1 => ![.L, .ρa, .z1, .ρc, .Gb, .Kb, .Ga, .nn, .padKG]
  | 2 => ![.nGb, .z1, .ρb, .ρc, .Ka, .Kb, .Ga, .nn, .padG]
  | 3 => ![.L, .ρa, .ρb, .ρc, .Ka, .Kb, .Ga, .nn, .padK]
  | 4 => ![.L, .ρa, .z1, .ρc, .Gb, .Kb, .Ga, .nn, .padK]
  | 5 => ![.nGb, .z1, .ρb, .ρc, .Ka, .Kb, .Ga, .nn, .padG]
  | 6 => ![.nGb, .z1, .z2, .ρc, .Gb, .Kb, .Ga, .nn, .padG]

/-- The registers of the rotation pass with preparation bank `t`. -/
def rotι (t : Fin 7) : RotGReg 11 8 9 → Fin T
  | .src => src
  | .ctr => ι (.sx .ctrKB)
  | .tmp => ι (.sx .rtmp)
  | .cnt => ι (.sx .cnt)
  | .ctmp => ι (.sx .rctmp)
  | .out => ι (.sx .rout)
  | .dst d => ι (.sx (.rdst d))
  | .aux d => ι (.sx (.raux d))
  | .fld g => ι (.fld g)
  | .comp => ι .comp
  | .spare r => ι (.sx (.rsp (Fin.castLE (by norm_num) r)))
  | .scr s => ι (.rscr s)
  | .prm q => ι (.val (bankVal t q))

/-- The registers of the indicator preparation. -/
def badι : BReg → Fin T
  | .mD => ι .mD
  | .mG => ι .mG
  | .padR => ι .padR
  | b => ι (.breg b)

end Maps

/-! ### The instructions of the machine -/

/-- The instructions of the compact program as the machine runs them: interchanges of the
control fields and rotations with a named preparation. The rotation forms: `rotYW ctrlU neg`
(`Y` by `offYW`, control `X` or `U`), `rotBbY` (`B` by the packed `Y` bits), `rotYb ctrlU`
(`Y` by `offYb`), `rotBx ctrlU` (`B` by `offBx`, negative), `rotBbX neg` (`B` by the packed
`X` bits, the load and unload of `U`). -/
inductive CxInstr where
  | swapTB | swapUB
  | rotYW (ctrlU neg : Bool) | rotBbY | rotYb (ctrlU : Bool) | rotBx (ctrlU : Bool)
  | rotBbX (neg : Bool)

namespace CxInstr

/-- The instruction as a compact-program instruction. -/
def toC (d : CxD) : CxInstr → CInstr 11
  | swapTB => .swap CxD.fT CxD.fB
  | swapUB => .swap CxD.fU CxD.fB
  | rotYW ctrlU neg => .rot d.fY neg
      (offYW d.len11 CxD.fT d.K d.ρ d.G d.nn (if ctrlU then CxD.fU else d.fX) (if ctrlU then 0 else d.ρ)
        (if ctrlU then d.G else d.K))
  | rotBbY => .rot CxD.fB false (offBb d.len11 d.G d.nn d.fY d.ρ d.K)
  | rotYb ctrlU => .rot d.fY false
      (offYb d.len11 d.K d.ρ d.nn (if ctrlU then CxD.fU else d.fX) (if ctrlU then 0 else d.ρ)
        (if ctrlU then d.G else d.K))
  | rotBx ctrlU => .rot CxD.fB true
      (offBx d.len11 d.fY d.K d.ρ d.G d.nn (if ctrlU then CxD.fU else d.fX) (if ctrlU then 0 else d.ρ)
        (if ctrlU then d.G else d.K))
  | rotBbX neg => .rot CxD.fB neg (offBb d.len11 d.G d.nn d.fX d.ρ d.K)

/-- The core with control `X` (`ctrlU = false`) or `U`. -/
def core (ctrlU : Bool) : List CxInstr :=
  [rotYW ctrlU false, swapTB, rotBbY, swapTB, rotYb ctrlU, rotYW ctrlU true, swapTB,
    rotBx ctrlU, swapTB]

/-- The load (`neg = false`) and unload of `U`. -/
def loadU (neg : Bool) : List CxInstr := [swapUB, rotBbX neg, swapUB]

/-- The program of the machine. -/
def prog (d : CxD) : List CxInstr :=
  if d.x < d.y then core true ++ loadU false ++ core true ++ loadU true else core false

lemma core_toC (d : CxD) (ctrlU : Bool) :
    (core ctrlU).map (toC d) =
      Layer.CompactXor.core d.len11 CxD.fT d.fY CxD.fB d.K d.ρ d.G d.nn (if ctrlU then CxD.fU else d.fX)
        (if ctrlU then 0 else d.ρ) (if ctrlU then d.G else d.K) := by
  cases ctrlU <;> rfl

lemma loadU_toC (d : CxD) (neg : Bool) :
    (loadU neg).map (toC d) = Layer.CompactXor.loadU d.len11 CxD.fU d.fX CxD.fB d.K d.ρ d.G d.nn neg := rfl

/-- The machine runs the compact program. -/
lemma prog_toC (d : CxD) : (prog d).map (toC d) = d.prog := by
  unfold prog CxD.prog
  split_ifs
  · simp only [List.map_append, core_toC, loadU_toC, ↓reduceIte]
    rfl
  · simp only [core_toC, Bool.false_eq_true, ↓reduceIte]
    rfl

end CxInstr


/-! ### Two more unary primitives -/

section Primitives

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- `c` gains `|a| · |b|` ticks: for every tick of `a`, a copy of `b`. -/
def umulU (a b c t₁ t₂ : Fin T) : Pr P T Q A U := scanP a t₁ (ucopy b c t₂)

theorem umulU_exec {a b c t₁ t₂ : Fin T} (hreg : [a, b, c, t₁, t₂].Nodup) (v : HS T Q A U)
    (S : Stacks T A) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (S.R a).length * (4 * (S.R b).length + 9) + 4 ∧
      Exec body (umulU a b c t₁ t₂) (mk v S) m
        (mk v' { S with
          R := Function.update S.R c
            (List.replicate ((S.R a).length * (S.R b).length) tick ++ S.R c) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hab, hac, ha1, ha2⟩, ⟨hbc, hb1, hb2⟩, ⟨hc1, hc2⟩, h12⟩ := hreg'
  set nb := (S.R b).length with hnb
  let Ψ : ℕ → Regs T A := fun j =>
    Function.update S.R c (List.replicate (j * nb) tick ++ S.R c)
  have hp : IterSpec body (ucopy b c t₂) a t₁ Ψ (fun _ => 4 * nb + 4) (S.R a).length := by
    intro j hj v' S' hS'
    have hb' : S'.R b = S.R b := by
      rw [hS' b hab.symm hb1]; simp [Ψ, Function.update_of_ne hbc]
    have hc' : S'.R c = List.replicate (j * nb) tick ++ S.R c := by
      rw [hS' c hac.symm hc1]; simp [Ψ]
    have ht₂' : S'.R t₂ = [] := by
      rw [hS' t₂ ha2.symm h12.symm]; simp [Ψ, Function.update_of_ne hc2.symm, ht₂]
    obtain ⟨v'', hu, he⟩ := ucopy_exec body hbc hb2 hc2 v' S' ht₂'
    rw [hb'] at he
    refine ⟨v'', _, _, hu, le_rfl, he, Function.update_of_ne hac _ _,
      Function.update_of_ne hc1.symm _ _, fun k hka hkt => ?_⟩
    simp only [Ψ, Function.update_apply]
    split_ifs with hk
    · subst hk
      rw [hc', ← List.append_assoc, ← List.replicate_add]
      congr 2; ring
    · rw [hS' k hka hkt]; simp [Ψ, Function.update_of_ne hk]
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := scanP_exec body ha1 hp 0 v S (by omega)
    (fun k _ _ => by simp [Ψ])
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, ht₁, List.length_nil] at hm
    nlinarith
  · congr 2
    funext k
    by_cases hka : k = a
    · subst hka; rw [ha', ht₁, Function.update_of_ne hac]; rfl
    by_cases hkt : k = t₁
    · subst hkt; rw [ht', Function.update_of_ne hc1.symm, ht₁]
    rw [hΨ' k hka hkt]
    simp [Ψ]

end Primitives


/-! ### The register contents after the setup -/

namespace CxD

variable (d : CxD)

/-- The parameter values. -/
def par : CXPar → ℕ
  | .K => d.K | .ρ => d.ρ | .a₀ => d.a₀ | .L => d.L | .rows => d.R | .n => d.n | .rw => d.rw
  | .G => d.G | .k => d.k | .bB => d.bB | .pT => d.pT | .pU => d.pU

/-- The values of the pool. -/
def valOf : CXVal → ℕ
  | .L => d.L | .nGa => d.nG | .nGb => d.nG | .ρa => d.ρ | .ρb => d.ρ | .ρc => d.ρ
  | .z1 => 0 | .z2 => 0 | .Ka => d.K | .Kb => d.K | .Ga => d.G | .Gb => d.G | .nn => d.nn
  | .padKG => d.K - 1 - d.G | .padK => d.K - 1 | .padG => d.G - 1

end CxD

/-- The setup stage of a pool value. -/
def valStage : CXVal → ℕ
  | .nn => 1 | .nGa => 2 | .nGb => 3 | .L => 4 | .ρa => 5 | .ρb => 6 | .ρc => 7 | .Ka => 8
  | .Kb => 9 | .Ga => 10 | .Gb => 11 | .padKG => 12 | .padK => 13 | .padG => 14 | .z1 => 0
  | .z2 => 0

/-- The setup stage building each register (`0`: empty at rest; `15`: the interchange setup). -/
def cxStage : CXReg → ℕ
  | .val i => valStage i
  | .sx r => if sxStage r = 0 then 0 else 15
  | .fld g => 16 + g
  | .kf j => if j.val < 6 then 27 + j else 0
  | .mselC => 33 | .mD => 34 | .mG => 35 | .mtopC => 36 | .padR => 37
  | .comp => 0 | .rscr _ => 0 | .breg _ => 0 | .ts _ => 0

lemma cxStage_le (x : CXReg) : cxStage x ≤ 37 := by
  cases x with
  | val i => cases i <;> simp [cxStage, valStage]
  | sx r => simp only [cxStage]; split_ifs <;> omega
  | fld g => have := g.isLt; simp only [cxStage]; omega
  | kf j => have := j.isLt; simp only [cxStage]; split_ifs <;> omega
  | _ => simp [cxStage]

/-- The contents of the registers after the setup. -/
def cxBc (A : ℕ) (d : CxD) : CXReg → List (Fin (A + 4))
  | .sx r => sxBc A d.swapD r
  | .fld g => binSyms (d.len11 g) 0
  | .kf j => binSyms (d.len8 j) 0
  | .val i => List.replicate (d.valOf i) tick
  | .mselC => binSyms d.L (selMask d.K d.ρ d.nn)
  | .mtopC => binSyms d.L (2 ^ (d.ρ + d.nn * d.K))
  | .mD => binSyms d.L (altMask d.G d.L)
  | .mG => binSyms d.L (highMask d.K d.ρ d.G d.nn d.L)
  | .padR => List.replicate (d.L - d.nG) tick
  | .comp => [] | .rscr _ => [] | .breg _ => [] | .ts _ => []

lemma cxBc_zero (A : ℕ) (d : CxD) (x : CXReg) (hx : cxStage x = 0) : cxBc A d x = [] := by
  cases x with
  | val i => cases i <;> simp_all [cxStage, valStage, cxBc, CxD.valOf]
  | sx r =>
      simp only [cxStage] at hx
      split_ifs at hx with h
      exact sxBc_zero A _ r h
  | fld g => simp [cxStage] at hx
  | kf j => fin_cases j <;> simp_all [cxStage, cxBc, CxD.len8, binSyms]
  | _ => simp_all [cxStage, cxBc]

/-- Only the old registers are built at stage `15`. -/
lemma cxStage_ne_15 (y : CXReg) (hy : ∀ r, y ≠ CXReg.sx r) : cxStage y ≠ 15 := by
  cases y with
  | val i => cases i <;> simp [cxStage, valStage]
  | sx r => exact absurd rfl (hy r)
  | fld g => simp only [cxStage]; omega
  | kf j => simp only [cxStage]; split_ifs <;> omega
  | _ => simp [cxStage]

/-! ### Filling the registers stage by stage -/

section Fill

variable {T A : ℕ} (ι : CXReg → Fin T)

/-- The register file after the first `s` setup stages, over the base file `R₀`. -/
noncomputable def cxFill (bc : CXReg → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.extend ι (fun x => if cxStage x ≤ s then bc x else []) R₀

variable {ι}

lemma cxFill_ι (hι : Function.Injective ι) (bc : CXReg → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) (x : CXReg) :
    cxFill ι bc s R₀ (ι x) = if cxStage x ≤ s then bc x else [] :=
  hι.extend_apply _ _ _

lemma cxFill_out (bc : CXReg → List (Fin (A + 4))) (s : ℕ) (R₀ : Fin T → List (Fin (A + 4)))
    {t : Fin T} (ht : ∀ x, ι x ≠ t) : cxFill ι bc s R₀ t = R₀ t :=
  Function.extend_apply' _ _ _ (by rintro ⟨x, rfl⟩; exact ht x rfl)

/-- Stage `s + 1` fills exactly the registers of stage `s + 1`. -/
lemma cxFill_succ (hι : Function.Injective ι) (bc : CXReg → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) {R : Fin T → List (Fin (A + 4))}
    (hnew : ∀ x, cxStage x = s + 1 → R (ι x) = bc x)
    (hold : ∀ k, (∀ x, cxStage x = s + 1 → k ≠ ι x) → R k = cxFill ι bc s R₀ k) :
    R = cxFill ι bc (s + 1) R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [cxFill_ι hι]
    by_cases hy : cxStage y = s + 1
    · rw [hnew y hy, if_pos (by omega)]
    · rw [hold _ (fun x hx e => hy (by rw [hι e]; exact hx)), cxFill_ι hι]
      by_cases h1 : cxStage y ≤ s
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  · simp only [not_exists] at ht
    rw [hold _ (fun x _ e => ht x e.symm), cxFill_out _ _ _ ht, cxFill_out _ _ _ ht]

/-- Stage `s + 1` with a single register `x`. -/
lemma cxFill_step (hι : Function.Injective ι) (bc : CXReg → List (Fin (A + 4))) {s : ℕ}
    (R₀ : Fin T → List (Fin (A + 4))) {x : CXReg} (hx : cxStage x = s + 1)
    (huniq : ∀ y, cxStage y = s + 1 → y = x) :
    Function.update (cxFill ι bc s R₀) (ι x) (bc x) = cxFill ι bc (s + 1) R₀ := by
  apply cxFill_succ hι bc s R₀
  · intro y hy
    rw [huniq y hy, Function.update_self]
  · intro k hk
    rw [Function.update_of_ne (hk x hx)]

lemma cxFill_unstep (hι : Function.Injective ι) (bc : CXReg → List (Fin (A + 4))) {s : ℕ}
    (R₀ : Fin T → List (Fin (A + 4))) {x : CXReg} (hx : cxStage x = s + 1)
    (huniq : ∀ y, cxStage y = s + 1 → y = x) :
    Function.update (cxFill ι bc (s + 1) R₀) (ι x) [] = cxFill ι bc s R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [cxFill_ι hι]
    by_cases hy : y = x
    · subst hy; rw [Function.update_self, if_neg (by omega)]
    · rw [Function.update_of_ne (hι.ne hy), cxFill_ι hι]
      have : cxStage y ≠ s + 1 := fun h => hy (huniq y h)
      by_cases h1 : cxStage y ≤ s
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  · simp only [not_exists] at ht
    rw [Function.update_of_ne (fun h => ht x h.symm), cxFill_out _ _ _ ht, cxFill_out _ _ _ ht]

lemma cxFill_zero (hι : Function.Injective ι) (bc : CXReg → List (Fin (A + 4)))
    (R₀ : Fin T → List (Fin (A + 4))) (h0 : ∀ x, R₀ (ι x) = [])
    (hbc : ∀ x, cxStage x = 0 → bc x = []) : cxFill ι bc 0 R₀ = R₀ := by
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [cxFill_ι hι, h0]
    split_ifs with h
    · exact hbc y (by omega)
    · rfl
  · simp only [not_exists] at ht
    rw [cxFill_out _ _ _ ht]

lemma cxFill_update (hι : Function.Injective ι) (bc : CXReg → List (Fin (A + 4))) (s : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) {t : Fin T} (ht : ∀ x, ι x ≠ t) (l : List (Fin (A + 4))) :
    Function.update (cxFill ι bc s R₀) t l = cxFill ι bc s (Function.update R₀ t l) := by
  funext t'
  by_cases h : ∃ y, ι y = t'
  · obtain ⟨y, rfl⟩ := h
    rw [Function.update_of_ne (ht y), cxFill_ι hι, cxFill_ι hι]
  · simp only [not_exists] at h
    rw [cxFill_out _ _ _ h]
    by_cases htt : t' = t
    · subst htt; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne htt, Function.update_of_ne htt, cxFill_out _ _ _ h]

/-- The interchange setup as stage `15`: the old registers filled over the file after stage
`14`. -/
lemma cxFill_sx (hι : Function.Injective ι) (d : CxD) (R₀ : Fin T → List (Fin (A + 4))) :
    sxFill (sxι ι) (sxBc A d.swapD) 38 (cxFill ι (cxBc A d) 14 R₀) = cxFill ι (cxBc A d) 15 R₀ := by
  have hsxι : Function.Injective (sxι ι) := fun a b h => by
    have := hι h; simpa [CXReg.sx.injEq] using this
  funext t
  by_cases ht : ∃ y, ι y = t
  · obtain ⟨y, rfl⟩ := ht
    by_cases hsx : ∃ r, y = CXReg.sx r
    · obtain ⟨r, rfl⟩ := hsx
      rw [show ι (CXReg.sx r) = sxι ι r from rfl, sxFill_ι hsxι, if_pos (sxStage_le r),
        show sxι ι r = ι (CXReg.sx r) from rfl, cxFill_ι hι]
      simp only [cxStage, cxBc]
      split_ifs <;> first | rfl | omega
    · simp only [not_exists] at hsx
      have hne := cxStage_ne_15 y hsx
      rw [sxFill_out (ι := sxι ι) _ _ _ (fun r e => hsx r (hι e).symm), cxFill_ι hι, cxFill_ι hι]
      by_cases h1 : cxStage y ≤ 14
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  · simp only [not_exists] at ht
    rw [sxFill_out (ι := sxι ι) _ _ _ (fun r => ht (CXReg.sx r)), cxFill_out _ _ _ ht,
      cxFill_out _ _ _ ht]

/-- The filled file is an interchange fill over itself. -/
lemma cxFill_sx_self (hι : Function.Injective ι) (d : CxD) (R₀ : Fin T → List (Fin (A + 4)))
    (s : ℕ) (hs : 15 ≤ s) :
    sxFill (sxι ι) (sxBc A d.swapD) 38 (cxFill ι (cxBc A d) s R₀) = cxFill ι (cxBc A d) s R₀ := by
  have hsxι : Function.Injective (sxι ι) := fun a b h => by
    have := hι h; simpa [CXReg.sx.injEq] using this
  funext t
  by_cases ht : ∃ r, sxι ι r = t
  · obtain ⟨r, rfl⟩ := ht
    rw [sxFill_ι hsxι, if_pos (sxStage_le r), show sxι ι r = ι (CXReg.sx r) from rfl,
      cxFill_ι hι]
    simp only [cxStage, cxBc]
    split_ifs with h1 h2 <;> first | rfl | omega | (rw [sxBc_zero A _ r h1])
  · simp only [not_exists] at ht
    rw [sxFill_out (ι := sxι ι) _ _ _ ht]

end Fill


/-! ### The setup stages -/

section Stages

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable (ι : CXReg → Fin T) (par : CXPar → Fin T)

/-- Drop the top symbol of `r`. -/
def popTop (r : Fin T) : Act T Q A U := .pop (.rt r) (fun v _ => v) .done

lemma popTop_run (r : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (popTop r : Act T Q A U).run (mk v S) =
      mk v { S with R := Function.update S.R r (S.R r).tail } := by
  simp [popTop, Action.run, update_rt]

/-- The length of a field register of the eleven-field tiling, assembled in `ts 0`
(`fld 2`, `fld 4`, `fld 6`, `fld 8`, `fld 10`) from the parameters. -/
noncomputable def cxLenProg (d : CxD) : Fin 11 → Pr P T Q A U
  | 2 => .seq (.seq (.seq (ucopy (par .a₀) (ι (.ts 0)) (ι (.ts 1)))
      (umul d.lo (par .L) (ι (.ts 0)) (ι (.ts 1))))
      (usub (par .bB) (ι (.ts 0)) (ι (.ts 1)))) (usub (ι (.val .nGa)) (ι (.ts 0)) (ι (.ts 1)))
  | 4 => umul (d.hi - d.lo - 1) (par .L) (ι (.ts 0)) (ι (.ts 1))
  | 6 => .seq (.seq (.seq (.seq (.seq (ucopy (par .bB) (ι (.ts 0)) (ι (.ts 1)))
      (umulU (par .pT) (ι (.val .nGa)) (ι (.ts 0)) (ι (.ts 1)) (ι (.ts 2))))
      (usub (par .a₀) (ι (.ts 0)) (ι (.ts 1))))
      (umul (d.hi + 1) (par .L) (ι (.ts 2)) (ι (.ts 1))))
      (usub (ι (.ts 2)) (ι (.ts 0)) (ι (.ts 1)))) (uclear (ι (.ts 2)))
  | 8 => .seq (.seq (.seq (.seq (ucopy (par .pU) (ι (.ts 2)) (ι (.ts 1)))
      (usub (par .pT) (ι (.ts 2)) (ι (.ts 1)))) (.act (popTop (ι (.ts 2)))))
      (umulU (ι (.ts 2)) (ι (.val .nGa)) (ι (.ts 0)) (ι (.ts 1)) (ι (.ts 3))))
      (uclear (ι (.ts 2)))
  | 10 => .seq (.seq (.seq (.seq (.seq (ucopy (par .n) (ι (.ts 0)) (ι (.ts 1)))
      (usub (par .bB) (ι (.ts 0)) (ι (.ts 1))))
      (umulU (par .pU) (ι (.val .nGa)) (ι (.ts 2)) (ι (.ts 1)) (ι (.ts 3))))
      (ucopy (ι (.val .nGa)) (ι (.ts 2)) (ι (.ts 1))))
      (usub (ι (.ts 2)) (ι (.ts 0)) (ι (.ts 1)))) (uclear (ι (.ts 2)))
  | _ => .act .done

/-- The length register of a field of the eleven-field tiling, when direct. -/
def cxLenReg : Fin 11 → Option (Fin T)
  | 0 => some (par .bB) | 1 => some (ι (.val .nGa)) | 3 => some (par .L) | 5 => some (par .L)
  | 7 => some (ι (.val .nGa)) | 9 => some (ι (.val .nGa)) | _ => none

/-- Build the zeros of field `g`: from a direct length register, or from `ts 0` assembled by
`cxLenProg`. -/
noncomputable def cxFldProg (d : CxD) (g : Fin 11) : Pr P T Q A U :=
  match cxLenReg ι par g with
  | some a => zeroBits a (ι (.fld g)) (ι (.ts 1))
  | none => .seq (cxLenProg ι par d g)
      (.seq (zeroBits (ι (.ts 0)) (ι (.fld g)) (ι (.ts 1))) (uclear (ι (.ts 0))))

/-- The length of a key field, assembled in `ts 0` (`kf 0`, `kf 2`, `kf 4`). -/
noncomputable def cxKLenProg (d : CxD) : Fin 8 → Pr P T Q A U
  | 0 => .seq (ucopy (par .a₀) (ι (.ts 0)) (ι (.ts 1))) (umul d.lo (par .L) (ι (.ts 0)) (ι (.ts 1)))
  | 2 => umul (d.hi - d.lo - 1) (par .L) (ι (.ts 0)) (ι (.ts 1))
  | 4 => .seq (.seq (.seq (.seq (ucopy (par .n) (ι (.ts 0)) (ι (.ts 1)))
      (usub (par .a₀) (ι (.ts 0)) (ι (.ts 1))))
      (umul (d.hi + 1) (par .L) (ι (.ts 2)) (ι (.ts 1))))
      (usub (ι (.ts 2)) (ι (.ts 0)) (ι (.ts 1)))) (uclear (ι (.ts 2)))
  | _ => .act .done

def cxKLenReg : Fin 8 → Option (Fin T)
  | 1 => some (par .L) | 3 => some (par .L) | 5 => some (ι (.sx .rb)) | _ => none

noncomputable def cxKfProg (d : CxD) (j : Fin 8) : Pr P T Q A U :=
  match cxKLenReg ι par j with
  | some a => zeroBits a (ι (.kf j)) (ι (.ts 1))
  | none => .seq (cxKLenProg ι par d j)
      (.seq (zeroBits (ι (.ts 0)) (ι (.kf j)) (ι (.ts 1))) (uclear (ι (.ts 0))))

/-- The stages of the interchange setup, the four gap stages taking the chunk distances `pT`,
`pU` from registers (`n3 = bB`, `n2 = (pT - 1) nG`, `n1 = (pU - pT - 1) nG`,
`n0 = n - bB - (pU + 1) nG`), the others as in `sxStageProg`. -/
noncomputable def cxGapProg (d : CxD) : ℕ → Pr P T Q A U
  | 1 => ucopy (par .bB) (ι (.sx .n3)) (ι (.sx (.sc 0)))
  | 2 => .seq (.seq (.seq (ucopy (par .pT) (ι (.sx (.sc 1))) (ι (.sx (.sc 0))))
      (.act (popTop (ι (.sx (.sc 1))))))
      (umulU (ι (.sx (.sc 1))) (ι (.val .nGa)) (ι (.sx .n2)) (ι (.sx (.sc 0))) (ι (.sx (.sc 2)))))
      (uclear (ι (.sx (.sc 1))))
  | 3 => .seq (.seq (.seq (.seq (ucopy (par .pU) (ι (.sx (.sc 1))) (ι (.sx (.sc 0))))
      (usub (par .pT) (ι (.sx (.sc 1))) (ι (.sx (.sc 0)))))
      (.act (popTop (ι (.sx (.sc 1))))))
      (umulU (ι (.sx (.sc 1))) (ι (.val .nGa)) (ι (.sx .n1)) (ι (.sx (.sc 0))) (ι (.sx (.sc 2)))))
      (uclear (ι (.sx (.sc 1))))
  | 4 => .seq (.seq (.seq (.seq (.seq (ucopy (par .n) (ι (.sx .n0)) (ι (.sx (.sc 0))))
      (usub (par .bB) (ι (.sx .n0)) (ι (.sx (.sc 0)))))
      (umulU (par .pU) (ι (.val .nGa)) (ι (.sx (.sc 1))) (ι (.sx (.sc 0))) (ι (.sx (.sc 2)))))
      (ucopy (ι (.val .nGa)) (ι (.sx (.sc 1))) (ι (.sx (.sc 0)))))
      (usub (ι (.sx (.sc 1))) (ι (.sx .n0)) (ι (.sx (.sc 0)))))
      (uclear (ι (.sx (.sc 1))))
  | s => sxStageProg (sxι ι) (parSx ι par) 2 1 0 s

/-- The step bounds of the interchange setup stages. -/
noncomputable def cxGapCost (d : CxD) : ℕ → ℕ
  | 1 => 4 * d.bB + 4
  | 2 => 4 * d.pT + 4 + 1 + (d.pT * (4 * d.nG + 9) + 4) + (2 * d.pT + 2)
  | 3 => 4 * d.pU + 4 + (4 * d.pT + 4) + 1 + (d.pU * (4 * d.nG + 9) + 4) + (2 * d.pU + 2)
  | 4 => 4 * d.n + 4 + (4 * d.bB + 4) + (d.pU * (4 * d.nG + 9) + 4) + (4 * d.nG + 4) +
      (4 * ((d.pU + 1) * d.nG) + 4) + (2 * ((d.pU + 1) * d.nG) + 2)
  | s => sxStageCost d.swapD s

/-- The setup stage programs. -/
noncomputable def cxStageProg (d : CxD) : ℕ → Pr P T Q A U
  | 1 => .seq (ucopy (par .k) (ι (.val .nn)) (ι (.ts 0))) (.act (popTop (ι (.val .nn))))
  | 2 => umulU (ι (.val .nn)) (par .G) (ι (.val .nGa)) (ι (.ts 0)) (ι (.ts 1))
  | 3 => ucopy (ι (.val .nGa)) (ι (.val .nGb)) (ι (.ts 0))
  | 4 => ucopy (par .L) (ι (.val .L)) (ι (.ts 0))
  | 5 => ucopy (par .ρ) (ι (.val .ρa)) (ι (.ts 0))
  | 6 => ucopy (par .ρ) (ι (.val .ρb)) (ι (.ts 0))
  | 7 => ucopy (par .ρ) (ι (.val .ρc)) (ι (.ts 0))
  | 8 => ucopy (par .K) (ι (.val .Ka)) (ι (.ts 0))
  | 9 => ucopy (par .K) (ι (.val .Kb)) (ι (.ts 0))
  | 10 => ucopy (par .G) (ι (.val .Ga)) (ι (.ts 0))
  | 11 => ucopy (par .G) (ι (.val .Gb)) (ι (.ts 0))
  | 12 => .seq (.seq (ucopy (par .K) (ι (.val .padKG)) (ι (.ts 0)))
      (.act (popTop (ι (.val .padKG))))) (usub (par .G) (ι (.val .padKG)) (ι (.ts 0)))
  | 13 => .seq (ucopy (par .K) (ι (.val .padK)) (ι (.ts 0))) (.act (popTop (ι (.val .padK))))
  | 14 => .seq (ucopy (par .G) (ι (.val .padG)) (ι (.ts 0))) (.act (popTop (ι (.val .padG))))
  | 15 => Prog.seqList ((List.range 38).map fun i => cxGapProg ι par d (i + 1))
  | 33 => sxMask (par .L) (ι (.val .ρa)) (ι (.val .Ka)) (ι (.val .nn)) (ι .mselC) (ι (.ts 0))
      (ι (.ts 1)) (ι (.ts 2)) (ι (.ts 3)) true false
  | 34 => segMask (par .L) (ι (.val .z1)) (ι (.val .Ga)) (ι (.val .Gb)) (ι (.val .L)) (ι .mD)
      (ι (.ts 0)) (ι (.ts 1)) (ι (.ts 2)) (ι (.ts 3))
  | 35 => .seq (.seq (.seq (.seq (.seq (.seq (ucopy (par .G) (ι (.ts 0)) (ι (.ts 1)))
      (.act (pushN (ι (.ts 0)) (fun _ => tick) 2 .done)))
      (ucopy (par .K) (ι (.ts 4)) (ι (.ts 1))))
      (usub (ι (.ts 0)) (ι (.ts 4)) (ι (.ts 1))))
      (segMask (par .L) (ι (.val .ρa)) (ι (.ts 0)) (ι (.ts 4)) (ι (.val .nn)) (ι .mG)
        (ι (.ts 1)) (ι (.ts 2)) (ι (.ts 3)) (ι (.ts 5))))
      (uclear (ι (.ts 0)))) (uclear (ι (.ts 4)))
  | 36 => .seq (.seq (.seq (ucopy (par .ρ) (ι (.ts 0)) (ι (.ts 1)))
      (umulU (ι (.val .nn)) (par .K) (ι (.ts 0)) (ι (.ts 1)) (ι (.ts 2))))
      (bitMask (par .L) (ι (.ts 0)) (ι .mtopC) (ι (.ts 1)) (ι (.ts 2)) (ι (.ts 3))))
      (uclear (ι (.ts 0)))
  | 37 => .seq (ucopy (par .L) (ι .padR) (ι (.ts 0))) (usub (ι (.val .nGa)) (ι .padR) (ι (.ts 0)))
  | s => if h : 16 ≤ s ∧ s ≤ 26 then cxFldProg ι par d ⟨s - 16, by omega⟩
      else if h' : 27 ≤ s ∧ s ≤ 32 then cxKfProg ι par d ⟨s - 27, by omega⟩
      else .act .done

/-- The step bound of every setup stage of the machine itself (the interchange setup aside):
linear in the parameters. -/
def cxUnit (d : CxD) : ℕ :=
  60 * (d.L + d.K + d.G + d.n + d.a₀ + d.bB + d.rb + d.nG + d.k + d.ρ) + d.L * (4 * d.K + 9) +
    d.nn * (12 * d.K + 20) + d.L * (8 * d.G + 13) + (d.pT + d.pU) * (4 * d.nG + 20) + 200

/-- The step bound of setup stage `s`. -/
noncomputable def cxStageCost (d : CxD) (s : ℕ) : ℕ :=
  if s = 15 then ∑ i ∈ Finset.range 38, cxGapCost d (i + 1) + 1 else cxUnit d

/-- The specification of setup stage `s + 1`. -/
def CxStageSpec (d : CxD) (R₀ : Fin T → List (Fin (A + 4))) (s : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), S.R = cxFill ι (cxBc A d) s R₀ →
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxStageCost d (s + 1) ∧
      Exec body (cxStageProg ι par d (s + 1)) (mk v S) m
        (mk v' { S with R := cxFill ι (cxBc A d) (s + 1) R₀ })

end Stages


/-! ### Stage proofs -/

section StageProofs

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable {ι : CXReg → Fin T} {par : CXPar → Fin T} {src : Fin T}

lemma CxEnv.ne (h : CxEnv ι par src) {a b : CXReg} (hab : a ≠ b) : ι a ≠ ι b := h.hι.ne hab

lemma CxEnv.hpι' (h : CxEnv ι par src) (p : CXPar) (x : CXReg) : par p ≠ ι x := (h.hpι x p).symm

lemma CxEnv.fill_ι (h : CxEnv ι par src) {bc : CXReg → List (Fin (A + 4))} {s : ℕ}
    {R₀ : Fin T → List (Fin (A + 4))} {S : Stacks T A} (hS : S.R = cxFill ι bc s R₀) (x : CXReg) :
    S.R (ι x) = if cxStage x ≤ s then bc x else [] := by
  rw [hS, cxFill_ι h.hι]

lemma CxEnv.fill_par (h : CxEnv ι par src) {bc : CXReg → List (Fin (A + 4))} {s : ℕ}
    {R₀ : Fin T → List (Fin (A + 4))} {S : Stacks T A} (hS : S.R = cxFill ι bc s R₀)
    (p : CXPar) : S.R (par p) = R₀ (par p) := by
  rw [hS, cxFill_out _ _ _ (fun x => h.hpι x p)]

/-- The register file after a stage: the file after the previous stage with the stage register
set to its contents. -/
lemma cx_finish2 (henv : CxEnv ι par src) {bc : CXReg → List (Fin (A + 4))} {s : ℕ}
    {R₀ : Fin T → List (Fin (A + 4))} {S : Stacks T A} (hS : S.R = cxFill ι bc s R₀)
    {x : CXReg} (hx : cxStage x = s + 1) (huniq : ∀ y, cxStage y = s + 1 → y = x)
    {R' : Fin T → List (Fin (A + 4))} (h₁ : R' (ι x) = bc x) (h₂ : ∀ t, t ≠ ι x → R' t = S.R t) :
    R' = cxFill ι bc (s + 1) R₀ := by
  rw [← cxFill_step henv.hι _ R₀ hx huniq, ← hS]
  funext t
  by_cases ht : t = ι x
  · subst ht; rw [h₁, Function.update_self]
  · rw [Function.update_of_ne ht, h₂ t ht]

set_option hygiene false in
/-- Distinctness of named registers. -/
macro "cxne" : tactic => `(tactic| first
  | exact henv.ne (by simp [Fin.ext_iff])
  | exact henv.hpι _ _
  | exact henv.hpι' _ _
  | exact henv.hpar.ne (by simp)
  | exact henv.hsrc _
  | exact (henv.hsrc _).symm
  | exact henv.hsrcp _
  | exact (henv.hsrcp _).symm)

set_option hygiene false in
/-- Evaluate a register file given by updates of named registers over a setup file. -/
macro "cxsimp" : tactic => `(tactic|
  simp [Function.update_of_ne, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', hF, hP, hR₀,
    cxStage, valStage, cxBc, CxD.par, CxD.valOf, Fin.ext_iff])

set_option hygiene false in
macro "cxsimp" "at" h:ident : tactic => `(tactic|
  simp [Function.update_of_ne, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', hF, hP, hR₀,
    cxStage, valStage, cxBc, CxD.par, CxD.valOf, Fin.ext_iff] at $h:ident ⊢)

set_option hygiene false in
macro "cxnodup" : tactic => `(tactic|
  simp [List.nodup_cons, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', Fin.ext_iff])

/-- Sequencing a register-by-register multiplication. -/
lemma cx_then_umulU {p : Pr P T Q A U}
    {s : IntegerMultBounds.MathlibTM2.Stack.Store (HΓ (T := T) A) (HS T Q A U)} {m : ℕ}
    {v₁ : HS T Q A U} {S₁ : Stacks T A} (he : Exec body p s m (mk v₁ S₁)) {a b c t₁ t₂ : Fin T}
    (hreg : [a, b, c, t₁, t₂].Nodup) (ht₁ : S₁.R t₁ = []) (ht₂ : S₁.R t₂ = []) :
    ∃ (v₂ : HS T Q A U) (m₂ : ℕ), v₂.user = v₁.user ∧
      m₂ ≤ (S₁.R a).length * (4 * (S₁.R b).length + 9) + 4 ∧
      Exec body (.seq p (umulU a b c t₁ t₂)) s (m + m₂)
        (mk v₂ { S₁ with
          R := Function.update S₁.R c
            (List.replicate ((S₁.R a).length * (S₁.R b).length) tick ++ S₁.R c) }) := by
  obtain ⟨v₂, m₂, hu, hm, he₂⟩ := umulU_exec body hreg v₁ S₁ ht₁ ht₂
  exact ⟨v₂, m₂, hu, hm, Exec.seq he he₂⟩

/-- Sequencing the removal of the top symbol of a register. -/
lemma cx_then_popTop {p : Pr P T Q A U}
    {s : IntegerMultBounds.MathlibTM2.Stack.Store (HΓ (T := T) A) (HS T Q A U)} {m : ℕ}
    {v₁ : HS T Q A U} {S₁ : Stacks T A} (he : Exec body p s m (mk v₁ S₁)) (r : Fin T) :
    Exec body (.seq p (.act (popTop r))) s (m + 1)
      (mk v₁ { S₁ with R := Function.update S₁.R r (S₁.R r).tail }) := by
  have h := Exec.seq he (Exec.act (body := body) (popTop r) (mk v₁ S₁))
  rwa [popTop_run] at h

variable {d : CxD} {R₀ : Fin T → List (Fin (A + 4))}

/-- The register built by a setup stage of the machine itself. -/
def cxOfStage : ℕ → CXReg
  | 1 => .val .nn | 2 => .val .nGa | 3 => .val .nGb | 4 => .val .L | 5 => .val .ρa
  | 6 => .val .ρb | 7 => .val .ρc | 8 => .val .Ka | 9 => .val .Kb | 10 => .val .Ga
  | 11 => .val .Gb | 12 => .val .padKG | 13 => .val .padK | 14 => .val .padG
  | 33 => .mselC | 34 => .mD | 35 => .mG | 36 => .mtopC | 37 => .padR
  | s => if h : 16 ≤ s ∧ s ≤ 26 then .fld ⟨s - 16, by omega⟩
      else if h' : 27 ≤ s ∧ s ≤ 32 then .kf ⟨s - 27, by omega⟩ else .comp

lemma cxOfStage_stage (x : CXReg) (hx : cxStage x ≠ 0) (hx15 : cxStage x ≠ 15) :
    cxOfStage (cxStage x) = x := by
  cases x with
  | val i => cases i <;> first | rfl | exact absurd rfl hx
  | sx r =>
      exfalso
      simp only [cxStage] at hx hx15
      split_ifs at hx hx15 <;> simp_all
  | fld g =>
      simp only [cxStage]
      rw [cxOfStage.eq_def]
      have := g.isLt
      split
      all_goals first | omega | skip
      rw [dif_pos (by omega)]
      congr 1
      exact Fin.ext (by simp)
  | kf j =>
      simp only [cxStage] at hx hx15 ⊢
      split_ifs at hx hx15 ⊢ with hj
      · rw [cxOfStage.eq_def]
        have := j.isLt
        split
        all_goals first | omega | skip
        rw [dif_neg (by omega), dif_pos (by omega)]
        congr 1
        exact Fin.ext (by simp)
      · exact absurd rfl hx
  | _ => first | rfl | exact absurd rfl hx

/-- A stage register is unique at its stage. -/
lemma cxStage_uniq {x y : CXReg} (hx : cxStage x ≠ 0) (hx15 : cxStage x ≠ 15)
    (h : cxStage y = cxStage x) : y = x := by
  rw [← cxOfStage_stage y (h ▸ hx) (h ▸ hx15), h, cxOfStage_stage x hx hx15]

lemma cxStageCost_ne (d : CxD) {s : ℕ} (hs : s ≠ 15) : cxStageCost d s = cxUnit d := by
  simp [cxStageCost, hs]

/-- A stage whose program takes the file after stage `s` to the file after stage `s + 1`. -/
lemma stage_of_exec (henv : CxEnv ι par src) {s : ℕ} {x : CXReg} (hx : cxStage x = s + 1)
    (hx15 : s + 1 ≠ 15) {p : Pr P T Q A U} {c : ℕ} (hc : c ≤ cxUnit d)
    (hrun : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = cxFill ι (cxBc A d) s R₀ →
      ∃ (v' : HS T Q A U) (m : ℕ) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧ m ≤ c ∧
        Exec body p (mk v S) m (mk v' { S with R := R' }) ∧ R' (ι x) = cxBc A d x ∧
        ∀ t, t ≠ ι x → R' t = S.R t) :
    ∀ (v : HS T Q A U) (S : Stacks T A), S.R = cxFill ι (cxBc A d) s R₀ →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxStageCost d (s + 1) ∧
        Exec body p (mk v S) m (mk v' { S with R := cxFill ι (cxBc A d) (s + 1) R₀ }) := by
  intro v S hS
  obtain ⟨v', m, R', hu, hm, he, h₁, h₂⟩ := hrun v S hS
  refine ⟨v', m, hu, by rw [cxStageCost_ne d hx15]; exact hm.trans hc, Exec.cast he rfl ?_⟩
  congr 2
  exact cx_finish2 henv hS hx (fun y hy => cxStage_uniq (by omega) (by omega) (hy.trans hx.symm))
    h₁ h₂

/-- A copy stage: `x` gains a copy of `a` through the empty `ts 0`. -/
lemma stage_copy (henv : CxEnv ι par src) {s : ℕ} {x : CXReg} (hx : cxStage x = s + 1)
    (hx15 : s + 1 ≠ 15) {a : Fin T} (hax : a ≠ ι x) (ha0 : a ≠ ι (.ts 0)) (hx0 : x ≠ .ts 0)
    {val : ℕ} (hav : ∀ S : Stacks T A, S.R = cxFill ι (cxBc A d) s R₀ → (S.R a).length = val)
    (hbc : cxBc A d x = List.replicate val tick) (hc : 4 * val + 4 ≤ cxUnit d) :
    ∀ (v : HS T Q A U) (S : Stacks T A), S.R = cxFill ι (cxBc A d) s R₀ →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxStageCost d (s + 1) ∧
        Exec body (ucopy a (ι x) (ι (.ts 0))) (mk v S) m
          (mk v' { S with R := cxFill ι (cxBc A d) (s + 1) R₀ }) := by
  refine stage_of_exec body henv hx hx15 hc fun v S hS => ?_
  have hF := henv.fill_ι hS
  have ht0 : S.R (ι (.ts 0)) = [] := by rw [hF]; simp [cxStage, cxBc]
  have hxe : S.R (ι x) = [] := by rw [hF, if_neg (by omega)]
  obtain ⟨v', hu, he⟩ := ucopy_exec body hax ha0 (henv.ne hx0) v S ht0
  refine ⟨v', _, _, hu, by rw [hav S hS], he, ?_, fun t ht => Function.update_of_ne ht _ _⟩
  rw [Function.update_self, hav S hS, hxe, hbc, List.append_nil]

/-- A zero-fill stage: `x` gains `|a|` zero bits through the empty `ts 1`. -/
lemma stage_zero (henv : CxEnv ι par src) {s : ℕ} {x : CXReg} (hx : cxStage x = s + 1)
    (hx15 : s + 1 ≠ 15) {a : Fin T} (hax : a ≠ ι x) (ha1 : a ≠ ι (.ts 1)) (hx1 : x ≠ .ts 1)
    {val : ℕ} (hav : ∀ S : Stacks T A, S.R = cxFill ι (cxBc A d) s R₀ → (S.R a).length = val)
    (hbc : cxBc A d x = binSyms val 0) (hc : 4 * val + 4 ≤ cxUnit d) :
    ∀ (v : HS T Q A U) (S : Stacks T A), S.R = cxFill ι (cxBc A d) s R₀ →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxStageCost d (s + 1) ∧
        Exec body (zeroBits a (ι x) (ι (.ts 1))) (mk v S) m
          (mk v' { S with R := cxFill ι (cxBc A d) (s + 1) R₀ }) := by
  refine stage_of_exec body henv hx hx15 hc fun v S hS => ?_
  have hF := henv.fill_ι hS
  have ht1 : S.R (ι (.ts 1)) = [] := by rw [hF]; simp [cxStage, cxBc]
  have hxe : S.R (ι x) = [] := by rw [hF, if_neg (by omega)]
  obtain ⟨v', hu, he⟩ := zeroBits_exec body hax ha1 (henv.ne hx1) v S ht1
  refine ⟨v', _, _, hu, by rw [hav S hS], he, ?_, fun t ht => Function.update_of_ne ht _ _⟩
  rw [Function.update_self, hav S hS, hxe, hbc, List.append_nil]

/-- A copy-and-pop stage: `x` gains `|a| - 1` ticks. -/
lemma stage_copy_pop (henv : CxEnv ι par src) {s : ℕ} {x : CXReg} (hx : cxStage x = s + 1)
    (hx15 : s + 1 ≠ 15) {a : Fin T} (hax : a ≠ ι x) (ha0 : a ≠ ι (.ts 0)) (hx0 : x ≠ .ts 0)
    {val : ℕ} (hav : ∀ S : Stacks T A, S.R = cxFill ι (cxBc A d) s R₀ → (S.R a).length = val)
    (hbc : cxBc A d x = List.replicate (val - 1) tick) (hc : 4 * val + 5 ≤ cxUnit d) :
    ∀ (v : HS T Q A U) (S : Stacks T A), S.R = cxFill ι (cxBc A d) s R₀ →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxStageCost d (s + 1) ∧
        Exec body (.seq (ucopy a (ι x) (ι (.ts 0))) (.act (popTop (ι x)))) (mk v S) m
          (mk v' { S with R := cxFill ι (cxBc A d) (s + 1) R₀ }) := by
  refine stage_of_exec body henv hx hx15 hc fun v S hS => ?_
  have hF := henv.fill_ι hS
  have ht0 : S.R (ι (.ts 0)) = [] := by rw [hF]; simp [cxStage, cxBc]
  have hxe : S.R (ι x) = [] := by rw [hF, if_neg (by omega)]
  obtain ⟨v', hu, he⟩ := ucopy_exec body hax ha0 (henv.ne hx0) v S ht0
  have he₂ := Exec.act (body := body) (popTop (ι x)) (mk v'
    { S with R := Function.update S.R (ι x) (List.replicate (S.R a).length tick ++ S.R (ι x)) })
  rw [popTop_run] at he₂
  refine ⟨v', _, _, hu, by rw [hav S hS], Exec.seq he he₂, ?_,
    fun t ht => by simp only [Function.update_of_ne ht]⟩
  simp only [Function.update_self, Function.update_idem, hav S hS, hxe, List.append_nil,
    List.tail_replicate, hbc]

lemma cxUnit_ge (d : CxD) : 60 * (d.L + d.K + d.G + d.n + d.a₀ + d.bB + d.rb + d.nG + d.k + d.ρ) +
    200 ≤ cxUnit d := by
  unfold cxUnit; omega

/-- Stages `1` to `14`: the value pool. -/
lemma cxStage_pool (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hG : 1 ≤ d.G) (hGK : d.G + 1 ≤ d.K) (s : ℕ) (hs : s < 14) :
    CxStageSpec body ι par d R₀ s := by
  have hunit := cxUnit_ge d
  interval_cases s
  · -- stage 1: `nn = k - 1`
    exact stage_copy_pop body henv (x := .val .nn) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.k) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · -- stage 2: `nG = nn * G`
    refine stage_of_exec body henv (x := .val .nGa) rfl (by decide) (c := d.nn * (4 * d.G + 9) + 4)
      (by unfold cxUnit; nlinarith) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    obtain ⟨v', m, hu, hm, he⟩ := umulU_exec body (a := ι (.val .nn)) (b := par .G)
      (c := ι (.val .nGa)) (t₁ := ι (.ts 0)) (t₂ := ι (.ts 1)) (by simp [henv.hι.eq_iff, henv.hpι, henv.hpι', Fin.ext_iff]) v S
      (by rw [hF]; simp [cxStage, cxBc]) (by rw [hF]; simp [cxStage, cxBc])
    refine ⟨v', m, _, hu, ?_, he, ?_, fun t ht => Function.update_of_ne ht _ _⟩
    · have h1 : (S.R (ι (.val .nn))).length = d.nn := by cxsimp
      have h2 : (S.R (par .G)).length = d.G := by cxsimp
      rw [h1, h2] at hm; exact hm
    · rw [Function.update_self]
      have h1 : S.R (ι (.val .nn)) = List.replicate d.nn tick := by cxsimp
      have h2 : (S.R (par .G)).length = d.G := by cxsimp
      have h3 : S.R (ι (.val .nGa)) = [] := by cxsimp
      rw [h1, h2, h3, List.length_replicate, List.append_nil]; rfl
  · -- stage 3: `nGb`
    exact stage_copy body henv (x := .val .nGb) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.nG) (fun S hS => by have hF := henv.fill_ι hS; have hP := henv.fill_par hS; cxsimp)
      rfl (by omega)
  · exact stage_copy body henv (x := .val .L) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.L) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_copy body henv (x := .val .ρa) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.ρ) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_copy body henv (x := .val .ρb) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.ρ) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_copy body henv (x := .val .ρc) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.ρ) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_copy body henv (x := .val .Ka) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.K) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_copy body henv (x := .val .Kb) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.K) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_copy body henv (x := .val .Ga) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.G) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_copy body henv (x := .val .Gb) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.G) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · -- stage 12: `K - 1 - G`
    refine stage_of_exec body henv (x := .val .padKG) rfl (by decide)
      (c := 4 * d.K + 4 + 1 + (4 * d.G + 4)) (by omega) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have hxe : S.R (ι (.val .padKG)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .K) (b := ι (.val .padKG)) (t := ι (.ts 0))
      (by cxne) (by cxne) (by cxne) v S ht0
    have he₂ := Exec.act (body := body) (popTop (ι (.val .padKG)))
      (mk v₁ { S with
        R := Function.update S.R (ι (.val .padKG))
              (List.replicate (S.R (par .K)).length tick ++ S.R (ι (.val .padKG))) })
    rw [popTop_run] at he₂
    obtain ⟨v₃, hu₃, he₃⟩ := sx_then_usub body (Exec.seq he₁ he₂) (a := par .G)
      (b := ι (.val .padKG)) (t := ι (.ts 0)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    refine ⟨v₃, _, _, by rw [hu₃, hu₁], ?_, he₃, ?_, fun t ht => by
      simp only [Function.update_of_ne ht]⟩
    · have h1 : (S.R (par .K)).length = d.K := by cxsimp
      have h2 : (S.R (par .G)).length = d.G := by cxsimp
      simp only [Function.update_of_ne (henv.hpι' CXPar.G (CXReg.val CXVal.padKG)), h1, h2,
        le_refl]
    · have h1 : (S.R (par .K)).length = d.K := by cxsimp
      have h2 : (S.R (par .G)).length = d.G := by cxsimp
      simp only [Function.update_self, Function.update_idem, h1, hxe, List.append_nil,
        List.tail_replicate, List.drop_replicate, cxBc, CxD.valOf,
        Function.update_of_ne (henv.hpι' CXPar.G (CXReg.val CXVal.padKG)), h2]
  · exact stage_copy_pop body henv (x := .val .padK) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.K) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_copy_pop body henv (x := .val .padG) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.G) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)


/-- The interchange environment of the old registers and the derived parameters. -/
lemma cxSxEnv (henv : CxEnv ι par src) : SxEnv (sxι ι) (parSx ι par) where
  hι := fun a b h => by have := henv.hι h; simpa [CXReg.sx.injEq] using this
  hpar := fun p q h => by
    cases p <;> cases q <;> simp_all [parSx, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι,
      henv.hpι']
  hpι := fun x p => by cases p <;> simp [parSx, sxι, henv.hι.eq_iff, henv.hpι]

/-- The interchange data is valid. -/
lemma swapD_valid (hv : d.Valid) : d.swapD.Valid where
  hρ := by
    show 0 < d.nG
    unfold CxD.nG CxD.nn
    have := hv.hk; have := hv.hG
    exact Nat.mul_pos (by omega) (by omega)
  hLK := by show d.nG = d.nG * 1; ring
  hk := le_rfl
  hR := hv.hR
  hrw := hv.hrw
  hxy := by show d.pU ≠ d.pT; have := hv.hpTU; omega
  hxz := by show d.pU ≠ 0; have := hv.hpTU; omega
  hyz := by show d.pT ≠ 0; have := hv.hpT; omega
  hfit := by
    show d.bB + (sxPos d.pU d.pT 0 0 + 1) * d.nG ≤ d.n
    have hpos : sxPos d.pU d.pT 0 0 = d.pU := by
      have h1 := hv.hpT; have h2 := hv.hpTU
      unfold sxPos sxSigma
      rw [if_pos ⟨h2, by omega⟩]
      rfl
    rw [hpos]
    have := hv.hUn
    unfold CxD.bU at this
    rw [Nat.add_mul, one_mul] at *
    omega

/-- The positions of the chunks of the interchange rectangle. -/
lemma swapD_pos (hv : d.Valid) :
    sxPos d.pU d.pT 0 0 = d.pU ∧ sxPos d.pU d.pT 0 1 = d.pT ∧ sxPos d.pU d.pT 0 2 = 0 := by
  have h1 := hv.hpT; have h2 := hv.hpTU
  unfold sxPos sxSigma
  rw [if_pos ⟨h2, by omega⟩]
  exact ⟨rfl, rfl, rfl⟩

/-- The registers at a stage of the interchange setup. -/
lemma cxGap_regs (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p) {s : ℕ}
    {S : Stacks T A} (hS : S.R = sxFill (sxι ι) (sxBc A d.swapD) s (cxFill ι (cxBc A d) 14 R₀)) :
    (∀ x : SXReg, S.R (ι (.sx x)) = if sxStage x ≤ s then sxBc A d.swapD x else []) ∧
      (∀ p, (S.R (par p)).length = d.par p) ∧
      S.R (ι (.val .nGa)) = List.replicate d.nG tick := by
  refine ⟨fun x => ?_, fun p => ?_, ?_⟩
  · rw [hS]; exact sxFill_ι (cxSxEnv henv).hι _ _ _ x
  · rw [hS, sxFill_out (ι := sxι ι) _ _ _ (fun x => henv.hpι (.sx x) p),
      cxFill_out _ _ _ (fun x => henv.hpι x p), hR₀]
  · rw [hS, sxFill_out (ι := sxι ι) _ _ _ (fun x => henv.ne (by simp)), cxFill_ι henv.hι]
    simp [cxStage, valStage, cxBc, CxD.valOf]

variable (ι par) in
/-- The specification of stage `s + 1` of the interchange setup. -/
def CxGapSpec (d : CxD) (R₀ : Fin T → List (Fin (A + 4))) (s : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A),
    S.R = sxFill (sxι ι) (sxBc A d.swapD) s (cxFill ι (cxBc A d) 14 R₀) →
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxGapCost d (s + 1) ∧
      Exec body (cxGapProg ι par d (s + 1)) (mk v S) m
        (mk v' { S with R := sxFill (sxι ι) (sxBc A d.swapD) (s + 1) (cxFill ι (cxBc A d) 14 R₀) })

set_option hygiene false in
macro "gapsimp" : tactic => `(tactic|
  simp [Function.update_of_ne, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', hF, hP, hG,
    sxStage, sxBc, CxD.par, CxD.swapD, SxD.n3, SxD.n2, SxD.n1, SxD.n0, sxN3, sxN2, sxN1, sxN0,
    hp0, hp1, hp2, sxι, Fin.ext_iff, List.drop_replicate, List.tail_replicate,
    List.replicate_append_replicate])

set_option hygiene false in
macro "gapsimp" "at" h:ident : tactic => `(tactic|
  simp [Function.update_of_ne, henv.hι.eq_iff, henv.hpar.eq_iff, henv.hpι, henv.hpι', hF, hP, hG,
    sxStage, sxBc, CxD.par, CxD.swapD, SxD.n3, SxD.n2, SxD.n1, SxD.n0, sxN3, sxN2, sxN1, sxN0,
    hp0, hp1, hp2, sxι, Fin.ext_iff, List.drop_replicate, List.tail_replicate,
    List.replicate_append_replicate] at $h:ident ⊢)

lemma cxGap_1 (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : CxGapSpec body ι par d R₀ 0 := by
  intro v S hS
  obtain ⟨hF, hP, hG⟩ := cxGap_regs henv hR₀ hS
  obtain ⟨hp0, hp1, hp2⟩ := swapD_pos hv
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .bB) (b := ι (.sx .n3))
    (t := ι (.sx (.sc 0))) (by cxne) (by cxne) (by cxne) v S (by gapsimp)
  refine ⟨v₁, _, hu₁, ?_, Exec.cast he₁ rfl ?_⟩
  · simp only [cxGapCost]; gapsimp
  · congr 2
    refine sx_finish2 (cxSxEnv henv) hS (x := .n3) rfl ?_ ?_
    · gapsimp
    · intro t ht; exact Function.update_of_ne ht _ _

lemma cxGap_2 (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : CxGapSpec body ι par d R₀ 1 := by
  intro v S hS
  obtain ⟨hF, hP, hG⟩ := cxGap_regs henv hR₀ hS
  obtain ⟨hp0, hp1, hp2⟩ := swapD_pos hv
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .pT) (b := ι (.sx (.sc 1)))
    (t := ι (.sx (.sc 0))) (by cxne) (by cxne) (by cxne) v S (by gapsimp)
  have he₂ := cx_then_popTop body he₁ (ι (.sx (.sc 1)))
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := cx_then_umulU body he₂ (a := ι (.sx (.sc 1)))
    (b := ι (.val .nGa)) (c := ι (.sx .n2)) (t₁ := ι (.sx (.sc 0))) (t₂ := ι (.sx (.sc 2)))
    (by cxnodup) (by gapsimp) (by gapsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_uclear body he₃ (ι (.sx (.sc 1)))
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₁], ?_, Exec.cast he₄ rfl ?_⟩
  · simp only [cxGapCost]
    gapsimp at hm₃
    have : (d.pT - 1) * (4 * d.nG + 9) ≤ d.pT * (4 * d.nG + 9) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · congr 2
    refine sx_finish2 (cxSxEnv henv) hS (x := .n2) rfl ?_ ?_
    · gapsimp
    · intro t ht
      have ht' : t ≠ ι (.sx .n2) := ht
      by_cases h1 : t = ι (.sx (.sc 1))
      · subst h1; gapsimp
      · simp [Function.update_of_ne h1, Function.update_of_ne ht']

lemma cxGap_3 (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : CxGapSpec body ι par d R₀ 2 := by
  intro v S hS
  obtain ⟨hF, hP, hG⟩ := cxGap_regs henv hR₀ hS
  obtain ⟨hp0, hp1, hp2⟩ := swapD_pos hv
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .pU) (b := ι (.sx (.sc 1)))
    (t := ι (.sx (.sc 0))) (by cxne) (by cxne) (by cxne) v S (by gapsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := par .pT) (b := ι (.sx (.sc 1)))
    (t := ι (.sx (.sc 0))) (by cxne) (by cxne) (by cxne) (by gapsimp)
  have he₃ := cx_then_popTop body he₂ (ι (.sx (.sc 1)))
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := cx_then_umulU body he₃ (a := ι (.sx (.sc 1)))
    (b := ι (.val .nGa)) (c := ι (.sx .n1)) (t₁ := ι (.sx (.sc 0))) (t₂ := ι (.sx (.sc 2)))
    (by cxnodup) (by gapsimp) (by gapsimp)
  obtain ⟨v₅, hu₅, he₅⟩ := sx_then_uclear body he₄ (ι (.sx (.sc 1)))
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
  · simp only [cxGapCost]
    gapsimp at hm₄
    have : (d.pU - d.pT - 1) * (4 * d.nG + 9) ≤ d.pU * (4 * d.nG + 9) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · congr 2
    refine sx_finish2 (cxSxEnv henv) hS (x := .n1) rfl ?_ ?_
    · gapsimp
    · intro t ht
      have ht' : t ≠ ι (.sx .n1) := ht
      by_cases h1 : t = ι (.sx (.sc 1))
      · subst h1; gapsimp
      · simp [Function.update_of_ne h1, Function.update_of_ne ht']

lemma cxGap_4 (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : CxGapSpec body ι par d R₀ 3 := by
  intro v S hS
  obtain ⟨hF, hP, hG⟩ := cxGap_regs henv hR₀ hS
  obtain ⟨hp0, hp1, hp2⟩ := swapD_pos hv
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .n) (b := ι (.sx .n0))
    (t := ι (.sx (.sc 0))) (by cxne) (by cxne) (by cxne) v S (by gapsimp)
  obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := par .bB) (b := ι (.sx .n0))
    (t := ι (.sx (.sc 0))) (by cxne) (by cxne) (by cxne) (by gapsimp)
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := cx_then_umulU body he₂ (a := par .pU)
    (b := ι (.val .nGa)) (c := ι (.sx (.sc 1))) (t₁ := ι (.sx (.sc 0))) (t₂ := ι (.sx (.sc 2)))
    (by cxnodup) (by gapsimp) (by gapsimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_ucopy body he₃ (a := ι (.val .nGa)) (b := ι (.sx (.sc 1)))
    (t := ι (.sx (.sc 0))) (by cxne) (by cxne) (by cxne) (by gapsimp)
  obtain ⟨v₅, hu₅, he₅⟩ := sx_then_usub body he₄ (a := ι (.sx (.sc 1))) (b := ι (.sx .n0))
    (t := ι (.sx (.sc 0))) (by cxne) (by cxne) (by cxne) (by gapsimp)
  obtain ⟨v₆, hu₆, he₆⟩ := sx_then_uclear body he₅ (ι (.sx (.sc 1)))
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₆ rfl ?_⟩
  · simp only [cxGapCost]
    gapsimp at hm₃
    rw [Nat.add_mul, one_mul]
    omega
  · congr 2
    refine sx_finish2 (cxSxEnv henv) hS (x := .n0) rfl ?_ ?_
    · gapsimp
      rw [Nat.add_mul, one_mul]
      omega
    · intro t ht
      have ht' : t ≠ ι (.sx .n0) := ht
      by_cases h1 : t = ι (.sx (.sc 1))
      · subst h1; gapsimp
      · simp [Function.update_of_ne h1, Function.update_of_ne ht']

/-- Every stage of the interchange setup. -/
lemma cxGap_all (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : ∀ s < 38, CxGapSpec body ι par d R₀ s := by
  intro s hs
  rcases Nat.lt_or_ge s 4 with h | h
  · interval_cases s
    exacts [cxGap_1 body henv hR₀ hv, cxGap_2 body henv hR₀ hv, cxGap_3 body henv hR₀ hv,
      cxGap_4 body henv hR₀ hv]
  · have hsx := cxSxEnv henv
    have hR₀' : ∀ p, ((cxFill ι (cxBc A d) 14 R₀) (parSx ι par p)).length = d.swapD.par p :=
      fun p => by
        cases p <;> simp only [parSx, SxD.par, CxD.swapD] <;>
          first
          | (rw [cxFill_out _ _ _ (fun x => henv.hpι x _), hR₀]; rfl)
          | (rw [cxFill_ι henv.hι]; simp [cxStage, valStage, cxBc, CxD.valOf])
    have hspec := sxStage_all body hsx hR₀' (swapD_valid hv) s hs
    intro v S hS
    obtain ⟨v', m, hu, hm, he⟩ := hspec v S hS
    interval_cases s <;> exact ⟨v', m, hu, hm, he⟩

/-- Stage `15`: the interchange setup. -/
lemma cxStage_15 (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : CxStageSpec body ι par d R₀ 14 := by
  intro v S hS
  have hall := cxGap_all body henv hR₀ hv
  have hsx := cxSxEnv henv
  have h0 : ∀ x, cxFill ι (cxBc A d) 14 R₀ (sxι ι x) = [] := fun x => by
    rw [show sxι ι x = ι (CXReg.sx x) from rfl, cxFill_ι henv.hι]
    simp only [cxStage]
    split_ifs with h1 h2 <;> first | omega | rfl | exact cxBc_zero A d _ (by simp [cxStage, h1])
  obtain ⟨v', m, hu, hm, he⟩ := sx_chain_exec body
    (fun i => sxFill (sxι ι) (sxBc A d.swapD) i (cxFill ι (cxBc A d) 14 R₀))
    (fun i => cxGapProg ι par d (i + 1)) (fun i => cxGapCost d (i + 1)) 38 0
    (fun i hi v S hS => by simpa using hall i hi v S (by simpa using hS)) v S
    (by rw [hS, sxFill_zero hsx.hι _ _ h0 (sxBc_zero A d.swapD)])
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · simpa [cxStageCost] using hm
  · congr 2
    exact cxFill_sx henv.hι d R₀

/-- A zero-fill stage whose length is first assembled in `ts 0`. -/
lemma stage_zero_via (henv : CxEnv ι par src) {s : ℕ} {x : CXReg} (hx : cxStage x = s + 1)
    (hx15 : s + 1 ≠ 15) (hx0 : x ≠ .ts 0) (hx1 : x ≠ .ts 1) {p : Pr P T Q A U} {c₀ val : ℕ}
    (hbc : cxBc A d x = binSyms val 0) (hc : c₀ + (4 * val + 4) + (2 * val + 2) ≤ cxUnit d)
    (hprog : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = cxFill ι (cxBc A d) s R₀ →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c₀ ∧
        Exec body p (mk v S) m
          (mk v' { S with R := Function.update S.R (ι (.ts 0)) (List.replicate val tick) })) :
    ∀ (v : HS T Q A U) (S : Stacks T A), S.R = cxFill ι (cxBc A d) s R₀ →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxStageCost d (s + 1) ∧
        Exec body (.seq p (.seq (zeroBits (ι (.ts 0)) (ι x) (ι (.ts 1))) (uclear (ι (.ts 0)))))
          (mk v S) m (mk v' { S with R := cxFill ι (cxBc A d) (s + 1) R₀ }) := by
  refine stage_of_exec body henv hx hx15 hc fun v S hS => ?_
  have hF := henv.fill_ι hS
  have ht1 : S.R (ι (.ts 1)) = [] := by rw [hF]; simp [cxStage, cxBc]
  have hxe : S.R (ι x) = [] := by rw [hF, if_neg (by omega)]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := hprog v S hS
  have h01 : ι (.ts 0) ≠ ι (.ts 1) := henv.ne (by simp [Fin.ext_iff])
  obtain ⟨v₂, hu₂, he₂⟩ := zeroBits_exec body (henv.ne hx0.symm) h01 (henv.ne hx1) v₁
    { S with R := Function.update S.R (ι (.ts 0)) (List.replicate val tick) }
    (by show Function.update S.R (ι (.ts 0)) _ (ι (.ts 1)) = []; rw [Function.update_of_ne h01.symm, ht1])
  set R₁ := Function.update S.R (ι (.ts 0)) (List.replicate val tick) with hR₁
  have hR₁0 : R₁ (ι (.ts 0)) = List.replicate val tick := by rw [hR₁, Function.update_self]
  have hR₁x : R₁ (ι x) = [] := by rw [hR₁, Function.update_of_ne (henv.ne hx0), hxe]
  set R₂ := Function.update R₁ (ι x) (binSyms (R₁ (ι (.ts 0))).length 0 ++ R₁ (ι x)) with hR₂
  have hR₂0 : R₂ (ι (.ts 0)) = List.replicate val tick := by
    rw [hR₂, Function.update_of_ne (henv.ne hx0).symm, hR₁0]
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (ι (.ts 0)) v₂ { S with R := R₂ }
  refine ⟨v₃, _, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.seq he₁ (Exec.seq he₂ he₃), ?_, ?_⟩
  · show m₁ + (4 * (R₁ (ι (.ts 0))).length + 4 + (2 * (R₂ (ι (.ts 0))).length + 2)) ≤ _
    rw [hR₁0, hR₂0, List.length_replicate]
    omega
  · show Function.update R₂ (ι (.ts 0)) [] (ι x) = _
    rw [Function.update_of_ne (henv.ne hx0), hR₂, Function.update_self, hR₁0, hR₁x,
      List.length_replicate, List.append_nil, hbc]
  · intro t ht
    show Function.update R₂ (ι (.ts 0)) [] t = S.R t
    by_cases ht0 : t = ι (.ts 0)
    · subst ht0
      rw [Function.update_self, hF]
      simp [cxStage, cxBc]
    · rw [Function.update_of_ne ht0, hR₂, Function.update_of_ne ht, hR₁,
        Function.update_of_ne ht0]


/-- The products of the field lengths are bounded by `n`. -/
lemma CxD.Valid.prods (hv : d.Valid) :
    (d.hi + 1) * d.L ≤ d.n ∧ d.lo * d.L ≤ d.n ∧ (d.hi - d.lo - 1) * d.L ≤ d.n ∧
      d.pT * d.nG ≤ d.n ∧ (d.pU + 1) * d.nG ≤ d.n ∧ (d.pU - d.pT - 1) * d.nG ≤ d.n ∧
      d.bT ≤ d.n ∧ d.bU ≤ d.n ∧ d.nG ≤ d.L := by
  have h1 := hv.hhiT; have h2 := hv.hUn; have h3 := hv.hpTU; have h4 := hv.hBlo
  have hbT : d.bT ≤ d.bU := by
    unfold CxD.bT CxD.bU
    have := Nat.mul_le_mul_right d.nG h3.le
    omega
  have hnG : d.nG ≤ d.L := by
    have h1 := hv.hLK; have h2 := hv.hGK; have h3 := hv.hk
    unfold CxD.nG CxD.nn
    rw [h1]
    calc (d.k - 1) * d.G ≤ d.k * d.K := Nat.mul_le_mul (by omega) (by omega)
      _ = d.K * d.k := by ring
  have hhi : (d.hi + 1) * d.L ≤ d.n := by unfold CxD.bT at *; omega
  have hlo : d.lo * d.L ≤ d.n := by
    have : d.lo * d.L ≤ (d.hi + 1) * d.L := Nat.mul_le_mul_right _ (by unfold CxD.lo CxD.hi; omega)
    omega
  have h4' : (d.hi - d.lo - 1) * d.L ≤ d.n := by
    have : (d.hi - d.lo - 1) * d.L ≤ (d.hi + 1) * d.L := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpU : (d.pU + 1) * d.nG ≤ d.n := by unfold CxD.bU at h2; rw [Nat.add_mul, one_mul]; omega
  have hpT : d.pT * d.nG ≤ d.n := by
    have : d.pT * d.nG ≤ (d.pU + 1) * d.nG := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpUT : (d.pU - d.pT - 1) * d.nG ≤ d.n := by
    have : (d.pU - d.pT - 1) * d.nG ≤ (d.pU + 1) * d.nG := Nat.mul_le_mul_right _ (by omega)
    omega
  have hbUn : d.bU ≤ d.n := by unfold CxD.bU at h2 ⊢; omega
  exact ⟨hhi, hlo, h4', hpT, hpU, hpUT, hbT.trans hbUn, hbUn, hnG⟩

/-- Stages `16` to `26`: the eleven field registers. -/
lemma cxStage_fld (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) (s : ℕ) (hs : 15 ≤ s) (hs' : s < 26) :
    CxStageSpec body ι par d R₀ s := by
  have hunit := cxUnit_ge d
  obtain ⟨hhi, hlo, h4, hpT, hpU, hpUT, hbT, hbU, hnG⟩ := hv.prods
  have hBlo := hv.hBlo
  have hhiT := hv.hhiT
  have hUn := hv.hUn
  interval_cases s
  · -- `fld 0`: `bB` zeros
    exact stage_zero body henv (x := .fld 0) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.bB) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · exact stage_zero body henv (x := .fld 1) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.nG) (fun S hS => by have hF := henv.fill_ι hS; have hP := henv.fill_par hS; cxsimp)
      rfl (by omega)
  · -- `fld 2`: `a₀ + lo L - (bB + nG)` zeros
    refine stage_zero_via body henv (x := .fld 2) rfl (by decide) (by simp) (by simp)
      (c₀ := 4 * d.a₀ + 4 + (4 * d.L + 4) + (4 * d.bB + 4) + (4 * d.nG + 4))
      (val := d.a₀ + d.lo * d.L - (d.bB + d.nG)) rfl (by omega) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .a₀) (b := ι (.ts 0)) (t := ι (.ts 1))
      (by cxne) (by cxne) (by cxne) v S ht1
    obtain ⟨v₂, hu₂, he₂⟩ := sx_then_umul body he₁ d.lo (a := par .L) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₃, hu₃, he₃⟩ := sx_then_usub body he₂ (a := par .bB) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₄, hu₄, he₄⟩ := sx_then_usub body he₃ (a := ι (.val .nGa)) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₄ rfl ?_⟩
    · cxsimp
    · congr 2
      simp only [Function.update_idem, Function.update_self, ht0, List.append_nil]
      cxsimp
      have e : d.lo * d.L + d.a₀ - d.bB - d.nG = d.a₀ + d.lo * d.L - (d.bB + d.nG) := by omega
      rw [e]
  · exact stage_zero body henv (x := .fld 3) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.L) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · -- `fld 4`: `(hi - lo - 1) L` zeros
    refine stage_zero_via body henv (x := .fld 4) rfl (by decide) (by simp) (by simp)
      (c₀ := 4 * d.L + 4) (val := (d.hi - d.lo - 1) * d.L) rfl (by omega) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := umul_exec body (d.hi - d.lo - 1) (a := par .L) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) v S ht1
    refine ⟨v₁, _, hu₁, by cxsimp, Exec.cast he₁ rfl ?_⟩
    congr 2
    rw [ht0, List.append_nil]
    cxsimp
  · exact stage_zero body henv (x := .fld 5) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.L) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · -- `fld 6`: `bT - (a₀ + (hi + 1) L)` zeros
    refine stage_zero_via body henv (x := .fld 6) rfl (by decide) (by simp) (by simp)
      (c₀ := 4 * d.bB + 4 + (d.pT * (4 * d.nG + 9) + 4) + (4 * d.a₀ + 4) + (4 * d.L + 4) +
        (4 * ((d.hi + 1) * d.L) + 4) + (2 * ((d.hi + 1) * d.L) + 2))
      (val := d.bT - (d.a₀ + (d.hi + 1) * d.L)) rfl
      (by
        have hval : d.bT - (d.a₀ + (d.hi + 1) * d.L) ≤ d.n := le_trans (Nat.sub_le _ _) hbT
        unfold cxUnit; nlinarith)
      fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    have ht2 : S.R (ι (.ts 2)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .bB) (b := ι (.ts 0)) (t := ι (.ts 1))
      (by cxne) (by cxne) (by cxne) v S ht1
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := cx_then_umulU body he₁ (a := par .pT) (b := ι (.val .nGa))
      (c := ι (.ts 0)) (t₁ := ι (.ts 1)) (t₂ := ι (.ts 2)) (by cxnodup) (by cxsimp) (by cxsimp)
    obtain ⟨v₃, hu₃, he₃⟩ := sx_then_usub body he₂ (a := par .a₀) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₄, hu₄, he₄⟩ := sx_then_umul body he₃ (d.hi + 1) (a := par .L) (b := ι (.ts 2))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₅, hu₅, he₅⟩ := sx_then_usub body he₄ (a := ι (.ts 2)) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₆, hu₆, he₆⟩ := sx_then_uclear body he₅ (ι (.ts 2))
    refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₆ rfl ?_⟩
    · cxsimp at hm₂
      omega
    · congr 2
      funext t
      by_cases ht2' : t = ι (.ts 2)
      · subst ht2'
        rw [Function.update_self, Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])), ht2]
      · rw [Function.update_of_ne ht2']
        by_cases ht0' : t = ι (.ts 0)
        · subst ht0'
          simp only [Function.update_idem, Function.update_self, ht0, List.append_nil]
          cxsimp
          unfold CxD.bT
          omega
        · simp only [Function.update_of_ne ht0', Function.update_of_ne ht2']
  · exact stage_zero body henv (x := .fld 7) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.nG) (fun S hS => by have hF := henv.fill_ι hS; have hP := henv.fill_par hS; cxsimp)
      rfl (by omega)
  · -- `fld 8`: `(pU - pT - 1) nG` zeros
    refine stage_zero_via body henv (x := .fld 8) rfl (by decide) (by simp) (by simp)
      (c₀ := 4 * d.pU + 4 + (4 * d.pT + 4) + 1 + ((d.pU - d.pT - 1) * (4 * d.nG + 9) + 4) +
        (2 * (d.pU - d.pT - 1) + 2))
      (val := (d.pU - d.pT - 1) * d.nG) rfl
      (by
        have h1 : (d.pU - d.pT - 1) * (4 * d.nG + 9) ≤ d.pU * (4 * d.nG + 9) :=
          Nat.mul_le_mul_right _ (by omega)
        unfold cxUnit; nlinarith)
      fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    have ht2 : S.R (ι (.ts 2)) = [] := by cxsimp
    have ht3 : S.R (ι (.ts 3)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .pU) (b := ι (.ts 2)) (t := ι (.ts 1))
      (by cxne) (by cxne) (by cxne) v S ht1
    obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := par .pT) (b := ι (.ts 2))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    have he₃ := cx_then_popTop body he₂ (ι (.ts 2))
    obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := cx_then_umulU body he₃ (a := ι (.ts 2)) (b := ι (.val .nGa))
      (c := ι (.ts 0)) (t₁ := ι (.ts 1)) (t₂ := ι (.ts 3)) (by cxnodup) (by cxsimp) (by cxsimp)
    obtain ⟨v₅, hu₅, he₅⟩ := sx_then_uclear body he₄ (ι (.ts 2))
    refine ⟨v₅, _, by rw [hu₅, hu₄, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
    · cxsimp at hm₄
      omega
    · congr 2
      funext t
      by_cases ht2' : t = ι (.ts 2)
      · subst ht2'
        rw [Function.update_self, Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])), ht2]
      · rw [Function.update_of_ne ht2']
        by_cases ht0' : t = ι (.ts 0)
        · subst ht0'
          simp only [Function.update_idem, Function.update_self, ht0, List.append_nil]
          cxsimp
          try simp [ht2, List.drop_replicate, List.tail_replicate]
        · simp only [Function.update_of_ne ht0', Function.update_of_ne ht2']
  · exact stage_zero body henv (x := .fld 9) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.nG) (fun S hS => by have hF := henv.fill_ι hS; have hP := henv.fill_par hS; cxsimp)
      rfl (by omega)
  · -- `fld 10`: `n - (bU + nG)` zeros
    refine stage_zero_via body henv (x := .fld 10) rfl (by decide) (by simp) (by simp)
      (c₀ := 4 * d.n + 4 + (4 * d.bB + 4) + (d.pU * (4 * d.nG + 9) + 4) + (4 * d.nG + 4) +
        (4 * (d.nG + d.pU * d.nG) + 4) + (2 * (d.nG + d.pU * d.nG) + 2))
      (val := d.n - (d.bU + d.nG)) rfl
      (by
        rw [Nat.add_mul, one_mul] at hpU
        have hval : d.n - (d.bU + d.nG) ≤ d.n := Nat.sub_le _ _
        unfold cxUnit; nlinarith) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    have ht2 : S.R (ι (.ts 2)) = [] := by cxsimp
    have ht3 : S.R (ι (.ts 3)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .n) (b := ι (.ts 0)) (t := ι (.ts 1))
      (by cxne) (by cxne) (by cxne) v S ht1
    obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := par .bB) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := cx_then_umulU body he₂ (a := par .pU) (b := ι (.val .nGa))
      (c := ι (.ts 2)) (t₁ := ι (.ts 1)) (t₂ := ι (.ts 3)) (by cxnodup) (by cxsimp) (by cxsimp)
    obtain ⟨v₄, hu₄, he₄⟩ := sx_then_ucopy body he₃ (a := ι (.val .nGa)) (b := ι (.ts 2))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₅, hu₅, he₅⟩ := sx_then_usub body he₄ (a := ι (.ts 2)) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₆, hu₆, he₆⟩ := sx_then_uclear body he₅ (ι (.ts 2))
    refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₆ rfl ?_⟩
    · cxsimp at hm₃
      omega
    · congr 2
      funext t
      by_cases ht2' : t = ι (.ts 2)
      · subst ht2'
        rw [Function.update_self, Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])), ht2]
      · rw [Function.update_of_ne ht2']
        by_cases ht0' : t = ι (.ts 0)
        · subst ht0'
          simp only [Function.update_idem, Function.update_self, ht0, List.append_nil]
          cxsimp
          unfold CxD.bU
          rw [Nat.add_mul, one_mul] at hpU
          try simp [ht2, List.drop_replicate]
          omega
        · simp only [Function.update_of_ne ht0', Function.update_of_ne ht2']

/-- Stages `27` to `32`: the key fields. -/
lemma cxStage_kf (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) (s : ℕ) (hs : 26 ≤ s) (hs' : s < 32) :
    CxStageSpec body ι par d R₀ s := by
  have hunit := cxUnit_ge d
  obtain ⟨hhi, hlo, h4, hpT, hpU, hpUT, hbT, hbU, hnG⟩ := hv.prods
  interval_cases s
  · -- `kf 0`: `a₀ + lo L` zeros
    refine stage_zero_via body henv (x := .kf 0) rfl (by decide) (by simp) (by simp)
      (c₀ := 4 * d.a₀ + 4 + (4 * d.L + 4)) (val := d.a₀ + d.lo * d.L) rfl (by omega)
      fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .a₀) (b := ι (.ts 0)) (t := ι (.ts 1))
      (by cxne) (by cxne) (by cxne) v S ht1
    obtain ⟨v₂, hu₂, he₂⟩ := sx_then_umul body he₁ d.lo (a := par .L) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast he₂ rfl ?_⟩
    · cxsimp
    · congr 2
      simp only [Function.update_idem, Function.update_self, ht0, List.append_nil]
      cxsimp
      have e : d.lo * d.L + d.a₀ = d.a₀ + d.lo * d.L := by ring
      rw [e]
  · exact stage_zero body henv (x := .kf 1) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.L) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · -- `kf 2`
    refine stage_zero_via body henv (x := .kf 2) rfl (by decide) (by simp) (by simp)
      (c₀ := 4 * d.L + 4) (val := (d.hi - d.lo - 1) * d.L) rfl (by omega) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := umul_exec body (d.hi - d.lo - 1) (a := par .L) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) v S ht1
    refine ⟨v₁, _, hu₁, by cxsimp, Exec.cast he₁ rfl ?_⟩
    congr 2
    rw [ht0, List.append_nil]
    cxsimp
  · exact stage_zero body henv (x := .kf 3) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.L) (fun S hS => by have hP := henv.fill_par hS; rw [hP, hR₀]; rfl) rfl (by omega)
  · -- `kf 4`: `n - (a₀ + (hi + 1) L)` zeros
    refine stage_zero_via body henv (x := .kf 4) rfl (by decide) (by simp) (by simp)
      (c₀ := 4 * d.n + 4 + (4 * d.a₀ + 4) + (4 * d.L + 4) + (4 * ((d.hi + 1) * d.L) + 4) +
        (2 * ((d.hi + 1) * d.L) + 2))
      (val := d.n - (d.a₀ + (d.hi + 1) * d.L)) rfl (by omega) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    have ht2 : S.R (ι (.ts 2)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .n) (b := ι (.ts 0)) (t := ι (.ts 1))
      (by cxne) (by cxne) (by cxne) v S ht1
    obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := par .a₀) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₃, hu₃, he₃⟩ := sx_then_umul body he₂ (d.hi + 1) (a := par .L) (b := ι (.ts 2))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₄, hu₄, he₄⟩ := sx_then_usub body he₃ (a := ι (.ts 2)) (b := ι (.ts 0))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    obtain ⟨v₅, hu₅, he₅⟩ := sx_then_uclear body he₄ (ι (.ts 2))
    refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast he₅ rfl ?_⟩
    · cxsimp
    · congr 2
      funext t
      by_cases ht2' : t = ι (.ts 2)
      · subst ht2'
        rw [Function.update_self, Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])), ht2]
      · rw [Function.update_of_ne ht2']
        by_cases ht0' : t = ι (.ts 0)
        · subst ht0'
          simp only [Function.update_idem, Function.update_self, ht0, List.append_nil]
          cxsimp
          omega
        · simp only [Function.update_of_ne ht0', Function.update_of_ne ht2']
  · -- `kf 5`: the row bits
    exact stage_zero body henv (x := .kf 5) rfl (by decide) (by cxne) (by cxne) (by simp)
      (val := d.rb) (fun S hS => by
        have hF := henv.fill_ι hS
        rw [hF]
        simp [cxStage, cxBc, sxStage, sxBc, SxD.rb, CxD.swapD, CxD.rb]) rfl (by omega)

/-- The alternating mask at an item position. -/
lemma altMask_item (G L : ℕ) (hG : 1 ≤ G) (j s : ℕ) (hs : s < G + G) (ht : 0 + (G + G) * j + s < L) :
    (altMask G L).testBit (0 + (G + G) * j + s) = decide (G ≤ s) := by
  rw [testBit_altMask G L _ ht]
  have e : 0 + (G + G) * j + s = G * (2 * j) + s := by ring
  rw [e, Nat.mul_add_div (by omega)]
  rcases Nat.lt_or_ge s G with h | h
  · rw [Nat.div_eq_of_lt h]; simp [h, Nat.not_le.mpr h]
  · have h1 : 1 ≤ s / G := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have h2 : s / G < 2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    have : s / G = 1 := by omega
    rw [this]; simp [h]

/-- The high-guard mask at an item position. -/
lemma inHigh_item {K ρ G n : ℕ} (hK : G + 3 ≤ K) (j s : ℕ) (hj : j < n) (hs : s < K) :
    InHigh K ρ G n (ρ + K * j + s) ↔ G + 2 ≤ s := by
  rw [Nat.mul_comm K j]
  constructor
  · rintro ⟨c, hc, h1, h2⟩
    rcases Nat.lt_trichotomy c j with h | h | h
    · have := Nat.mul_le_mul_right K (show c + 1 ≤ j by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    · subst h; omega
    · have := Nat.mul_le_mul_right K (show j + 1 ≤ c by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
  · intro h
    exact ⟨j, hj, by omega, by omega⟩

lemma not_inHigh_lo {K ρ G n q : ℕ} (hq : q < ρ) : ¬ InHigh K ρ G n q := by
  rintro ⟨c, _, h1, _⟩; omega

lemma not_inHigh_hi {K ρ G n q : ℕ} (hq : ρ + K * n ≤ q) : ¬ InHigh K ρ G n q := by
  rintro ⟨c, hc, _, h2⟩
  have := Nat.mul_le_mul_right K (show c + 1 ≤ n by omega)
  rw [Nat.add_mul, one_mul] at this
  rw [Nat.mul_comm K n] at hq
  omega

/-- Stages `33` to `37`: the masks and the padding count. -/
lemma cxStage_masks (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) (s : ℕ) (hs : 32 ≤ s) (hs' : s < 37) :
    CxStageSpec body ι par d R₀ s := by
  have hunit := cxUnit_ge d
  have hG := hv.hG
  have hGK := hv.hGK
  have hρ := hv.hρ
  have hLK := hv.hLK
  have hnnL : d.ρ + d.K * d.nn ≤ d.L := by
    rw [hLK]; unfold CxD.nn; have := hv.hk
    have : d.K * (d.k - 1) + d.K = d.K * d.k := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  interval_cases s
  · -- `mselC`
    refine stage_of_exec body henv (x := .mselC) rfl (by decide)
      (c := 10 * d.L + 4 * d.ρ + d.nn * (4 * d.K + 9) + 18) (by unfold cxUnit; nlinarith)
      fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    obtain ⟨v', m, hu, hm, he⟩ := sxMask_exec body (nR := par .L) (oR := ι (.val .ρa))
      (KR := ι (.val .Ka)) (kR := ι (.val .nn)) (z := ι .mselC) (cnt := ι (.ts 0)) (w := ι (.ts 1))
      (t₁ := ι (.ts 2)) (t₂ := ι (.ts 3))
      (by simp [henv.hι.eq_iff, henv.hpι, henv.hpι', Fin.ext_iff]) true false
      (n := d.L) (o := d.ρ) (K := d.K) (N := d.nn) (X := selMask d.K d.ρ d.nn) v S
      (by cxsimp) (by cxsimp) (by cxsimp) (by cxsimp) (by omega) (by cxsimp) (by cxsimp) (by cxsimp)
      (by cxsimp)
      (fun q hq _ => not_isSel_lo d.K d.ρ d.nn q hq)
      (fun i hi _ => by
        have := testBit_selMask_seg d.K d.ρ d.nn i 0 hi (by omega)
        rw [show d.ρ + d.K * i = d.ρ + i * d.K + 0 by ring, this]; rfl)
      (fun i hi u hu1 hu2 _ => by
        have := testBit_selMask_seg d.K d.ρ d.nn i u hi hu2
        rw [show d.ρ + d.K * i + u = d.ρ + i * d.K + u by ring, this]
        simp; omega)
      (fun q hq _ => not_isSel_hi d.K d.ρ d.nn (by omega) q (by rw [Nat.mul_comm]; exact hq))
    refine ⟨v', m, _, hu, hm, he, ?_, fun t ht => Function.update_of_ne ht _ _⟩
    rw [Function.update_self]
    have : S.R (ι .mselC) = [] := by cxsimp
    rw [this, List.append_nil]; rfl
  · -- `mD`
    refine stage_of_exec body henv (x := .mD) rfl (by decide)
      (c := 10 * d.L + 4 * 0 + d.L * (4 * (d.G + d.G) + 13) + 18) (by unfold cxUnit; nlinarith)
      fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    obtain ⟨v', m, hu, hm, he⟩ := segMask_exec body (nR := par .L) (oR := ι (.val .z1))
      (aR := ι (.val .Ga)) (bR := ι (.val .Gb)) (kR := ι (.val .L)) (z := ι .mD) (cnt := ι (.ts 0))
      (w := ι (.ts 1)) (t₁ := ι (.ts 2)) (t₂ := ι (.ts 3))
      (by simp [henv.hι.eq_iff, henv.hpι, henv.hpι', Fin.ext_iff])
      (n := d.L) (o := 0) (a := d.G) (b := d.G) (N := d.L) (X := altMask d.G d.L) v S
      (by cxsimp) (by cxsimp) (by cxsimp) (by cxsimp) (by cxsimp) (by cxsimp) (by cxsimp) (by cxsimp)
      (by cxsimp)
      (fun q hq _ => absurd hq (Nat.not_lt_zero _))
      (fun j _ u hu ht => by rw [altMask_item d.G d.L hG j u (by omega) ht]; simp; omega)
      (fun j _ u hu1 hu2 ht => by rw [altMask_item d.G d.L hG j u hu2 ht]; simp [hu1])
      (fun q hq hqL => by
        have : d.L ≤ (d.G + d.G) * d.L := Nat.le_mul_of_pos_left d.L (by omega)
        omega)
    refine ⟨v', m, _, hu, hm, he, ?_, fun t ht => Function.update_of_ne ht _ _⟩
    rw [Function.update_self]
    have : S.R (ι .mD) = [] := by cxsimp
    rw [this, List.append_nil]; rfl
  · -- `mG`
    refine stage_of_exec body henv (x := .mG) rfl (by decide)
      (c := 4 * d.G + 4 + 1 + (4 * d.K + 4) + (4 * (d.G + 2) + 4) +
        (10 * d.L + 4 * d.ρ + d.nn * (4 * (d.G + 2 + (d.K - (d.G + 2))) + 13) + 18) +
        (2 * (d.G + 2) + 2) + (2 * (d.K - (d.G + 2)) + 2))
      (by
        have : d.G + 2 + (d.K - (d.G + 2)) = d.K := by omega
        rw [this]; unfold cxUnit; nlinarith)
      fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    have ht4 : S.R (ι (.ts 4)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .G) (b := ι (.ts 0)) (t := ι (.ts 1))
      (by cxne) (by cxne) (by cxne) v S ht1
    set R₁ := Function.update S.R (ι (.ts 0)) (List.replicate (S.R (par .G)).length tick ++
      S.R (ι (.ts 0))) with hR₁
    have he₂ := Exec.act (body := body) (pushN (ι (.ts 0)) (fun _ => tick) 2 .done)
      (mk v₁ { S with R := R₁ })
    rw [pushN_run, run_done] at he₂
    set R₂ := Function.update R₁ (ι (.ts 0)) (List.replicate 2 tick ++ R₁ (ι (.ts 0))) with hR₂
    have hR₂0 : R₂ (ι (.ts 0)) = List.replicate (d.G + 2) tick := by
      rw [hR₂, Function.update_self, hR₁, Function.update_self, ht0, List.append_nil,
        List.replicate_append_replicate]
      congr 1
      have : (S.R (par .G)).length = d.G := by cxsimp
      omega
    have hR₂f : ∀ k, k ≠ ι (.ts 0) → R₂ k = S.R k := fun k hk => by
      rw [hR₂, Function.update_of_ne hk, hR₁, Function.update_of_ne hk]
    obtain ⟨v₃, hu₃, he₃⟩ := sx_then_ucopy body (Exec.seq he₁ he₂) (a := par .K) (b := ι (.ts 4))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne)
      (by show R₂ (ι (.ts 1)) = []; rw [hR₂f _ (henv.ne (by simp [Fin.ext_iff]))]; exact ht1)
    obtain ⟨v₄, hu₄, he₄⟩ := sx_then_usub body he₃ (a := ι (.ts 0)) (b := ι (.ts 4))
      (t := ι (.ts 1)) (by cxne) (by cxne) (by cxne)
      (by
        show Function.update R₂ (ι (.ts 4)) _ (ι (.ts 1)) = []
        rw [Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])),
          hR₂f _ (henv.ne (by simp [Fin.ext_iff]))]; exact ht1)
    set R₄ := Function.update (Function.update R₂ (ι (.ts 4))
      (List.replicate (R₂ (par .K)).length tick ++ R₂ (ι (.ts 4)))) (ι (.ts 4))
      ((Function.update R₂ (ι (.ts 4))
        (List.replicate (R₂ (par .K)).length tick ++ R₂ (ι (.ts 4))) (ι (.ts 4))).drop
          (Function.update R₂ (ι (.ts 4))
            (List.replicate (R₂ (par .K)).length tick ++ R₂ (ι (.ts 4))) (ι (.ts 0))).length)
      with hR₄
    have hR₄f : ∀ k, k ≠ ι (.ts 0) → k ≠ ι (.ts 4) → R₄ k = S.R k := fun k hk0 hk4 => by
      rw [hR₄, Function.update_of_ne hk4, Function.update_of_ne hk4, hR₂f _ hk0]
    have hR₄0 : R₄ (ι (.ts 0)) = List.replicate (d.G + 2) tick := by
      rw [hR₄, Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])),
        Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])), hR₂0]
    have hR₄4 : R₄ (ι (.ts 4)) = List.replicate (d.K - (d.G + 2)) tick := by
      rw [hR₄, Function.update_self, Function.update_self,
        Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])), hR₂0,
        hR₂f _ (henv.ne (by simp [Fin.ext_iff])), ht4, List.append_nil, List.length_replicate,
        hR₂f _ (henv.hpι' _ _), List.drop_replicate]
      congr 1
      have : (S.R (par .K)).length = d.K := by cxsimp
      omega
    obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := segMask_exec body (nR := par .L) (oR := ι (.val .ρa))
      (aR := ι (.ts 0)) (bR := ι (.ts 4)) (kR := ι (.val .nn)) (z := ι .mG) (cnt := ι (.ts 1))
      (w := ι (.ts 2)) (t₁ := ι (.ts 3)) (t₂ := ι (.ts 5))
      (by simp [henv.hι.eq_iff, henv.hpι, henv.hpι', Fin.ext_iff])
      (n := d.L) (o := d.ρ) (a := d.G + 2) (b := d.K - (d.G + 2)) (N := d.nn)
      (X := highMask d.K d.ρ d.G d.nn d.L) v₄ { S with R := R₄ }
      (by show (R₄ (par .L)).length = _; rw [hR₄f _ (henv.hpι' _ _) (henv.hpι' _ _)]; cxsimp)
      (by show (R₄ (ι (.val .ρa))).length = _
          rw [hR₄f _ (henv.ne (by simp)) (henv.ne (by simp))]; cxsimp)
      (by show (R₄ (ι (.ts 0))).length = _; rw [hR₄0, List.length_replicate])
      (by show (R₄ (ι (.ts 4))).length = _; rw [hR₄4, List.length_replicate])
      (by show (R₄ (ι (.val .nn))).length = _
          rw [hR₄f _ (henv.ne (by simp)) (henv.ne (by simp))]; cxsimp)
      (by show R₄ (ι (.ts 1)) = []
          rw [hR₄f _ (henv.ne (by simp [Fin.ext_iff])) (henv.ne (by simp [Fin.ext_iff]))]; exact ht1)
      (by show R₄ (ι (.ts 2)) = []
          rw [hR₄f _ (henv.ne (by simp [Fin.ext_iff])) (henv.ne (by simp [Fin.ext_iff]))]; cxsimp)
      (by show R₄ (ι (.ts 3)) = []
          rw [hR₄f _ (henv.ne (by simp [Fin.ext_iff])) (henv.ne (by simp [Fin.ext_iff]))]; cxsimp)
      (by show R₄ (ι (.ts 5)) = []
          rw [hR₄f _ (henv.ne (by simp [Fin.ext_iff])) (henv.ne (by simp [Fin.ext_iff]))]; cxsimp)
      (fun q hq hqL => by
        rw [testBit_highMask _ _ _ _ _ _ hqL]; exact decide_eq_false (not_inHigh_lo hq))
      (fun j hj u hu ht => by
        have e : d.G + 2 + (d.K - (d.G + 2)) = d.K := by omega
        rw [e] at ht ⊢
        rw [testBit_highMask _ _ _ _ _ _ ht]
        exact decide_eq_false (fun h => by have := (inHigh_item hGK j u hj (by omega)).1 h; omega))
      (fun j hj u hu1 hu2 ht => by
        have e : d.G + 2 + (d.K - (d.G + 2)) = d.K := by omega
        rw [e] at ht hu2 ⊢
        rw [testBit_highMask _ _ _ _ _ _ ht]
        exact decide_eq_true ((inHigh_item hGK j u hj hu2).2 hu1))
      (fun q hq hqL => by
        have e : d.G + 2 + (d.K - (d.G + 2)) = d.K := by omega
        rw [e] at hq
        rw [testBit_highMask _ _ _ _ _ _ hqL]; exact decide_eq_false (not_inHigh_hi hq))
    have hR₄mG : R₄ (ι .mG) = [] := by
      rw [hR₄f _ (henv.ne (by simp)) (henv.ne (by simp))]; cxsimp
    set R₅ := Function.update R₄ (ι .mG) (binSyms d.L (highMask d.K d.ρ d.G d.nn d.L) ++ R₄ (ι .mG))
      with hR₅
    obtain ⟨v₆, hu₆, he₆⟩ := sx_then_uclear body (Exec.seq he₄ he₅) (ι (.ts 0))
    obtain ⟨v₇, hu₇, he₇⟩ := sx_then_uclear body he₆ (ι (.ts 4))
    have hR₅f : ∀ k, k ≠ ι .mG → R₅ k = R₄ k := fun k hk => by
      rw [hR₅, Function.update_of_ne hk]
    refine ⟨v₇, _, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃]; simpa using hu₁, ?_, he₇, ?_, ?_⟩
    · -- the cost
      have e1 : (S.R (par .G)).length = d.G := by cxsimp
      have e2 : (R₂ (par .K)).length = d.K := by
        rw [hR₂f _ (henv.hpι' _ _)]; cxsimp
      have e3 : (Function.update R₂ (ι (.ts 4))
          (List.replicate d.K tick ++ R₂ (ι (.ts 4))) (ι (.ts 0))).length = d.G + 2 := by
        rw [Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])), hR₂0, List.length_replicate]
      have e4 : (R₅ (ι (.ts 0))).length = d.G + 2 := by
        rw [hR₅f _ (henv.ne (by simp)), hR₄0, List.length_replicate]
      have e5 : (Function.update R₅ (ι (.ts 0)) [] (ι (.ts 4))).length = d.K - (d.G + 2) := by
        rw [Function.update_of_ne (henv.ne (by simp [Fin.ext_iff])), hR₅f _ (henv.ne (by simp)),
          hR₄4, List.length_replicate]
      simp only [e1, e2, e3, e4, e5]
      omega
    · show Function.update (Function.update R₅ (ι (.ts 0)) []) (ι (.ts 4)) [] (ι .mG) = _
      rw [Function.update_of_ne (henv.ne (by simp)), Function.update_of_ne (henv.ne (by simp)),
        hR₅, Function.update_self, hR₄mG, List.append_nil]
      rfl
    · intro t ht
      show Function.update (Function.update R₅ (ι (.ts 0)) []) (ι (.ts 4)) [] t = S.R t
      by_cases h4 : t = ι (.ts 4)
      · subst h4; rw [Function.update_self, ht4]
      rw [Function.update_of_ne h4]
      by_cases h0 : t = ι (.ts 0)
      · subst h0; rw [Function.update_self, ht0]
      rw [Function.update_of_ne h0, hR₅f _ ht, hR₄f _ h0 h4]
  · -- `mtopC`
    refine stage_of_exec body henv (x := .mtopC) rfl (by decide)
      (c := 4 * d.ρ + 4 + (d.nn * (4 * d.K + 9) + 4) + (10 * d.L + 4 * (d.nn * d.K + d.ρ) + 15) +
        (2 * (d.nn * d.K + d.ρ) + 2))
      (by unfold cxUnit; nlinarith) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have ht1 : S.R (ι (.ts 1)) = [] := by cxsimp
    have ht2 : S.R (ι (.ts 2)) = [] := by cxsimp
    have ht3 : S.R (ι (.ts 3)) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .ρ) (b := ι (.ts 0)) (t := ι (.ts 1))
      (by cxne) (by cxne) (by cxne) v S ht1
    set R₁ := Function.update S.R (ι (.ts 0)) (List.replicate (S.R (par .ρ)).length tick ++
      S.R (ι (.ts 0))) with hR₁
    have hR₁f : ∀ k, k ≠ ι (.ts 0) → R₁ k = S.R k := fun k hk => by
      rw [hR₁, Function.update_of_ne hk]
    have hR₁0 : R₁ (ι (.ts 0)) = List.replicate d.ρ tick := by
      rw [hR₁, Function.update_self, ht0, List.append_nil]
      have : (S.R (par .ρ)).length = d.ρ := by cxsimp
      rw [this]
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := umulU_exec body (a := ι (.val .nn)) (b := par .K)
      (c := ι (.ts 0)) (t₁ := ι (.ts 1)) (t₂ := ι (.ts 2))
      (by simp [henv.hι.eq_iff, henv.hpι, henv.hpι', Fin.ext_iff]) v₁ { S with R := R₁ }
      (by show R₁ (ι (.ts 1)) = []; rw [hR₁f _ (henv.ne (by simp [Fin.ext_iff]))]; exact ht1)
      (by show R₁ (ι (.ts 2)) = []; rw [hR₁f _ (henv.ne (by simp [Fin.ext_iff]))]; exact ht2)
    have hnn : (R₁ (ι (.val .nn))).length = d.nn := by rw [hR₁f _ (henv.ne (by simp))]; cxsimp
    have hKl : (R₁ (par .K)).length = d.K := by rw [hR₁f _ (henv.hpι' _ _)]; cxsimp
    set R₂ := Function.update R₁ (ι (.ts 0))
      (List.replicate ((R₁ (ι (.val .nn))).length * (R₁ (par .K)).length) tick ++ R₁ (ι (.ts 0)))
      with hR₂
    have hR₂f : ∀ k, k ≠ ι (.ts 0) → R₂ k = S.R k := fun k hk => by
      rw [hR₂, Function.update_of_ne hk, hR₁f _ hk]
    have hR₂0 : R₂ (ι (.ts 0)) = List.replicate (d.nn * d.K + d.ρ) tick := by
      rw [hR₂, Function.update_self, hR₁0, hnn, hKl, List.replicate_append_replicate]
    obtain ⟨v₃, hu₃, he₃⟩ := bitMask_exec body (nR := par .L) (tR := ι (.ts 0)) (z := ι .mtopC)
      (cnt := ι (.ts 1)) (w := ι (.ts 2)) (t₁ := ι (.ts 3))
      (by simp [henv.hι.eq_iff, henv.hpι, henv.hpι', Fin.ext_iff]) (n := d.L)
      (t := d.nn * d.K + d.ρ) v₂ { S with R := R₂ }
      (by show (R₂ (par .L)).length = _; rw [hR₂f _ (henv.hpι' _ _)]; cxsimp)
      (by show (R₂ (ι (.ts 0))).length = _; rw [hR₂0, List.length_replicate])
      (by show R₂ (ι (.ts 1)) = []; rw [hR₂f _ (henv.ne (by simp [Fin.ext_iff]))]; exact ht1)
      (by show R₂ (ι (.ts 2)) = []; rw [hR₂f _ (henv.ne (by simp [Fin.ext_iff]))]; exact ht2)
      (by show R₂ (ι (.ts 3)) = []; rw [hR₂f _ (henv.ne (by simp [Fin.ext_iff]))]; exact ht3)
    set R₃ := Function.update R₂ (ι .mtopC) (binSyms d.L (2 ^ (d.nn * d.K + d.ρ)) ++ R₂ (ι .mtopC))
      with hR₃
    obtain ⟨v₄, hu₄, he₄⟩ := sx_then_uclear body (Exec.seq (Exec.seq he₁ he₂) he₃) (ι (.ts 0))
    have hR₃f : ∀ k, k ≠ ι .mtopC → R₃ k = R₂ k := fun k hk => by
      rw [hR₃, Function.update_of_ne hk]
    refine ⟨v₄, _, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, he₄, ?_, ?_⟩
    · have e1 : (S.R (par .ρ)).length = d.ρ := by cxsimp
      have e2 : (R₃ (ι (.ts 0))).length = d.nn * d.K + d.ρ := by
        rw [hR₃f _ (henv.ne (by simp)), hR₂0, List.length_replicate]
      simp only [hnn, hKl] at hm₂
      simp only [e1, e2, hnn, hKl]
      omega
    · show Function.update R₃ (ι (.ts 0)) [] (ι .mtopC) = _
      rw [Function.update_of_ne (henv.ne (by simp)), hR₃, Function.update_self,
        hR₂f _ (henv.ne (by simp))]
      have : S.R (ι .mtopC) = [] := by cxsimp
      rw [this, List.append_nil, Nat.add_comm (d.nn * d.K) d.ρ]
      rfl
    · intro t ht
      show Function.update R₃ (ι (.ts 0)) [] t = S.R t
      by_cases h0 : t = ι (.ts 0)
      · subst h0; rw [Function.update_self, ht0]
      rw [Function.update_of_ne h0, hR₃f _ ht, hR₂f _ h0]
  · -- `padR`
    refine stage_of_exec body henv (x := .padR) rfl (by decide)
      (c := 4 * d.L + 4 + (4 * d.nG + 4)) (by omega) fun v S hS => ?_
    have hF := henv.fill_ι hS
    have hP := henv.fill_par hS
    have ht0 : S.R (ι (.ts 0)) = [] := by cxsimp
    have hxe : S.R (ι .padR) = [] := by cxsimp
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := par .L) (b := ι .padR) (t := ι (.ts 0))
      (by cxne) (by cxne) (by cxne) v S ht0
    obtain ⟨v₂, hu₂, he₂⟩ := sx_then_usub body he₁ (a := ι (.val .nGa)) (b := ι .padR)
      (t := ι (.ts 0)) (by cxne) (by cxne) (by cxne) (by cxsimp)
    refine ⟨v₂, _, _, by rw [hu₂, hu₁], by cxsimp, he₂, ?_, fun t ht => by
      simp only [Function.update_of_ne ht]⟩
    simp only [Function.update_self, Function.update_idem, hxe, List.append_nil]
    cxsimp


/-- The stage of the register built at stage `s`. -/
lemma cxStage_ofStage (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ 37) (h15 : s ≠ 15) :
    cxStage (cxOfStage s) = s := by
  interval_cases s <;> first | rfl | exact absurd rfl h15

/-- Every setup stage. -/
lemma cxStage_all (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) : ∀ s < 37, CxStageSpec body ι par d R₀ s := by
  intro s hs
  rcases Nat.lt_or_ge s 14 with h | h
  · exact cxStage_pool body henv hR₀ hv.hG (by have := hv.hGK; omega) s h
  rcases Nat.eq_or_lt_of_le h with h' | h'
  · subst h'; exact cxStage_15 body henv hR₀ hv
  rcases Nat.lt_or_ge s 26 with h2 | h2
  · exact cxStage_fld body henv hR₀ hv s h' h2
  rcases Nat.lt_or_ge s 32 with h3 | h3
  · exact cxStage_kf body henv hR₀ hv s h2 h3
  · exact cxStage_masks body henv hR₀ hv s h3 hs

end StageProofs

/-! ### The setup and the cleanup -/

section SetupCleanup

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable (ι : CXReg → Fin T) (par : CXPar → Fin T) (d : CxD)

/-- The setup: the thirty-seven stages. -/
noncomputable def cxSetup : Pr P T Q A U :=
  Prog.seqList ((List.range 37).map fun i => cxStageProg ι par d (i + 1))

/-- The stage programs depend on the data only through the static slots. -/
lemma cxStageProg_ofXY (s : ℕ) (hs : s < 38) :
    cxStageProg (P := P) (Q := Q) (U := U) (A := A) ι par (CxD.ofXY d.x d.y) s =
      cxStageProg ι par d s := by
  interval_cases s <;> rfl

lemma cxSetup_ofXY :
    cxSetup (P := P) (Q := Q) (U := U) (A := A) ι par (CxD.ofXY d.x d.y) = cxSetup ι par d := by
  unfold cxSetup
  exact congrArg Prog.seqList (List.map_congr_left fun i hi =>
    cxStageProg_ofXY ι par d (i + 1) (by simp at hi; omega))

/-- The program undoing stage `s`. -/
noncomputable def cxUnstage (s : ℕ) : Pr P T Q A U :=
  if s = 15 then sxCleanup (sxι ι) else uclear (ι (cxOfStage s))

/-- The cleanup: clear the built registers, the last built first. -/
noncomputable def cxCleanup : Pr P T Q A U :=
  Prog.seqList ((List.range 37).map fun i => cxUnstage ι (37 - i))

/-- The step bound of the cleanup. -/
noncomputable def cxCleanupCost : ℕ :=
  ∑ i ∈ Finset.range 37, (if 37 - i = 15 then
    ∑ j ∈ Finset.range 38, (2 * (sxBc A d.swapD (sxOfStage (38 - j))).length + 2) + 1
    else 2 * (cxBc A d (cxOfStage (37 - i))).length + 2) + 1

variable {ι par d} {src : Fin T} {R₀ : Fin T → List (Fin (A + 4))}

theorem cxSetup_exec (henv : CxEnv ι par src) (hR₀ : ∀ p, (R₀ (par p)).length = d.par p)
    (hv : d.Valid) (h0 : ∀ x, R₀ (ι x) = []) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = R₀) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ ∑ i ∈ Finset.range 37, cxStageCost d (i + 1) + 1 ∧
      Exec body (cxSetup ι par d) (mk v S) m
        (mk v' { S with R := cxFill ι (cxBc A d) 37 R₀ }) := by
  have hall := cxStage_all body henv hR₀ hv
  obtain ⟨v', m, hu, hm, he⟩ := sx_chain_exec body (fun i => cxFill ι (cxBc A d) i R₀)
    (fun i => cxStageProg ι par d (i + 1)) (fun i => cxStageCost d (i + 1)) 37 0
    (fun i hi v S hS => by simpa using hall i hi v S (by simpa using hS)) v S
    (by rw [hS, cxFill_zero henv.hι _ R₀ h0 (cxBc_zero A d)])
  refine ⟨v', m, hu, by simpa using hm, ?_⟩
  unfold cxSetup
  simpa using he

theorem cxCleanup_exec (henv : CxEnv ι par src) {R₁ : Fin T → List (Fin (A + 4))}
    (h0 : ∀ x, R₁ (ι x) = []) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = cxFill ι (cxBc A d) 37 R₁) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ cxCleanupCost (A := A) d ∧
      Exec body (cxCleanup (P := P) (Q := Q) (U := U) ι) (mk v S) m (mk v' { S with R := R₁ }) := by
  obtain ⟨v', m, hu, hm, he⟩ := sx_chain_exec body (fun i => cxFill ι (cxBc A d) (37 - i) R₁)
    (fun i => cxUnstage ι (37 - i))
    (fun i => if 37 - i = 15 then
      ∑ j ∈ Finset.range 38, (2 * (sxBc A d.swapD (sxOfStage (38 - j))).length + 2) + 1
      else 2 * (cxBc A d (cxOfStage (37 - i))).length + 2) 37 0
    (fun i hi v S hS => by
      simp only [Nat.zero_add] at hS ⊢
      by_cases h15 : 37 - i = 15
      · -- the interchange cleanup
        rw [h15] at hS ⊢
        simp only [cxUnstage, ↓reduceIte]
        have hsx := cxSxEnv henv
        obtain ⟨v', m, hu, hm, he⟩ := sxCleanup_exec body (d := d.swapD) hsx
          (R₁ := cxFill ι (cxBc A d) 14 R₁)
          (fun x => by
            rw [show sxι ι x = ι (CXReg.sx x) from rfl, cxFill_ι henv.hι]
            simp only [cxStage]
            split_ifs with h1 h2 <;> first | omega | rfl | exact cxBc_zero A d _ (by simp [cxStage, h1]))
          v S (by rw [hS, cxFill_sx henv.hι])
        refine ⟨v', m, hu, hm, Exec.cast he rfl ?_⟩
        rw [show 37 - (i + 1) = 14 by omega]
      · simp only [cxUnstage, h15, ↓reduceIte]
        have hx : cxStage (cxOfStage (37 - i)) = 37 - i :=
          cxStage_ofStage (37 - i) (by omega) (by omega) h15
        obtain ⟨v', hu, he⟩ := uclear_exec body (ι (cxOfStage (37 - i))) v S
        refine ⟨v', _, hu, ?_, Exec.cast he rfl ?_⟩
        · rw [hS, cxFill_ι henv.hι, if_pos (by omega)]
        · congr 2
          have h := cxFill_unstep henv.hι (cxBc A d) R₁ (s := 36 - i)
            (x := cxOfStage (37 - i)) (by rw [hx]; omega)
            (fun y hy => cxStage_uniq (by omega) (by omega) (hy.trans (by rw [hx]; omega)))
          rw [hS, show 37 - (i + 1) = 36 - i by omega, ← h, show 36 - i + 1 = 37 - i by omega])
    v S (by simpa using hS)
  refine ⟨v', m, hu, by simpa [cxCleanupCost] using hm, Exec.cast he rfl ?_⟩
  congr 2
  simp only [Nat.zero_add, Nat.sub_self]
  exact cxFill_zero henv.hι _ R₁ h0 (cxBc_zero A d)

end SetupCleanup



end IntegerMultBounds.MathlibTM2.Node
