module

public import IntegerMultBounds.MathlibTM2.M8.TwistedExchange
public import IntegerMultBounds.MathlibTM2.M8.ExchangeProgram

/-!
# Field programs over an atom ring

The stage-2 machine keeps the field programs of the network unchanged and runs them on
coordinates that carry `f` atoms. Within a field, scalings and shifts act on every atom alike.
Across the two fields, the head is read with its atoms reversed: `addToD i j` adds `σ(h_i)` into
`d_j`, `subFromD i j` writes `σ(h_i) - d_j`, and `interchange i j` is the twisted interchange
`h_i ← σ(d_j)`, `d_j ← σ(h_i)`, a reversed child (`twRun`).

`twRun_eq`: when the tail scalings and shifts have `σ`-fixed coefficients (`FixedOp`), the
twisted run is the ordinary run conjugated by the twist of the tail field. Coefficients that are
scalars, the images of a map that `σ` fixes, always qualify (`fixedOp_mapOp`). So every theorem
about ordinary runs transfers. In particular the reversed exchange program, the stage-1
`exchangeOps` on a factorization `P C = L Π R` (`revOps_run`), runs twisted as the reversed
exchange of the atom field (`revOps_twRun`), with one reversed child per pivot.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.TwistedProgram

open Matrix
open IntegerMultBounds.Networks
open IntegerMultBounds.Swap.Shear (State LowerTriangular pivotMatrix)
open Exchange (transform cross swaps kMat exchangeOps transformOps_run swapOps_run run_append)
open ReversedExchange (revExchangeOf)
open TwistedExchange (twist conj revSwap conj_conj)

variable {ι S : Type*} [Fintype ι] [LinearOrder ι] [CommRing S] (σ : S →+* S)

/-- One field operation with the head read through `σ`. -/
def twExecute : AffineFieldProgram.Op ι S → State ι S → State ι S
  | .affineH op, s => (OrderedAffine.execute op s.1, s.2)
  | .affineD op, s => (s.1, OrderedAffine.execute op s.2)
  | .addToD i j, s => (s.1, Function.update s.2 j (s.2 j + σ (s.1 i)))
  | .subFromD i j, s => (s.1, Function.update s.2 j (σ (s.1 i) - s.2 j))
  | .interchange i j, s => revSwap σ (i, j) s

/-- The twisted run of a field program. -/
def twRun (p : List (AffineFieldProgram.Op ι S)) (s : State ι S) : State ι S :=
  p.foldl (fun s op => twExecute σ op s) s

/-- The tail scalings and shifts have `σ`-fixed coefficients. -/
def FixedOp : AffineFieldProgram.Op ι S → Prop
  | .affineD (.scale _ a) => σ a = a
  | .affineD (.shift _ _ a) => σ a = a
  | _ => True

variable {σ}

omit [Fintype ι] [LinearOrder ι] in
theorem fixedOp_mapOp {R : Type*} {g : R → S} (hg : ∀ c, σ (g c) = g c)
    (op : AffineFieldProgram.Op ι R) : FixedOp σ (AffineFieldProgram.mapOp g op) := by
  cases op with
  | affineH op => trivial
  | affineD op => cases op <;> exact hg _
  | addToD => trivial
  | subFromD => trivial
  | interchange => trivial

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

omit [Fintype ι] hσ in
theorem twist_update (v : ι → S) (i : ι) (z : S) :
    twist σ (Function.update v i z) = Function.update (twist σ v) i (σ z) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [twist]
  · simp [twist, hk]

theorem twExecute_eq {op : AffineFieldProgram.Op ι S} (hop : FixedOp σ op) (s : State ι S) :
    twExecute σ op s = conj σ (AffineFieldProgram.execute op (conj σ s)) := by
  obtain ⟨h, d⟩ := s
  have htt := TwistedExchange.twist_twist hσ d
  cases op with
  | affineH op => simp [twExecute, AffineFieldProgram.execute, conj, htt]
  | affineD op =>
    cases op with
    | scale i a =>
      simp only [FixedOp] at hop
      simp [twExecute, AffineFieldProgram.execute, OrderedAffine.execute, conj,
        twist_update, htt, hop, twist, hσ]
    | shift i j a =>
      simp only [FixedOp] at hop
      simp [twExecute, AffineFieldProgram.execute, OrderedAffine.execute, conj,
        twist_update, htt, hop, twist, hσ]
  | addToD i j =>
    simp [twExecute, AffineFieldProgram.execute, Swap.Shear.Op.run, conj, twist_update, htt,
      twist, hσ]
  | subFromD i j =>
    simp [twExecute, AffineFieldProgram.execute, Swap.Shear.Op.run, conj, twist_update, htt,
      twist, hσ]
  | interchange i j =>
    change revSwap σ (i, j) (h, d) =
      conj σ ((Swap.Shear.Op.interchange (i, j).1 (i, j).2).run (conj σ (h, d)))
    rw [TwistedExchange.conj_interchange hσ, conj_conj hσ]

/-- **The twisted run** is the ordinary run conjugated by the twist of the tail field. -/
theorem twRun_eq : ∀ {p : List (AffineFieldProgram.Op ι S)}, (∀ op ∈ p, FixedOp σ op) →
    ∀ s, twRun σ p s = conj σ (AffineFieldProgram.run p (conj σ s))
  | [], _, s => (conj_conj hσ s).symm
  | op :: p, hp, s => by
    change twRun σ p (twExecute σ op s) =
      conj σ (AffineFieldProgram.run p (AffineFieldProgram.execute op (conj σ s)))
    rw [twExecute_eq hσ (hp op (by simp)), twRun_eq (fun op h => hp op (by simp [h])),
      conj_conj hσ]

omit hσ

/-- The exchange program from its parts, as the composition of its parts. -/
theorem exchangeOps_run_parts {E₁ E₁' E₂ E₂' : Matrix ι ι S} (L : List (ι × ι))
    (hl₁ : LowerTriangular E₁) (hl₁' : LowerTriangular E₁') (hl₂ : LowerTriangular E₂)
    (hl₂' : LowerTriangular E₂') {K K' : Matrix ι ι S}
    (crossK crossNegK : List (AffineFieldProgram.Op ι S))
    (hK : ∀ s, AffineFieldProgram.run crossK s = cross K s)
    (hK' : ∀ s, AffineFieldProgram.run crossNegK s = cross K' s) (s : State ι S) :
    AffineFieldProgram.run (exchangeOps E₁ E₁' E₂ E₂' L crossK crossNegK) s =
      transform E₁ E₂' (cross K' (Swap.Shear.run (swaps L) (cross K (transform E₁' E₂ s)))) := by
  rw [exchangeOps, run_append, run_append, run_append, run_append, transformOps_run _ _ hl₁' hl₂,
    hK, swapOps_run, hK', transformOps_run _ _ hl₁ hl₂']

/-- **The reversed exchange program.** On a factorization `P C = L Π R'` with lower-triangular
`L`, `L⁻¹`, `R'`, `R'⁻¹`, the exchange program of the parts runs as the reversed exchange. -/
theorem revOps_run {C : Matrix ι ι S} (hC : C * C = 1) {L L' R' R'' : Matrix ι ι S}
    (hl : LowerTriangular L) (hl' : LowerTriangular L') (hr : LowerTriangular R')
    (hr' : LowerTriangular R'') (pivots : List (ι × ι)) (h₁ : (pivots.map Prod.fst).Nodup)
    (h₂ : (pivots.map Prod.snd).Nodup) (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1)
    (hR' : R'' * R' = 1) (P : Matrix ι ι S) (hP : P * C = L * pivotMatrix pivots * R')
    (hidem : P * P = P) (crossK crossNegK : List (AffineFieldProgram.Op ι S))
    (hK : ∀ s, AffineFieldProgram.run crossK s = cross (kMat (pivotMatrix pivots) (R' * C * L)) s)
    (hK' : ∀ s, AffineFieldProgram.run crossNegK s =
      cross (-kMat (pivotMatrix pivots) (R' * C * L)) s) (s : State ι S) :
    AffineFieldProgram.run (exchangeOps L L' R' R'' pivots crossK crossNegK) s =
      revExchangeOf C P s := by
  rw [exchangeOps_run_parts pivots hl hl' hr hr' crossK crossNegK hK hK']
  exact ReversedExchange.revExchangeOf_factor C hC L L' R' R'' pivots h₁ h₂ hL hL' hR hR' P hP
    hidem s

include hσ in
/-- **The reversed exchange of the atom field.** The same program, run twisted, is the reversed
exchange conjugated by the twist: with `C` the reversal of the coordinates, the reversal of all
atoms. Its `pivots.length` twisted interchanges are the reversed children. -/
theorem revOps_twRun {C : Matrix ι ι S} (hC : C * C = 1) {L L' R' R'' : Matrix ι ι S}
    (hl : LowerTriangular L) (hl' : LowerTriangular L') (hr : LowerTriangular R')
    (hr' : LowerTriangular R'') (pivots : List (ι × ι)) (h₁ : (pivots.map Prod.fst).Nodup)
    (h₂ : (pivots.map Prod.snd).Nodup) (hL : L * L' = 1) (hL' : L' * L = 1) (hR : R' * R'' = 1)
    (hR' : R'' * R' = 1) (P : Matrix ι ι S) (hP : P * C = L * pivotMatrix pivots * R')
    (hidem : P * P = P) (crossK crossNegK : List (AffineFieldProgram.Op ι S))
    (hK : ∀ s, AffineFieldProgram.run crossK s = cross (kMat (pivotMatrix pivots) (R' * C * L)) s)
    (hK' : ∀ s, AffineFieldProgram.run crossNegK s =
      cross (-kMat (pivotMatrix pivots) (R' * C * L)) s)
    (hfixed : ∀ op ∈ exchangeOps L L' R' R'' pivots crossK crossNegK, FixedOp σ op)
    (s : State ι S) :
    twRun σ (exchangeOps L L' R' R'' pivots crossK crossNegK) s =
      conj σ (revExchangeOf C P (conj σ s)) := by
  rw [twRun_eq hσ hfixed, revOps_run hC hl hl' hr hr' pivots h₁ h₂ hL hL' hR hR' P hP hidem
    crossK crossNegK hK hK']

end IntegerMultBounds.MathlibTM2.M8.TwistedProgram
