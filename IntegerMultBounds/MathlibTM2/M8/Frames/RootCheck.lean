module

public import Mathlib.Init

/-!
# Kernel checks of root-complement bases

A root is coded by a natural number: an output triple `{p₀, p₁, p₂}`, `p₀ < p₁ < p₂ < 23`, by
`p₀ + 32 p₁ + 1024 p₂`, or the centre `c < 23` by `32768 + c`, with the vector `w_c = 1 + 7 e_c`. The dot
products of two codes, their sums and so `9 G(x, y) = 9 x · y − (Σ x)(Σ y)` are computed from the
codes (`dotE`, `sumE`, `g9`), without the vectors.

A list `B` of codes is a basis of a root complement when its Gram matrix `Γ` under `9 G` is
invertible and every generator lies in the span of `B`. The check `basisOk B gens` computes, by a
fraction-free Gauss–Jordan elimination that nothing trusts (`gaussJordan`), a matrix `N` and an
integer `d` with `Γ N = d · 1`; for a generator `g` it takes `λ = N v`, `v_i = 9 G(b_i, g)`, and
checks that the residual `e = d g − Σ λ_i b_i` has Euclidean norm zero:
`d² g·g − 2 d Σ λ_i b_i·g + Σ λ_i λ_j b_i·b_j = 0`. `Frames/RootFrame` turns a passed check into
the frame facts.

All functions recurse structurally over lists, for kernel reduction.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames.RootCheck

/-- The code offset of the centres. -/
def cen : Nat := 32768

/-- The points of a triple code `p₀ + 32 p₁ + 1024 p₂`. -/
def p0 (k : Nat) : Nat := Nat.mod k 32
def p1 (k : Nat) : Nat := Nat.mod (Nat.div k 32) 32
def p2 (k : Nat) : Nat := Nat.div k 1024

/-- `[x = y]`. -/
def eqN (x y : Nat) : Nat := bif Nat.beq x y then 1 else 0

/-- `[x ∈ k]` for a triple code `k`. -/
def memT (x k : Nat) : Nat := Nat.add (Nat.add (eqN x (p0 k)) (eqN x (p1 k))) (eqN x (p2 k))

/-- A valid code: three points `p₀ < p₁ < p₂ < 23`, or a centre below `23`. -/
def validCode (k : Nat) : Bool :=
  bif Nat.blt k cen then Nat.blt (p0 k) (p1 k) && Nat.blt (p1 k) (p2 k) && Nat.blt (p2 k) 23
  else Nat.blt (Nat.sub k cen) 23

/-- The sum of the entries of the vector of code `k`. -/
def sumE (k : Nat) : Int := bif Nat.blt k cen then 3 else 30

/-- The dot product of the vectors of two codes. -/
def dotE (a b : Nat) : Int :=
  bif Nat.blt a cen then
    (bif Nat.blt b cen then Int.ofNat (Nat.add (Nat.add (memT (p0 a) b) (memT (p1 a) b)) (memT (p2 a) b))
     else Int.ofNat (Nat.add 3 (Nat.mul 7 (memT (Nat.sub b cen) a))))
  else
    (bif Nat.blt b cen then Int.ofNat (Nat.add 3 (Nat.mul 7 (memT (Nat.sub a cen) b)))
     else bif Nat.beq a b then 86 else 37)

/-- `9 G` of the vectors of two codes. -/
def g9 (a b : Nat) : Int := 9 * dotE a b - sumE a * sumE b

/-- The dot product of two lists. -/
def dot : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

/-- `l x + m y`, entrywise. -/
def comb (l m : Int) : List Int → List Int → List Int
  | x :: xs, y :: ys => (l * x + m * y) :: comb l m xs ys
  | _, _ => []

/-- Exact division of every entry. -/
def divAll (p : Int) : List Int → List Int
  | [] => []
  | x :: xs => x / p :: divAll p xs

/-- Row `i` of the identity of size `n`. -/
def unitRow (n i : Nat) : List Int := (List.range n).map fun j => bif Nat.beq i j then 1 else 0

/-- The augmented rows `[Γ | 1]`. -/
def augment (rows : List (List Int)) : List (List Int) :=
  (List.range rows.length).zipWith (fun i r => r ++ unitRow rows.length i) rows

/-- The offset, from the first row, of a row with a nonzero entry in column `k`. -/
def findPivot (k : Nat) : Nat → List (List Int) → Option Nat
  | _, [] => none
  | i, r :: rs => bif (r.getD k 0 != 0) then some i else findPivot k (i + 1) rs

/-- Swap rows `i` and `j`. -/
def swapRows (i j : Nat) (rows : List (List Int)) : List (List Int) :=
  (rows.set i (rows.getD j [])).set j (rows.getD i [])

/-- The rows other than the pivot row `pr` at `k`, each `(p_k r − r_k pr) / prev`. -/
def stepRows (k : Nat) (prev pk : Int) (pr : List Int) : Nat → List (List Int) → List (List Int)
  | _, [] => []
  | i, r :: rs =>
    (bif Nat.beq i k then r else divAll prev (comb pk (-(r.getD k 0)) r pr)) ::
      stepRows k prev pk pr (i + 1) rs

/-- One Bareiss step at pivot `k`. -/
def step (k : Nat) (prev : Int) (rows : List (List Int)) : List (List Int) :=
  stepRows k prev ((rows.getD k []).getD k 0) (rows.getD k []) 0 rows

/-- Fraction-free Gauss–Jordan from pivot `k` on, `fuel` pivots left: the last pivot and rows. -/
def gaussJordan : Nat → Nat → Int → List (List Int) → Option (Int × List (List Int))
  | 0, _, prev, rows => some (prev, rows)
  | fuel + 1, k, prev, rows =>
    match findPivot k 0 (rows.drop k) with
    | none => none
    | some i => gaussJordan fuel (k + 1) (((swapRows k (k + i) rows).getD k []).getD k 0)
        (step k prev (swapRows k (k + i) rows))

/-- The scale `d` and the matrix `N` of the elimination of `Γ`. -/
def invert (Γ : List (List Int)) : Option (Int × List (List Int)) :=
  match gaussJordan Γ.length 0 1 (augment Γ) with
  | none => none
  | some (d, rows) => some (d, rows.map fun r => r.drop Γ.length)

/-- The columns of a list of rows. -/
def cols : Nat → List (List Int) → List (List Int)
  | 0, _ => []
  | n + 1, rows => (rows.map fun r => r.headD 0) :: cols n (rows.map List.tail)

/-- Row `r` of `Γ N` against row `i` of `d · 1`, from column `j` on. -/
def rowOk (d : Int) (r : List Int) (i : Nat) : Nat → List (List Int) → Bool
  | _, [] => true
  | j, c :: cs => (dot r c == bif Nat.beq i j then d else 0) && rowOk d r i (j + 1) cs

/-- The rows of `Γ N` against `d · 1`, from row `i` on. -/
def mulRows (d : Int) (Ncols : List (List Int)) : Nat → List (List Int) → Bool
  | _, [] => true
  | i, r :: rs => rowOk d r i 0 Ncols && mulRows d Ncols (i + 1) rs

/-- The Gram matrix of a list of codes under `f`, as rows. -/
def gramOf (f : Nat → Nat → Int) (B : List Nat) : List (List Int) :=
  B.map fun a => B.map fun b => f a b

/-- `λᵀ E λ`. -/
def quad (E : List (List Int)) (l : List Int) : Int := dot l (E.map fun row => dot row l)

/-- The generator `g` lies in the span: the residual `d g − Σ λ_i b_i` has norm zero. -/
def memOk (d : Int) (N E : List (List Int)) (B : List Nat) (g : Nat) : Bool :=
  let l := N.map fun row => dot row (B.map fun b => g9 b g)
  d * d * dotE g g - 2 * d * dot l (B.map fun b => dotE b g) + quad E l == 0

/-- **The basis check.** -/
def basisOk (B gens : List Nat) : Bool :=
  B.all validCode && gens.all validCode &&
    match invert (gramOf g9 B) with
    | none => false
    | some (d, N) =>
      (d != 0) && mulRows d (cols B.length N) 0 (gramOf g9 B) &&
        gens.all fun g => B.contains g || memOk d N (gramOf dotE B) B g

end IntegerMultBounds.MathlibTM2.M8.Frames.RootCheck
