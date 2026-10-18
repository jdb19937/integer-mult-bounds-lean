module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Int.Basic

/-!
# The nine-stage recipe and its bank matrix

The selected bit node (upstream `global_k.py`, `recipe`) has `K` pairs of data banks, `2K` banks
in all: bank `2p` is side zero of pair `p` and bank `2p+1` side one. Its events are
* a local sweep on one pair, in forward or reverse orientation: forward adds side zero to side
  one, reverse subtracts side one from side zero;
* a bridge between two pairs with coefficient `±1`, made of two shears: `2d += c·2s` and
  `2s+1 += -c·(2d+1)`;
* the final exchange, which swaps the two sides of every pair with a sign.

`bankMatrix` is upstream's integer scalar eight-bank matrix (`small()`), built by row operations
from the identity. `recipe_identity` proves that the recipe at `K = 4` (nine stages) is the identity
on the eight banks, and `bridge_needed` proves that omitting any one of its 18 bridge shears is
not.
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

/-- An event of the nine-stage recipe. -/
inductive Event where
  | sweep (stage pair : ℕ) (reverse : Bool)
  | bridge (dst src : ℕ) (coefficient : ℤ)
  | exchange
  deriving DecidableEq, Repr

/-- The recipe of the `2K+1`-stage node (`global_k.py`, `recipe`). -/
def recipe (K : ℕ) : List Event :=
  [.sweep 0 0 false] ++
  ((List.range K).flatMap fun j =>
    [.sweep (2 * j + 1) j true] ++ (if j < K - 1 then [.bridge j (j + 1) 1] else []) ++
    [.sweep (2 * j + 2) j false] ++ (if j < K - 1 then [.bridge j (j + 1) (-1)] else [])) ++
  ((List.range (K - 1)).reverse.map fun j => .bridge (j + 1) j 1) ++
  [.exchange]

/-- Integer bank rows. -/
abbrev Rows := List (List ℤ)

def identityRows (n : ℕ) : Rows :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0

/-- Row `d` += `c` times row `s`. -/
def addRow (z : Rows) (d s : ℕ) (c : ℤ) : Rows :=
  z.set d (List.zipWith (fun x y => x + c * y) (z.getD d []) (z.getD s []))

/-- The exchange: rows `2j` and `2j+1` become row `2j+1` and minus row `2j`. -/
def exchangeRows (K : ℕ) (z : Rows) : Rows :=
  (List.range K).foldl (fun z j =>
    (z.set (2 * j) (z.getD (2 * j + 1) [])).set (2 * j + 1) ((z.getD (2 * j) []).map (- ·))) z

/-- One event on the rows, skipping the bridge shear with index `skip`; `count` numbers the
bridge shears seen so far. -/
def stepRows (K skip : ℕ) : Rows × ℕ → Event → Rows × ℕ
  | (z, count), .sweep _ p rev =>
      (if rev then addRow z (2 * p) (2 * p + 1) (-1) else addRow z (2 * p + 1) (2 * p) 1, count)
  | (z, count), .bridge d s c =>
      let z₁ := if count = skip then z else addRow z (2 * d) (2 * s) c
      let z₂ := if count + 1 = skip then z₁ else addRow z₁ (2 * s + 1) (2 * d + 1) (-c)
      (z₂, count + 2)
  | (z, count), .exchange => (exchangeRows K z, count)

/-- The bank matrix of the recipe, with the bridge shear `skip` omitted (`skip` beyond the last
shear omits nothing), and the number of bridge shears. -/
def bankMatrix (K skip : ℕ) : Rows × ℕ :=
  (recipe K).foldl (stepRows K skip) (identityRows (2 * K), 0)

/-- The nine-stage recipe has eighteen bridge shears and is the identity on the eight banks. -/
theorem recipe_identity : bankMatrix 4 18 = (identityRows 8, 18) := by
  decide +kernel

/-- Every one of the eighteen bridge shears is needed. -/
theorem bridge_needed : ∀ skip < 18, (bankMatrix 4 skip).1 ≠ identityRows 8 := by
  decide +kernel

theorem recipe_length : (recipe 4).length = 1 + 4 * 2 + 3 * 2 + 3 + 1 := by
  decide +kernel

/-- The sweep stages run through `0, …, 2K` in order, each once. -/
theorem sweep_stages : (recipe 4).filterMap (fun e => match e with
    | .sweep s _ _ => some s | _ => none) = List.range 9 := by
  decide +kernel

end IntegerMultBounds.Networks.Certificates.PR589.Nine
