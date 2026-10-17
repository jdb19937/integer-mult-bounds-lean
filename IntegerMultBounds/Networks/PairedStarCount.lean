module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Bitwise

/-! The star leaf sets shared between common-point copies. Every duplicate
support of the fifty-copy family joins a local center to a set of leaves; the
families below list, for each local center, the leaf sets whose stars the
recursive constructor builds. Copies `c < c'` meet on center `c' - 1` of copy
`c` and center `c` of copy `c'`. Their common leaf sets are counted by a merge
of the sorted lifted leaf masks, with no circuit evaluated. -/

@[expose] public section

namespace IntegerMultBounds.Networks.PairedStarCount

/-- Fine vertices of coarse group `j` among the `49` local vertices. -/
def grp (j : ℕ) : List ℕ := if j < 24 then [2 * j, 2 * j + 1] else if j = 24 then [48] else []

/-- The coarse groups other than `i`, in increasing order. -/
def others (i : ℕ) : List ℕ := (List.range 25).filter (· != i)

def leavesOf (js : List ℕ) : List ℕ := js.flatMap grp

/-- Dyadic block `k` of width `w`. -/
def block (w k : ℕ) : List ℕ := List.range' (w * k) w

/-- Leaf sets of the built stars at local center `v`. At the last vertex:
coarse edges of every level and three base sums. Elsewhere: the top strip
values, prefixes, suffixes and omissions, and the right cross sums. -/
def fam (v : ℕ) : List (List ℕ) :=
  if v = 48 then
    (List.range 24).map grp ++ (List.range 12).map (block 4) ++ (List.range 6).map (block 8) ++
      (List.range 3).map (block 16) ++ [block 16 0 ++ block 16 2, List.range 32, List.range' 16 32]
  else
    (((others (v / 2)).filter (· < 24)).map grp ++
      (List.range' 2 21).map (fun s => leavesOf ((others (v / 2)).take s))) ++
    ((List.range' 2 21).map (fun s => leavesOf ((others (v / 2)).drop s)) ++
      (List.range 24).map (fun t => leavesOf ((others (v / 2)).eraseIdx t)) ++
      (List.range (2 * (v / 2))).map (fun a => (leavesOf (others (v / 2))).erase a))

/-- Plain structural sum, reduced directly by the kernel. -/
def sumNat : List ℕ → ℕ
  | [] => 0
  | a :: as => a + sumNat as

def maskOf (xs : List ℕ) : ℕ := sumNat (xs.map (2 ^ ·))

/-- Insert a zero bit at position `c`: the mask of the `succAbove c` image. -/
def liftMask (c m : ℕ) : ℕ := m % 2 ^ c + 2 ^ (c + 1) * (m / 2 ^ c)

/-- Matches found by one merge pass over two lists. -/
def mergeCount : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | a :: as, bs => mergeGo a (mergeCount as) bs
where
  mergeGo (a : ℕ) (rest : List ℕ → ℕ) : List ℕ → ℕ
    | [] => 0
    | b :: bs => if a = b then rest bs + 1 else if a < b then rest (b :: bs) else mergeGo a rest bs

/-- Insertion into an increasing list. -/
def insertSorted (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertSorted a bs

def sortList : List ℕ → List ℕ
  | [] => []
  | a :: as => insertSorted a (sortList as)

/-- The leaf masks of center `v` in increasing order. -/
def sortedMasks (v : ℕ) : List ℕ := sortList ((fam v).map maskOf)

/-- Lifting preserves the order of masks, so lifted lists stay sorted. -/
def lifted (c v : ℕ) : List ℕ := (sortedMasks v).map (liftMask c)

/-- Common lifted leaf sets of copies `c < c'`. -/
def pairCount (c c' : ℕ) : ℕ := mergeCount (lifted c (c' - 1)) (lifted c' c)

def rowCount (c' : ℕ) : ℕ := sumNat ((List.range c').map fun c => pairCount c c')

def lowCount : ℕ := sumNat ((List.range 25).map rowCount)

def highCount : ℕ := sumNat ((List.range' 25 25).map rowCount)

theorem lowCount_eq : lowCount = 13276 := by decide +kernel

theorem highCount_eq : highCount = 26980 := by decide +kernel

/-- Strictly increasing, by one structural pass. -/
def increasing : List ℕ → Bool
  | a :: b :: rest => decide (a < b) && increasing (b :: rest)
  | _ => true

/-- A leaf list of a star at `v`: increasing, avoiding `v`, local, with
between two and forty-six leaves. -/
def leafShape (v : ℕ) (xs : List ℕ) : Bool :=
  increasing xs && !(xs.contains v) && xs.all (· < 49) && decide (2 ≤ xs.length) &&
    decide (xs.length ≤ 46)

theorem fam_shape : ∀ v < 49, (fam v).all (leafShape v) = true := by decide +kernel

/-- Distinct leaf lists at each center have distinct masks. -/
theorem masks_increasing : ∀ v < 49, increasing (sortedMasks v) = true := by decide +kernel

end IntegerMultBounds.Networks.PairedStarCount
