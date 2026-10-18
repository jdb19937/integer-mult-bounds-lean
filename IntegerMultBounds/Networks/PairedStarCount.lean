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

/-! ### Fast evaluation

The kernel evaluates the count over arithmetic masks, sorted once per center,
in ten blocks of five rows so that no single check holds every row. -/

/-- Mask of coarse group `j`. -/
def grpMask (j : ℕ) : ℕ := if j < 24 then 3 * 2 ^ (2 * j) else if j = 24 then 2 ^ 48 else 0

/-- Mask of the coarse groups below `t`. -/
def lowMask (t : ℕ) : ℕ := 2 ^ min (2 * t) 49 - 1

def blockMask (w k : ℕ) : ℕ := (2 ^ w - 1) * 2 ^ (w * k)

/-- The masks of `fam v`, computed without building leaf lists. -/
def famMasks (v : ℕ) : List ℕ :=
  if v = 48 then
    (List.range 24).map grpMask ++ (List.range 12).map (blockMask 4) ++
      (List.range 6).map (blockMask 8) ++ (List.range 3).map (blockMask 16) ++
      [blockMask 16 0 + blockMask 16 2, 2 ^ 32 - 1, (2 ^ 32 - 1) * 2 ^ 16]
  else
    let i := v / 2
    let rest := 2 ^ 49 - 1 - grpMask i
    let pre (s : ℕ) := if s ≤ i then lowMask s else lowMask (s + 1) - grpMask i
    (((List.range 24).filter (· != i)).map grpMask ++ (List.range' 2 21).map pre) ++
    ((List.range' 2 21).map (fun s => rest - pre s) ++
      (List.range 24).map (fun t => rest - grpMask (if t < i then t else t + 1)) ++
      (List.range (2 * i)).map (fun a => rest - 2 ^ a))

theorem famMasks_eq : ∀ v < 49, (fam v).map maskOf = famMasks v := by decide +kernel

/-- The sorted masks of every center, shared by all copy pairs. -/
def sorts : List (List ℕ) := (List.range 49).map fun v => sortList (famMasks v)

theorem sortedMasks_eq (v : ℕ) (hv : v < 49) : sortedMasks v = sorts.getD v [] := by
  rw [sortedMasks, famMasks_eq v hv, sorts, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hv]
  rfl

def fastPair (c c' : ℕ) : ℕ :=
  mergeCount ((sorts.getD (c' - 1) []).map (liftMask c)) ((sorts.getD c []).map (liftMask c'))

def fastRow (c' : ℕ) : ℕ := sumNat ((List.range c').map fun c => fastPair c c')

theorem rowCount_eq (c' : ℕ) (hc' : c' ≤ 49) : rowCount c' = fastRow c' := by
  simp only [rowCount, fastRow]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  rw [List.mem_range] at hc
  simp only [pairCount, fastPair, lifted, sortedMasks_eq _ (show c' - 1 < 49 by omega),
    sortedMasks_eq _ (show c < 49 by omega)]

theorem sumNat_append (l l' : List ℕ) : sumNat (l ++ l') = sumNat l + sumNat l' := by
  induction l with
  | nil => simp [sumNat]
  | cons a as ih => simp [sumNat, ih, Nat.add_assoc]

theorem block0_eq : sumNat ((List.range' 0 5).map fastRow) = 716 := by
  decide +kernel

theorem block1_eq : sumNat ((List.range' 5 5).map fastRow) = 1829 := by
  decide +kernel

theorem block2_eq : sumNat ((List.range' 10 5).map fastRow) = 2826 := by
  decide +kernel

theorem block3_eq : sumNat ((List.range' 15 5).map fastRow) = 3569 := by
  decide +kernel

theorem block4_eq : sumNat ((List.range' 20 5).map fastRow) = 4336 := by
  decide +kernel

theorem block5_eq : sumNat ((List.range' 25 5).map fastRow) = 4809 := by
  decide +kernel

theorem block6_eq : sumNat ((List.range' 30 5).map fastRow) = 5346 := by
  decide +kernel

theorem block7_eq : sumNat ((List.range' 35 5).map fastRow) = 5549 := by
  decide +kernel

theorem block8_eq : sumNat ((List.range' 40 5).map fastRow) = 5856 := by
  decide +kernel

theorem block9_eq : sumNat ((List.range' 45 5).map fastRow) = 5420 := by
  decide +kernel

/-- All 40,256 merge matches over the copy pairs `c < c' < 50`. -/
theorem total_eq : sumNat ((List.range 50).map rowCount) = 40256 := by
  have hsplit : List.range 50 = List.range' 0 5 ++ List.range' 5 5 ++ List.range' 10 5 ++
      List.range' 15 5 ++ List.range' 20 5 ++ List.range' 25 5 ++ List.range' 30 5 ++
      List.range' 35 5 ++ List.range' 40 5 ++ List.range' 45 5 := by decide
  rw [List.map_congr_left fun c' hc' => rowCount_eq c' (by rw [List.mem_range] at hc'; omega), hsplit]
  simp only [List.map_append, sumNat_append, block0_eq, block1_eq, block2_eq, block3_eq, block4_eq,
    block5_eq, block6_eq, block7_eq, block8_eq, block9_eq]

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
theorem masks_increasing (v : ℕ) (hv : v < 49) : increasing (sortedMasks v) = true := by
  rw [sortedMasks_eq v hv]
  revert v
  decide +kernel

end IntegerMultBounds.Networks.PairedStarCount
