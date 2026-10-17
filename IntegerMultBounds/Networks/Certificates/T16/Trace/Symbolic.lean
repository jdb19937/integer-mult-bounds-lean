module

public import IntegerMultBounds.Networks.FramedCircuit
import Mathlib.Tactic.Ring

/-! A kernel-evaluable symbolic interpreter for rational register programs. Each register holds
a sparse rational row over the input registers, stored in a complete binary trie. Soundness
says that a successful symbolic run computes `moduleRun` exactly, on every module. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace.Symbolic

open FramedCircuit

/-- A sparse rational row, sorted by register with no zero coefficients. -/
abbrev Row := List (ℕ × ℚ)

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

def Row.eval (r : Row) (x : ℕ → E) : E := (r.map fun p => p.2 • x p.1).sum

@[simp] theorem Row.eval_nil (x : ℕ → E) : Row.eval [] x = 0 := rfl

@[simp] theorem Row.eval_cons (p : ℕ × ℚ) (r : Row) (x : ℕ → E) :
    Row.eval (p :: r) x = p.2 • x p.1 + Row.eval r x := rfl

/-- Add `c` times register `j` to a sorted row. -/
def Row.insert (j : ℕ) (c : ℚ) : Row → Row
  | [] => if c = 0 then [] else [(j, c)]
  | (k, a) :: r =>
    if j < k then (if c = 0 then (k, a) :: r else (j, c) :: (k, a) :: r)
    else if j = k then (if a + c = 0 then r else (k, a + c) :: r)
    else (k, a) :: Row.insert j c r

theorem Row.eval_insert (j : ℕ) (c : ℚ) (r : Row) (x : ℕ → E) :
    (Row.insert j c r).eval x = c • x j + r.eval x := by
  induction r with
  | nil =>
    unfold Row.insert
    split_ifs with h
    · simp [h]
    · simp
  | cons p r ih =>
    obtain ⟨k, a⟩ := p
    unfold Row.insert
    split_ifs with h1 h2 h3 h4
    · simp [h2]
    · simp
    · subst h3
      rw [Row.eval_cons]
      have e : c • x j + a • x j = 0 := by rw [← add_smul, add_comm, h4, zero_smul]
      rw [← add_assoc, e, zero_add]
    · subst h3
      rw [Row.eval_cons, Row.eval_cons, add_smul]
      abel
    · rw [Row.eval_cons, Row.eval_cons, ih]
      abel

/-- Add `c` times a row to a row. -/
def Row.addScaled (c : ℚ) (s t : Row) : Row :=
  s.foldl (fun acc p => acc.insert p.1 (c * p.2)) t

theorem Row.eval_addScaled (c : ℚ) (s t : Row) (x : ℕ → E) :
    (Row.addScaled c s t).eval x = t.eval x + c • s.eval x := by
  induction s generalizing t with
  | nil => simp [Row.addScaled]
  | cons p s ih =>
    simp only [Row.addScaled, List.foldl_cons] at ih ⊢
    rw [ih, Row.eval_insert, Row.eval_cons, smul_add, mul_smul]
    abel

/-- Linear-time `t + c • s` for sorted rows, with fuel; without fuel it falls back to
`addScaled`, so it is correct for all inputs. -/
def Row.merge : ℕ → ℚ → Row → Row → Row
  | 0, c, s, t => Row.addScaled c s t
  | _ + 1, _, [], t => t
  | n + 1, c, (j, a) :: s, [] =>
    if c * a = 0 then Row.merge n c s [] else (j, c * a) :: Row.merge n c s []
  | n + 1, c, (j, a) :: s, (k, b) :: t =>
    if j < k then
      (if c * a = 0 then Row.merge n c s ((k, b) :: t)
       else (j, c * a) :: Row.merge n c s ((k, b) :: t))
    else if k < j then (k, b) :: Row.merge n c ((j, a) :: s) t
    else if b + c * a = 0 then Row.merge n c s t else (k, b + c * a) :: Row.merge n c s t

theorem Row.eval_merge (n : ℕ) (c : ℚ) (s t : Row) (x : ℕ → E) :
    (Row.merge n c s t).eval x = t.eval x + c • s.eval x := by
  induction n generalizing s t with
  | zero => exact Row.eval_addScaled c s t x
  | succ n ih =>
    match s, t with
    | [], t => simp [Row.merge]
    | (j, a) :: s, [] =>
      unfold Row.merge
      split_ifs with h
      · rw [ih]
        simp only [Row.eval_cons, Row.eval_nil, smul_add, smul_smul, h, zero_smul]
        abel
      · rw [Row.eval_cons, ih]
        simp only [Row.eval_cons, Row.eval_nil, smul_add, smul_smul]
        abel
    | (j, a) :: s, (k, b) :: t =>
      unfold Row.merge
      split_ifs with h1 h2 h3 h4
      · rw [ih]
        simp only [Row.eval_cons, smul_add, smul_smul, h2, zero_smul]
        abel
      · rw [Row.eval_cons, ih]
        simp only [Row.eval_cons, smul_add, smul_smul]
        abel
      · rw [Row.eval_cons, ih]
        simp only [Row.eval_cons, smul_add, smul_smul]
        abel
      · obtain rfl : j = k := by omega
        rw [ih]
        simp only [Row.eval_cons, smul_add, smul_smul]
        have e : b • x j + (c * a) • x j = 0 := by rw [← add_smul, h4, zero_smul]
        rw [show b • x j + Row.eval t x + ((c * a) • x j + c • Row.eval s x) =
          (b • x j + (c * a) • x j) + (Row.eval t x + c • Row.eval s x) by abel, e, zero_add]
      · obtain rfl : j = k := by omega
        rw [Row.eval_cons, ih]
        simp only [Row.eval_cons, smul_add, smul_smul, add_smul]
        abel

/-! ### Register tries -/

inductive Trie where
  | leaf (r : Row)
  | fork (even odd : Trie)
  deriving DecidableEq

def Trie.get : Trie → ℕ → Row
  | .leaf r, i => if i = 0 then r else []
  | .fork even odd, i => if i % 2 = 0 then even.get (i / 2) else odd.get (i / 2)

def Trie.put : Trie → ℕ → Row → Trie
  | .leaf r, i, next => .leaf (if i = 0 then next else r)
  | .fork even odd, i, next =>
    if i % 2 = 0 then .fork (even.put (i / 2) next) odd else .fork even (odd.put (i / 2) next)

/-- A complete trie of the given depth. -/
def Trie.Full : ℕ → Trie → Prop
  | 0, .leaf _ => True
  | n + 1, .fork even odd => Trie.Full n even ∧ Trie.Full n odd
  | _, _ => False

theorem Trie.full_put : ∀ (n : ℕ) (T : Trie) (i : ℕ) (r : Row), T.Full n → (T.put i r).Full n
  | 0, .leaf _, _, _, _ => trivial
  | n + 1, .fork e o, i, r, h => by
    unfold Trie.put
    split_ifs
    · exact ⟨Trie.full_put n e _ r h.1, h.2⟩
    · exact ⟨h.1, Trie.full_put n o _ r h.2⟩
  | 0, .fork _ _, _, _, h => (by simp [Trie.Full] at h)
  | _ + 1, .leaf _, _, _, h => (by simp [Trie.Full] at h)

theorem Trie.get_put_self : ∀ (n : ℕ) (T : Trie) (i : ℕ) (r : Row), T.Full n → i < 2 ^ n →
    (T.put i r).get i = r
  | 0, .leaf _, i, r, _, hi => by
    have : i = 0 := by simpa using hi
    subst this
    simp [Trie.put, Trie.get]
  | n + 1, .fork e o, i, r, h, hi => by
    have hi' : i / 2 < 2 ^ n := by rw [pow_succ] at hi; omega
    unfold Trie.put
    split_ifs with h2
    · simp only [Trie.get, h2, ite_true]
      exact Trie.get_put_self n e _ r h.1 hi'
    · simp only [Trie.get, h2, ite_false]
      exact Trie.get_put_self n o _ r h.2 hi'
  | 0, .fork _ _, _, _, h, _ => (by simp [Trie.Full] at h)
  | _ + 1, .leaf _, _, _, h, _ => (by simp [Trie.Full] at h)

theorem Trie.get_put_other : ∀ (T : Trie) (i j : ℕ) (r : Row), i ≠ j → (T.put j r).get i = T.get i
  | .leaf old, i, j, r, h => by
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp_all [Trie.put, Trie.get]
  | .fork e o, i, j, r, h => by
    by_cases hi : i % 2 = 0 <;> by_cases hj : j % 2 = 0
    · simpa [Trie.put, Trie.get, hi, hj] using Trie.get_put_other e (i / 2) (j / 2) r (by omega)
    · simp [Trie.put, Trie.get, hi, hj]
    · simp [Trie.put, Trie.get, hi, hj]
    · simpa [Trie.put, Trie.get, hi, hj] using Trie.get_put_other o (i / 2) (j / 2) r (by omega)

/-- The identity trie: register `base + stride * j` at position `j`. -/
def Trie.init : ℕ → ℕ → ℕ → Trie
  | 0, base, _ => .leaf [(base, 1)]
  | n + 1, base, stride => .fork (Trie.init n base (2 * stride)) (Trie.init n (base + stride) (2 * stride))

theorem Trie.full_init : ∀ n base stride, (Trie.init n base stride).Full n
  | 0, _, _ => trivial
  | n + 1, _, _ => ⟨Trie.full_init n _ _, Trie.full_init n _ _⟩

theorem Trie.get_init : ∀ (n base stride j : ℕ), j < 2 ^ n →
    (Trie.init n base stride).get j = [(base + stride * j, 1)]
  | 0, base, stride, j, hj => by
    have : j = 0 := by simpa using hj
    subst this
    simp [Trie.init, Trie.get]
  | n + 1, base, stride, j, hj => by
    have hj' : j / 2 < 2 ^ n := by rw [pow_succ] at hj; omega
    simp only [Trie.init, Trie.get]
    split_ifs with h
    · rw [Trie.get_init n _ _ _ hj']
      have hj2 : 2 * (j / 2) = j := by omega
      have e : base + 2 * stride * (j / 2) = base + stride * j := by
        conv_rhs => rw [← hj2]
        ring
      rw [e]
    · rw [Trie.get_init n _ _ _ hj']
      have hj2 : 2 * (j / 2) + 1 = j := by omega
      have e : base + stride + 2 * stride * (j / 2) = base + stride * j := by
        conv_rhs => rw [← hj2]
        ring
      rw [e]

/-! ### Symbolic execution -/

/-- Number of registers interpreted symbolically. -/
def bound : ℕ := 712

/-- The new row of a gate's target, reading every source before writing. -/
def gateRow (T : Trie) (g : Circuit.Gate ℕ ℚ) : Row :=
  g.terms.foldl (fun acc p =>
    Row.merge ((T.get p.1).length + acc.length + 1) p.2 (T.get p.1) acc) (T.get g.target)

/-- The length test is always true for normalized rows; it forces the new row during kernel
evaluation, so long programs do not accumulate deferred work. -/
def symStep (T : Trie) (g : Circuit.Gate ℕ ℚ) : Option Trie :=
  let row := gateRow T g
  if g.target < bound ∧ g.terms.all (fun p => decide (p.1 < bound)) ∧ row.length ≤ 4096 then
    some (T.put g.target row)
  else none

def symRun : Trie → List (Circuit.Gate ℕ ℚ) → Option Trie
  | T, [] => some T
  | T, g :: gs => (symStep T g).bind fun T' => symRun T' gs

/-- `T` represents `y` over inputs `x`: registers below the bound are their rows, and the rest
are untouched. -/
def Represents (T : Trie) (y x : ℕ → E) : Prop :=
  T.Full 10 ∧ (∀ i < bound, y i = (T.get i).eval x) ∧ (∀ i, bound ≤ i → y i = x i)

theorem represents_init (x : ℕ → E) : Represents (Trie.init 10 0 1) x x := by
  refine ⟨Trie.full_init _ _ _, fun i hi => ?_, fun _ _ => rfl⟩
  rw [Trie.get_init 10 0 1 i (by unfold bound at hi; norm_num; omega)]
  simp

theorem eval_gateRow (T : Trie) (g : Circuit.Gate ℕ ℚ) (y x : ℕ → E)
    (hT : ∀ i < bound, y i = (T.get i).eval x) (hs : ∀ p ∈ g.terms, p.1 < bound)
    (ht : g.target < bound) :
    (gateRow T g).eval x = y g.target + (g.terms.map fun p => p.2 • y p.1).sum := by
  unfold gateRow
  suffices h : ∀ (ts : List (ℕ × ℚ)) (acc : Row), (∀ p ∈ ts, p.1 < bound) →
      (ts.foldl (fun acc p =>
        Row.merge ((T.get p.1).length + acc.length + 1) p.2 (T.get p.1) acc) acc).eval x =
        acc.eval x + (ts.map fun p => p.2 • y p.1).sum by
    rw [h g.terms _ hs, ← hT _ ht]
  intro ts
  induction ts with
  | nil => intro acc _; simp
  | cons p ts ih =>
    intro acc hp
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih _ (fun q hq => hp q (List.mem_cons_of_mem _ hq)), Row.eval_merge,
      hT _ (hp p List.mem_cons_self)]
    abel

theorem symStep_sound {T T' : Trie} {g : Circuit.Gate ℕ ℚ} {y x : ℕ → E}
    (h : symStep T g = some T') (hr : Represents T y x) :
    Represents T' (moduleGate g y) x := by
  unfold symStep at h
  dsimp only at h
  split_ifs at h with hg
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨ht, hs, -⟩ := hg
  have hs' : ∀ p ∈ g.terms, p.1 < bound := fun p hp => by
    have := List.all_eq_true.mp hs p hp
    simpa using this
  obtain ⟨hfull, hlow, hhigh⟩ := hr
  refine ⟨Trie.full_put _ _ _ _ hfull, fun i hi => ?_, fun i hi => ?_⟩
  · by_cases hit : i = g.target
    · subst hit
      rw [Trie.get_put_self 10 _ _ _ hfull (by unfold bound at hi; norm_num; omega)]
      rw [eval_gateRow T g y x hlow hs' ht]
      simp [moduleGate]
    · rw [Trie.get_put_other _ _ _ _ hit]
      simp [moduleGate, Function.update_of_ne hit, hlow i hi]
  · have hit : i ≠ g.target := by omega
    simp [moduleGate, Function.update_of_ne hit, hhigh i hi]

theorem symRun_sound : ∀ {T T' : Trie} {gs : List (Circuit.Gate ℕ ℚ)} {y x : ℕ → E},
    symRun T gs = some T' → Represents T y x → Represents T' (moduleRun gs y) x
  | T, T', [], y, x, h, hr => by
    simp only [symRun, Option.some.injEq] at h
    subst h
    exact hr
  | T, T', g :: gs, y, x, h, hr => by
    simp only [symRun] at h
    cases hs : symStep T g with
    | none => simp [hs] at h
    | some U =>
      rw [hs, Option.bind_some] at h
      exact symRun_sound (y := moduleGate g y) h (symStep_sound hs hr)

/-- Successful symbolic execution from the identity trie computes `moduleRun` exactly. -/
theorem moduleRun_eq_of_symRun {gs : List (Circuit.Gate ℕ ℚ)} {T : Trie}
    (h : symRun (Trie.init 10 0 1) gs = some T) (x : ℕ → E) :
    (∀ i < bound, moduleRun gs x i = (T.get i).eval x) ∧
      (∀ i, bound ≤ i → moduleRun gs x i = x i) :=
  (symRun_sound h (represents_init x)).2

end IntegerMultBounds.Networks.Certificates.T16.Trace.Symbolic
