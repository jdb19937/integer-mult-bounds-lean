module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Recipe
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic

/-!
# The nine-stage recipe on banks over `F₂`

`stepBank` is one recipe event on a bank vector `x : ℕ → M` in any `F₂`-module, banks `2p` and
`2p+1` being the two sides of pair `p`. Over `F₂` the signs of the integer bank matrix
(`Recipe.lean`) vanish:
* a forward sweep adds side zero to side one, a reverse sweep adds side one to side zero;
* a bridge `(d, s)` adds bank `2s` to bank `2d`, then bank `2d+1` to bank `2s+1`;
* the exchange swaps the two sides of every pair.

`stepBank` commutes with additive maps (`runBank_map`) and reads and writes only the eight data
banks (`runBank_congr`, `runBank_high`). Evaluating the recipe once on the coefficient vectors of
the eight banks therefore decides it on every module. `recipe_runBank` proves that the
nine-stage recipe is the identity on banks of every `F₂`-module.
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

variable {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup N] [Module (ZMod 2) N]

/-- One recipe event on `2K` banks (`K` pairs). -/
def stepBank (K : ℕ) (x : ℕ → M) : Event → ℕ → M
  | .sweep _ p rev =>
      if rev then Function.update x (2 * p) (x (2 * p) + x (2 * p + 1))
      else Function.update x (2 * p + 1) (x (2 * p + 1) + x (2 * p))
  | .bridge d s _ =>
      let x₁ := Function.update x (2 * d) (x (2 * d) + x (2 * s))
      Function.update x₁ (2 * s + 1) (x₁ (2 * s + 1) + x₁ (2 * d + 1))
  | .exchange => fun i => if i < 2 * K then x (if i % 2 = 0 then i + 1 else i - 1) else x i

def runBank (K : ℕ) (es : List Event) (x : ℕ → M) : ℕ → M := es.foldl (stepBank K) x

/-- The event touches only the eight data banks. -/
def localEvent : Event → Bool
  | .sweep _ p _ => decide (p < 4)
  | .bridge d s _ => decide (d < 4 ∧ s < 4)
  | .exchange => true

theorem recipe_local : (recipe 4).all localEvent = true := by
  decide +kernel

theorem stepBank_map (K : ℕ) (φ : M →+ N) (x : ℕ → M) (e : Event) :
    stepBank K (fun i => φ (x i)) e = fun i => φ (stepBank K x e i) := by
  funext i
  cases e with
  | sweep st p rev =>
      cases rev <;> simp only [stepBank, Bool.false_eq_true, ↓reduceIte, Function.update_apply] <;>
        split_ifs <;> simp [map_add]
  | bridge d s c =>
      simp only [stepBank, Function.update_apply]
      split_ifs <;> simp [map_add]
  | exchange =>
      simp only [stepBank]
      split <;> rfl

theorem runBank_map (K : ℕ) (φ : M →+ N) (es : List Event) (x : ℕ → M) :
    runBank K es (fun i => φ (x i)) = fun i => φ (runBank K es x i) := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    simp only [runBank, List.foldl_cons] at ih ⊢
    rw [stepBank_map, ih]

theorem stepBank_high (e : Event) (he : localEvent e = true) (x : ℕ → M) (i : ℕ) (hi : 8 ≤ i) :
    stepBank 4 x e i = x i := by
  cases e with
  | sweep st p rev =>
      simp only [localEvent, decide_eq_true_eq] at he
      cases rev <;> simp [stepBank, Function.update_apply, show i ≠ 2 * p by omega,
        show i ≠ 2 * p + 1 by omega]
  | bridge d s c =>
      simp only [localEvent, decide_eq_true_eq] at he
      simp [stepBank, Function.update_apply, show i ≠ 2 * d by omega, show i ≠ 2 * s + 1 by omega]
  | exchange =>
      simp [stepBank, show ¬i < 2 * 4 by omega]

theorem stepBank_congr (e : Event) (he : localEvent e = true) (x y : ℕ → M)
    (hxy : ∀ k < 8, x k = y k) : ∀ i < 8, stepBank 4 x e i = stepBank 4 y e i := by
  intro i hi
  cases e with
  | sweep st p rev =>
      simp only [localEvent, decide_eq_true_eq] at he
      cases rev <;> simp only [stepBank, Bool.false_eq_true, ↓reduceIte, Function.update_apply] <;>
        split_ifs <;> simp only [hxy _ hi, hxy (2 * p) (by omega), hxy (2 * p + 1) (by omega)]
  | bridge d s c =>
      simp only [localEvent, decide_eq_true_eq] at he
      simp only [stepBank, Function.update_apply]
      split_ifs <;> simp only [hxy _ hi, hxy (2 * d) (by omega), hxy (2 * s) (by omega),
        hxy (2 * d + 1) (by omega), hxy (2 * s + 1) (by omega)]
  | exchange =>
      simp only [stepBank, if_pos (show i < 2 * 4 by omega)]
      split_ifs <;> exact hxy _ (by omega)

theorem runBank_high (es : List Event) (hes : es.all localEvent = true) (x : ℕ → M) (i : ℕ)
    (hi : 8 ≤ i) : runBank 4 es x i = x i := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hes
    simp only [runBank, List.foldl_cons] at ih ⊢
    rw [ih hes.2, stepBank_high e hes.1 x i hi]

theorem runBank_congr (es : List Event) (hes : es.all localEvent = true) (x y : ℕ → M)
    (hxy : ∀ k < 8, x k = y k) : ∀ i < 8, runBank 4 es x i = runBank 4 es y i := by
  induction es generalizing x y with
  | nil => exact hxy
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hes
    simp only [runBank, List.foldl_cons] at ih ⊢
    exact ih hes.2 _ _ (stepBank_congr e hes.1 x y hxy)

/-- The coefficient vectors of the eight banks. -/
def unitBanks (i : ℕ) : Fin 8 → ZMod 2 := fun j => if i = j.val then 1 else 0

/-- The recipe computed once on the coefficient vectors. -/
theorem recipe_unitBanks : ∀ i < 8, runBank 4 (recipe 4) unitBanks i = unitBanks i := by
  decide +kernel

/-- **The nine-stage recipe is the identity** on the eight banks of every `F₂`-module, and it
leaves every other bank alone. -/
theorem recipe_runBank (x : ℕ → M) : runBank 4 (recipe 4) x = x := by
  funext i
  by_cases hi : i < 8
  · let φ : (Fin 8 → ZMod 2) →+ M :=
      { toFun := fun v => ∑ j : Fin 8, v j • x j.val
        map_zero' := by simp
        map_add' := by intro v w; simp [add_smul, Finset.sum_add_distrib] }
    have hx : ∀ k < 8, φ (unitBanks k) = x k := by
      intro k hk
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, unitBanks]
      rw [Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro j _ hj
        have : k ≠ j.val := fun h => hj (Fin.ext h.symm)
        simp [this]
      · simp
    have hloc := runBank_congr (recipe 4) recipe_local x (fun k => φ (unitBanks k))
      (fun k hk => (hx k hk).symm) i hi
    rw [hloc, runBank_map 4 φ (recipe 4) unitBanks]
    beta_reduce
    rw [recipe_unitBanks i hi, hx i hi]
  · exact runBank_high (recipe 4) recipe_local x i (by omega)

end IntegerMultBounds.Networks.Certificates.PR589.Nine
