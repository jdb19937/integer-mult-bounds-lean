module

public import IntegerMultBounds.Compact.ExactRepair
public import Mathlib.Data.Bool.Basic

/-!
# Packed shears controlled by preserved source data

The source bits may be read from an arbitrary unchanged field, which can also
contain spectators. A fixed-length hypothesis gives one rectangular address
space, rather than a different space for each source value. The packed program
is a permutation even on bad addresses; its good-set endpoint restores both
borrowed fields and XORs the target parities. This is address arithmetic only:
the source reader still needs a costed physical implementation.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Packed

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

/-- Low bit of a packed digit. -/
def parity (v : ℤ) : Bool := decide (v % 2 = 1)

theorem parity_toggle (v z : ℤ) (hz : z = 0 ∨ z = 1) :
    parity (toggle v z) = Bool.xor (parity v) (parity z) := by
  rcases hz with rfl | rfl
  · simp [parity, toggle]
  · by_cases hv : v % 2 = 1
    · simp [parity, toggle, hv]
      omega
    · have h : (v + (1 - 2 * (v % 2))) % 2 = 1 := by omega
      simp [parity, toggle, hv, h]

theorem parities_toggleList (vs zs : List ℤ) (hz : Bits zs) :
    (toggleList vs zs).map parity = List.zipWith Bool.xor (vs.map parity) (zs.map parity) := by
  induction vs generalizing zs with
  | nil => simp [toggleList]
  | cons v vs ih =>
    cases zs with
    | nil => simp [toggleList]
    | cons z zs =>
      have hz₀ := hz z (by simp)
      have hzs : Bits zs := fun a ha => hz a (by simp [ha])
      simpa [toggleList, parity_toggle v z hz₀] using congrArg
        (List.cons (Bool.xor (parity v) (parity z))) (ih zs hzs)

/-- Target guards and all bits above each selected low bit stay unchanged. -/
theorem upper_toggleList (vs zs : List ℤ) (hlen : vs.length = zs.length) (hz : Bits zs) :
    (toggleList vs zs).map (fun v => v / 2) = vs.map (fun v => v / 2) := by
  induction vs generalizing zs with
  | nil => simp [toggleList]
  | cons v vs ih =>
    cases zs with
    | nil => simp at hlen
    | cons z zs =>
      have hz₀ := hz z (by simp)
      have hzs : Bits zs := fun a ha => hz a (by simp [ha])
      simp only [toggleList, List.zipWith_cons_cons, List.map_cons]
      rw [toggle_guard v z hz₀]
      exact congrArg (List.cons (v / 2)) (ih zs (by simpa using hlen) hzs)

/-- The existing modular program transported to its fixed physical field width. -/
def step (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) : Equiv.Perm (LateAddress B L n) :=
  hlen ▸ packedLatePerm (2 * L) B (by omega) (by omega) zs

def ideal (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs) : Equiv.Perm (LateAddress B L n) :=
  hlen ▸ lateIdeal B L hL zs hz

theorem step_eq_ideal (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs)
    (x : LateAddress B L n) (hx : lateGood B L n x) :
    step B L hB hL zs hlen x = ideal B L hL zs hlen hz x := by
  subst n
  exact late_program_agrees_on_good B L hB hL zs hz x hx

theorem ideal_good (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs) (x : LateAddress B L n) :
    lateGood B L n (ideal B L hL zs hlen hz x) ↔ lateGood B L n x := by
  subst n
  exact lateIdeal_preserves_good B L hL zs hz x

/-- The ideal endpoint preserves both borrowed fields and changes just digit parities. -/
theorem ideal_endpoint (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs) (x : LateAddress B L n) :
    let y := ideal B L hL zs hlen hz x
    y.1 = x.1 ∧ y.2.2 = x.2.2 ∧
      (digits (2 * L) n y.2.1.val).map parity =
        List.zipWith Bool.xor ((digits (2 * L) n x.2.1.val).map parity) (zs.map parity) := by
  subst n
  refine ⟨rfl, rfl, ?_⟩
  change (digits (2 * L) zs.length (idealTarget L hL zs hz x.2.1).val).map parity = _
  rw [idealTarget_digits, parities_toggleList _ _ hz]

theorem ideal_upper (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs) (x : LateAddress B L n) :
    (digits (2 * L) n (ideal B L hL zs hlen hz x).2.1.val).map (fun v => v / 2) =
      (digits (2 * L) n x.2.1.val).map (fun v => v / 2) := by
  subst n
  change (digits (2 * L) zs.length (idealTarget L hL zs hz x.2.1).val).map _ = _
  rw [idealTarget_digits, upper_toggleList _ _ (digits_length ..) hz]

variable {C : Type*} {n : ℕ}

/-- The entire unchanged source/spectator field selects one packed program. -/
def program (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (read : C → List ℤ) (hlen : ∀ c, (read c).length = n) :
    Equiv.Perm (C × LateAddress B L n) :=
  fiberPerm fun c => step B L hB hL (read c) (hlen c)

def target (B L : ℤ) (hL : 0 < L) (read : C → List ℤ)
    (hlen : ∀ c, (read c).length = n) (hbits : ∀ c, Bits (read c)) :
    Equiv.Perm (C × LateAddress B L n) :=
  fiberPerm fun c => ideal B L hL (read c) (hlen c) (hbits c)

@[simp] theorem program_source (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (read : C → List ℤ) (hlen : ∀ c, (read c).length = n) (x : C × LateAddress B L n) :
    (program B L hB hL read hlen x).1 = x.1 := rfl

theorem program_good (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (read : C → List ℤ) (hlen : ∀ c, (read c).length = n) (hbits : ∀ c, Bits (read c))
    (x : C × LateAddress B L n) (hx : lateGood B L n x.2) :
    program B L hB hL read hlen x = target B L hL read hlen hbits x := by
  apply Prod.ext
  · rfl
  exact step_eq_ideal B L hB hL (read x.1) (hlen x.1) (hbits x.1) x.2 hx

/-- No assumption on the source values or spectators enters the guard invariant. -/
theorem target_good (B L : ℤ) (hL : 0 < L)
    (read : C → List ℤ) (hlen : ∀ c, (read c).length = n) (hbits : ∀ c, Bits (read c))
    (x : C × LateAddress B L n) :
    lateGood B L n (target B L hL read hlen hbits x).2 ↔ lateGood B L n x.2 :=
  ideal_good B L hL (read x.1) (hlen x.1) (hbits x.1) x.2

/-- Full good-set contract of the actual modular permutation, including upper digits. -/
theorem program_endpoint (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (read : C → List ℤ) (hlen : ∀ c, (read c).length = n) (hbits : ∀ c, Bits (read c))
    (x : C × LateAddress B L n) (hx : lateGood B L n x.2) :
    let y := program B L hB hL read hlen x
    y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2.2 = x.2.2.2 ∧
      (digits (2 * L) n y.2.2.1.val).map (fun v => v / 2) =
        (digits (2 * L) n x.2.2.1.val).map (fun v => v / 2) ∧
      (digits (2 * L) n y.2.2.1.val).map parity =
        List.zipWith Bool.xor ((digits (2 * L) n x.2.2.1.val).map parity)
          ((read x.1).map parity) := by
  dsimp only
  rw [program_good B L hB hL read hlen hbits x hx]
  obtain ⟨hu, hw, hp⟩ := ideal_endpoint B L hL (read x.1) (hlen x.1) (hbits x.1) x.2
  exact ⟨rfl, hu, hw, ideal_upper B L hL (read x.1) (hlen x.1) (hbits x.1) x.2, hp⟩

/-- Exceptional addresses are neither lost nor introduced by the packed program. -/
theorem program_bad (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (read : C → List ℤ) (hlen : ∀ c, (read c).length = n) (hbits : ∀ c, Bits (read c))
    (x : C × LateAddress B L n) :
    (¬lateGood B L n (program B L hB hL read hlen x).2) ↔ ¬lateGood B L n x.2 := by
  apply actual_preserves_bad (program B L hB hL read hlen)
    (target B L hL read hlen hbits) (fun y => ¬lateGood B L n y.2)
  · intro y
    exact not_congr (target_good B L hL read hlen hbits y)
  · intro y hy
    exact program_good B L hB hL read hlen hbits y (Classical.not_not.mp hy)

/-- The packed fiber program now meets the generic exact-repair interface. -/
theorem repair_program (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (read : C → List ℤ) (hlen : ∀ c, (read c).length = n) (hbits : ∀ c, Bits (read c))
    (x : C × LateAddress B L n) :
    let S := program B L hB hL read hlen
    let T := target B L hL read hlen hbits
    (if ¬lateGood B L n (S x).2 then T (S.symm (S x)) else S x) = T x := by
  apply repair_exact (program B L hB hL read hlen) (target B L hL read hlen hbits)
    (fun y => ¬lateGood B L n y.2)
  · intro y
    exact not_congr (target_good B L hL read hlen hbits y)
  · intro y hy
    exact program_good B L hB hL read hlen hbits y (Classical.not_not.mp hy)

end IntegerMultBounds.MathlibTM2.Routing.Packed
