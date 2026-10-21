module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Transpose

/-!
# The stage-2 core from its pieces

On a bank `B u X` holding the bit array `X` on the view `u`, the core runs the interchange of a
descriptor `v` as nine programs (`core`): switch the headers to the top `n w` digits
(`top`), the three atomwise shears around two runs of the reversed family, switch the headers to
the low `r` digits (`low`), the leaf interchange there, and switch the headers back. Each piece
is a parameter with its contract on the bank; `core_hoare` composes them by `Stage2Wrapper.flf`
and `Stage2Wrapper.swap_split` into the transpose of the array, at the sum of the piece costs.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Core

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume index)
open Stage2Wrapper (Moves shear top low)
open RevMachine (RevT)
open FamilyRoot (ext)

variable {t : ℕ}

/-- A program run from every bank `B u X` with `P X Y` for some `Y`, ending at `B u' Y`. -/
def Step {s : ℕ} (M : Program t s prime) (B : Descriptor → (ℕ → ZMod 2) → Tapes t prime)
    (u u' : Descriptor) (P : (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop) (c : ℕ) : Prop :=
  ∀ X, HoareTime M (· = B u X) (fun z => ∃ Y, P X Y ∧ z = B u' Y) c

variable {B : Descriptor → (ℕ → ZMod 2) → Tapes t prime}

theorem Step.seq {s s' : ℕ} {M : Program t s prime} {N : Program t s' prime} {u u' u'' : Descriptor}
    {P Q : (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop} {c c' : ℕ}
    (hM : Step M B u u' P c) (hN : Step N B u' u'' Q c') :
    Step (Machine.seq M N) B u u'' (fun X Z => ∃ Y, P X Y ∧ Q Y Z) (c + 1 + c') := by
  intro X
  refine (hM X).seq (middle := fun z => ∃ Y, P X Y ∧ z = B u' Y) ?_
  intro z ⟨Y, hY, hz⟩
  obtain ⟨k, c₀, hk, hr, hh, Z, hZ, hc⟩ := hN Y z hz
  exact ⟨k, c₀, hk, hr, hh, Z, ⟨Y, hY, hZ⟩, hc⟩

theorem Step.mono {s : ℕ} {M : Program t s prime} {u u' : Descriptor}
    {P Q : (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop} {c c' : ℕ}
    (h : Step M B u u' P c) (hPQ : ∀ X Y, P X Y → Q X Y) (hc : c ≤ c') : Step M B u u' Q c' :=
  fun X => (h X).consequence (fun _ h => h) (fun _ ⟨Y, hY, hz⟩ => ⟨Y, hPQ X Y hY, hz⟩) hc

/-- The nine pieces in order. -/
def core {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : ℕ} (toTop : Program t s₁ prime) (shear₁ : Program t s₂ prime)
    (fam₁ : Program t s₃ prime) (shear₂ : Program t s₄ prime) (fam₂ : Program t s₅ prime)
    (shear₃ : Program t s₆ prime) (toLow : Program t s₇ prime) (leaf : Program t s₈ prime)
    (back : Program t s₉ prime) :=
  Machine.seq (Machine.seq (Machine.seq (Machine.seq (Machine.seq (Machine.seq (Machine.seq
    (Machine.seq toTop shear₁) fam₁) shear₂) fam₂) shear₃) toLow) leaf) back

/-- **The core.** Its pieces, run on the bank in order, interchange the array of `v`. -/
theorem core_hoare {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : ℕ} {toTop : Program t s₁ prime}
    {shear₁ : Program t s₂ prime} {fam₁ : Program t s₃ prime} {shear₂ : Program t s₄ prime}
    {fam₂ : Program t s₅ prime} {shear₃ : Program t s₆ prime} {toLow : Program t s₇ prime}
    {leaf : Program t s₈ prime} {back : Program t s₉ prime}
    {v : Descriptor} {r w n : ℕ} [NeZero (prime ^ w)] (hr : r ≤ v.width)
    (hw : (top prime r v).width = n * w) {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℕ}
    (h₁ : Step toTop B v (top prime r v) Eq c₁)
    (h₂ : Step shear₁ B (top prime r v) (top prime r v)
      (Moves prime (top prime r v) (shear (prime ^ w) n fun h d => d - h)) c₂)
    (h₃ : Step fam₁ B (top prime r v) (top prime r v) (RevT prime w n (top prime r v)) c₃)
    (h₄ : Step shear₂ B (top prime r v) (top prime r v)
      (Moves prime (top prime r v) (shear (prime ^ w) n fun h d => d + h)) c₄)
    (h₅ : Step fam₂ B (top prime r v) (top prime r v) (RevT prime w n (top prime r v)) c₅)
    (h₆ : Step shear₃ B (top prime r v) (top prime r v)
      (Moves prime (top prime r v) (shear (prime ^ w) n fun h d => h - d)) c₆)
    (h₇ : Step toLow B (top prime r v) (low prime r v) Eq c₇)
    (h₈ : Step leaf B (low prime r v) (low prime r v) (Moves prime (low prime r v) Prod.swap) c₈)
    (h₉ : Step back B (low prime r v) v Eq c₉) :
    Step (core toTop shear₁ fam₁ shear₂ fam₂ shear₃ toLow leaf back) B v v (Moves prime v Prod.swap)
      (c₁ + 1 + c₂ + 1 + c₃ + 1 + c₄ + 1 + c₅ + 1 + c₆ + 1 + c₇ + 1 + c₈ + 1 + c₉) :=
  ((((((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).seq h₇).seq h₈).seq h₉).mono
    (fun _ _ h => by
      obtain ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, rfl, m₂⟩, m₃⟩, m₄⟩, m₅⟩, m₆⟩, rfl⟩, m₈⟩, rfl⟩ := h
      have hq : 0 < prime := Networks.Shared50ModularControl.prime_prime.pos
      exact Stage2Wrapper.swap_split hq hr (Stage2Wrapper.flf hq hw m₂ m₃ m₄ m₅ m₆) m₈) le_rfl

/-- The bank depends on the array only within the volume. -/
def Local (B : Descriptor → (ℕ → ZMod 2) → Tapes t prime) : Prop :=
  ∀ u X Y, (∀ i < volume prime u, X i = Y i) → B u X = B u Y

/-- **The transpose.** On a local bank, a step whose moves are the swap ends with the transpose. -/
theorem transpose_hoare {s : ℕ} {M : Program t s prime} {v : Descriptor} {c : ℕ} (hB : Local B)
    (h : Step M B v v (Moves prime v Prod.swap) c) (x : Fin (volume prime v) → ZMod 2) :
    HoareTime M (· = B v (ext x))
      (· = B v (ext (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))) c := by
  refine (h (ext x)).consequence (fun _ h => h) ?_ le_rfl
  rintro z ⟨Y, hY, rfl⟩
  set y : Fin (volume prime v) → ZMod 2 := fun i => Y i
  have hYy : ∀ i < volume prime v, Y i = ext y i := fun i hi => by simp [ext, y, hi]
  have hm : Moves prime v Prod.swap (ext x) (ext y) := by
    intro a ha row hrow before hb h hh mid hm d hd after haf
    have e := Transpose.addr_val (v := v) ⟨a, ha⟩ ⟨row, hrow⟩ ⟨before, hb⟩ ⟨d, hd⟩ ⟨mid, hm⟩ ⟨h, hh⟩
      ⟨after, haf⟩
    simp only [Prod.swap_prod_mk] at e ⊢
    rw [← hYy _ (e ▸ (Transpose.addr _ _ _ _ _ _ _).isLt)]
    exact hY a ha row hrow before hb h hh mid hm d hd after haf
  rw [← Transpose.eq_transpose hm]
  exact hB v Y _ hYy

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Core
