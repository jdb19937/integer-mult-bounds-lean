module

public import IntegerMultBounds.Schoenhage.TwistTape
public import IntegerMultBounds.Schoenhage.Relabel

/-! The recordwise monomial over a whole array. A fifteen-tape word program
runs the eleven-tape monomial on its first tapes once per record, loading the
record's head count, tail count and the two sign flags from four descriptor
lists (`runs_twistArray`): from the component words of records `fᵢ` with
exponents `Eᵢ`, the output gains the component words of `y^(Eᵢ) fᵢ`, in
`O(M r w)` steps for `M` records. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct

namespace TwistArray

open TwistTape

/-- The monomial's tapes inside the larger bank. -/
def κ : Fin 11 → Fin 15 := Fin.castLE (by norm_num)

theorem κ_injective : Function.Injective κ := Fin.castLE_injective _

/-- Replace the first eleven tapes of `τ` by `σ`. -/
def ext (τ : Fin 15 → WTape) (σ : Fin 11 → WTape) : Fin 15 → WTape :=
  fun x => if h : x.val < 11 then σ ⟨x.val, h⟩ else τ x

theorem ext_self (τ : Fin 15 → WTape) : ext τ (τ ∘ κ) = τ := by
  funext x; unfold ext; split_ifs <;> rfl

theorem ext_update (τ : Fin 15 → WTape) (σ : Fin 11 → WTape) (i : Fin 11) (v : WTape) :
    ext τ (Function.update σ i v) = Function.update (ext τ σ) (κ i) v := by
  funext x
  unfold ext
  by_cases hx : x = κ i
  · subst hx; simp [κ]
  · rw [Function.update_of_ne hx]
    split_ifs with h
    · have : (⟨x.val, h⟩ : Fin 11) ≠ i := fun e => hx (by ext; simp [κ, ← e])
      rw [Function.update_of_ne this]
    · rfl

theorem runs_lift {c : Cmd 0 11} {τ : Fin 15 → WTape} {σ' : Fin 11 → WTape} {B : ℕ}
    (h : Runs c (τ ∘ κ) (· = σ') B) : Runs (c.map κ κ_injective) τ (· = ext τ σ') B := by
  refine (h.map κ κ_injective τ rfl).mono (fun τ' ⟨hq, ho⟩ => ?_) le_rfl
  funext x
  unfold ext
  split_ifs with hx
  · rw [← hq]; rfl
  · exact ho x (fun y e => hx (by rw [← e]; exact y.isLt))

/-- The record's words. -/
abbrev xX : Fin 15 := 0
/-- The output words. -/
abbrev xO : Fin 15 := 1
/-- Unary register: words per record. -/
abbrev xC : Fin 15 := 3
/-- The monomial's head-count register. -/
abbrev xH : Fin 15 := 4
/-- The monomial's tail-count register. -/
abbrev xT : Fin 15 := 5
/-- The monomial's tail flag. -/
abbrev xG : Fin 15 := 6
/-- The monomial's head flag. -/
abbrev xF : Fin 15 := 7
/-- Descriptor list: head counts. -/
abbrev dH : Fin 15 := 11
/-- Descriptor list: tail counts. -/
abbrev dT : Fin 15 := 12
/-- Descriptor list: head flags. -/
abbrev dF : Fin 15 := 13
/-- Descriptor list: tail flags. -/
abbrev dG : Fin 15 := 14

theorem κ0 : κ wX = 0 := rfl
theorem κ1 : κ wO = 1 := rfl
theorem κ2 : κ wA = 2 := rfl
theorem κ3 : κ wC = 3 := rfl
theorem κ4 : κ wH = 4 := rfl
theorem κ5 : κ wT = 5 := rfl
theorem κ6 : κ fT = 6 := rfl
theorem κ7 : κ fH = 7 := rfl
theorem κ8 : κ wQ = 8 := rfl
theorem κ9 : κ wJ = 9 := rfl
theorem κ10 : κ wW = 10 := rfl

/-- Copy the current descriptor word into an empty register and rewind it. -/
noncomputable def load (s d : Fin 15) (h : s ≠ d) : Cmd 0 15 := .seq (cpy s d h) (rewind d)

theorem runs_load {s d : Fin 15} (h : s ≠ d) (σ : Fin 15 → WTape) {L R : List (List Bool)} {x : List Bool}
    (hs : σ s = ⟨L, x :: R⟩) (hd : σ d = emp) :
    Runs (load s d h) σ (· = Function.update (Function.update σ s ⟨x :: L, R⟩) d (reg x))
      (2 * x.length + 10) := by
  have s1 := runs_cpy (a := 0) h σ (by simp [hs]) (by simp [hd, emp])
  have e1 : Function.update (Function.update σ s (σ s).next) d ((σ d).put false [(σ s).cur]) =
      Function.update (Function.update σ s ⟨x :: L, R⟩) d ⟨[x], []⟩ := by
    rw [hs, hd]; rfl
  rw [e1] at s1
  have s2 := runs_rewind (a := 0) d (Function.update (Function.update σ s ⟨x :: L, R⟩) d ⟨[x], []⟩)
  refine (Runs.then s1 s2).mono (fun τ e => ?_) ?_
  · rw [e]; simp [reg]
  · simp [hs]; omega

/-- The per-record descriptor words. -/
def hdW (r E : ℕ) : List Bool := ones (2 * (r - E % r))
def tlW (r E : ℕ) : List Bool := ones (2 * (E % r))
def hfW (r E : ℕ) : List Bool := [decide (E / r % 2 = 1)]
def tfW (r E : ℕ) : List Bool := [!decide (E / r % 2 = 1)]

/-- One record: load its descriptors, run the monomial, clear the registers. -/
noncomputable def body : Cmd 0 15 :=
  .seq (load dH xH (by decide)) <| .seq (load dT xT (by decide)) <| .seq (load dF xF (by decide)) <|
  .seq (load dG xG (by decide)) <| .seq (twistCmd.map κ κ_injective) <|
  .seq (clear xH) <| .seq (clear xT) <| .seq (clear xF) (clear xG)

/-- The work tapes of the monomial are empty and the word count is loaded. -/
def Idle (r : ℕ) (τ : Fin 15 → WTape) : Prop :=
  τ xC = reg (ones (2 * r)) ∧ τ 2 = emp ∧ τ xH = emp ∧ τ xT = emp ∧ τ xG = emp ∧ τ xF = emp ∧
    τ 8 = emp ∧ τ 9 = emp ∧ τ 10 = emp

set_option maxHeartbeats 8000000 in
theorem runs_body {r : ℕ} [NeZero r] (w E : ℕ) (f : Rec r) (τ : Fin 15 → WTape) (hI : Idle r τ)
    {Lx R Lh Hs Lt Ts Lf Fs Lg Gs D : List (List Bool)}
    (hX : τ xX = ⟨Lx, recordWords w f.1 f.2 ++ R⟩) (hO : τ xO = ⟨D, []⟩)
    (hH : τ dH = ⟨Lh, hdW r E :: Hs⟩) (hT : τ dT = ⟨Lt, tlW r E :: Ts⟩)
    (hF : τ dF = ⟨Lf, hfW r E :: Fs⟩) (hG : τ dG = ⟨Lg, tfW r E :: Gs⟩) :
    Runs body τ (· = Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ xX ⟨(recordWords w f.1 f.2).reverse ++ Lx, R⟩)
      xO ⟨(recordWords w (twistRec E f).1 (twistRec E f).2).reverse ++ D, []⟩)
      dH ⟨hdW r E :: Lh, Hs⟩) dT ⟨tlW r E :: Lt, Ts⟩) dF ⟨hfW r E :: Lf, Fs⟩) dG ⟨tfW r E :: Lg, Gs⟩)
      (2 * r * (25 * w + 200) + 50 * r + 400) := by
  obtain ⟨hC, hA, hxH, hxT, hxG, hxF, hQ, hJ, hW⟩ := hI
  have hs : E % r < r := Nat.mod_lt _ (NeZero.pos r)
  have s1 := runs_load (show dH ≠ xH by decide) τ hH hxH
  set τ₁ := Function.update (Function.update τ dH ⟨hdW r E :: Lh, Hs⟩) xH (reg (hdW r E))
  have s2 := runs_load (show dT ≠ xT by decide) τ₁ (L := Lt) (R := Ts) (x := tlW r E) (by tsimp [τ₁, hT]) (by tsimp [τ₁, hxT])
  set τ₂ := Function.update (Function.update τ₁ dT ⟨tlW r E :: Lt, Ts⟩) xT (reg (tlW r E))
  have s3 := runs_load (show dF ≠ xF by decide) τ₂ (L := Lf) (R := Fs) (x := hfW r E) (by tsimp [τ₂, τ₁, hF]) (by tsimp [τ₂, τ₁, hxF])
  set τ₃ := Function.update (Function.update τ₂ dF ⟨hfW r E :: Lf, Fs⟩) xF (reg (hfW r E))
  have s4 := runs_load (show dG ≠ xG by decide) τ₃ (L := Lg) (R := Gs) (x := tfW r E) (by tsimp [τ₃, τ₂, τ₁, hG]) (by tsimp [τ₃, τ₂, τ₁, hxG])
  set τ₄ := Function.update (Function.update τ₃ dG ⟨tfW r E :: Lg, Gs⟩) xG (reg (tfW r E))
  have t5 := runs_twist_record w E f D Lx R (τ₄ ∘ κ)
    (by show τ₄ (κ _) = _; rw [κ0]; tsimp [τ₄, τ₃, τ₂, τ₁, hX])
    (by show τ₄ (κ _) = _; rw [κ1]; tsimp [τ₄, τ₃, τ₂, τ₁, hO])
    (by show τ₄ (κ _) = _; rw [κ2]; tsimp [τ₄, τ₃, τ₂, τ₁, hA])
    (by show τ₄ (κ _) = _; rw [κ3]; tsimp [τ₄, τ₃, τ₂, τ₁, hC])
    (by show τ₄ (κ _) = _; rw [κ4]; tsimp [τ₄, τ₃, τ₂, τ₁, hdW])
    (by show τ₄ (κ _) = _; rw [κ5]; tsimp [τ₄, τ₃, τ₂, τ₁, tlW])
    (by show τ₄ (κ _) = _; rw [κ6]; tsimp [τ₄, τ₃, τ₂, τ₁, tfW])
    (by show τ₄ (κ _) = _; rw [κ7]; tsimp [τ₄, τ₃, τ₂, τ₁, hfW])
    (by show τ₄ (κ _) = _; rw [κ8]; tsimp [τ₄, τ₃, τ₂, τ₁, hQ])
    (by show τ₄ (κ _) = _; rw [κ9]; tsimp [τ₄, τ₃, τ₂, τ₁, hJ])
    (by show τ₄ (κ _) = _; rw [κ10]; tsimp [τ₄, τ₃, τ₂, τ₁, hW])
  have s5 := runs_lift t5
  rw [ext_update, ext_update, ext_self, κ0, κ1] at s5
  set τ₅ := Function.update (Function.update τ₄ xX ⟨(recordWords w f.1 f.2).reverse ++ Lx, R⟩)
    xO ⟨(recordWords w (twistRec E f).1 (twistRec E f).2).reverse ++ D, []⟩
  have s6 := runs_clear (a := 0) xH τ₅
  have s7 := runs_clear (a := 0) xT (Function.update τ₅ xH ⟨[], []⟩)
  have s8 := runs_clear (a := 0) xF (Function.update (Function.update τ₅ xH ⟨[], []⟩) xT ⟨[], []⟩)
  have s9 := runs_clear (a := 0) xG
    (Function.update (Function.update (Function.update τ₅ xH ⟨[], []⟩) xT ⟨[], []⟩) xF ⟨[], []⟩)
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5
    (Runs.then s6 (Runs.then s7 (Runs.then s8 s9)))))))).mono (fun τ' h => ?_) ?_
  · clear s1 s2 s3 s4 s5 s6 s7 s8 s9 t5
    rw [h]; funext y
    by_cases hm : y ∈ [xX, xO, dH, dT, dF, dG, xH, xT, xF, xG]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [τ₅, τ₄, τ₃, τ₂, τ₁] <;> tsimp [emp, hxH, hxT, hxF, hxG]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hm
      simp only [τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10,
        ite_false]
  · clear s1 s2 s3 s4 s5 s6 s7 s8 s9 t5
    simp only [τ₅, τ₄, τ₃, τ₂, τ₁]
    tsimp [reg, WTape.words, hdW, tlW, hfW, tfW, length_ones]
    omega

/-- The monomial on every record, one per head-count descriptor. -/
noncomputable def twistArray : Cmd 0 15 := .loop dH body

/-- The component words of a list of records. -/
def arrWords {r : ℕ} (w : ℕ) (fs : List (Rec r)) : List (List Bool) := fs.flatMap fun f => recordWords w f.1 f.2

theorem runs_twistArray {r : ℕ} [NeZero r] (w : ℕ) :
    ∀ (ps : List (ℕ × Rec r)) (τ : Fin 15 → WTape) (Lx R Lh Lt Lf Lg D : List (List Bool)),
      Idle r τ → τ xX = ⟨Lx, arrWords w (ps.map Prod.snd) ++ R⟩ → τ xO = ⟨D, []⟩ →
      τ dH = ⟨Lh, ps.map fun p => hdW r p.1⟩ → τ dT = ⟨Lt, ps.map fun p => tlW r p.1⟩ →
      τ dF = ⟨Lf, ps.map fun p => hfW r p.1⟩ → τ dG = ⟨Lg, ps.map fun p => tfW r p.1⟩ →
      Runs twistArray τ (· = Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update τ
          xX ⟨(arrWords w (ps.map Prod.snd)).reverse ++ Lx, R⟩)
          xO ⟨(arrWords w (ps.map fun p => twistRec p.1 p.2)).reverse ++ D, []⟩)
          dH ⟨(ps.map fun p => hdW r p.1).reverse ++ Lh, []⟩) dT ⟨(ps.map fun p => tlW r p.1).reverse ++ Lt, []⟩)
          dF ⟨(ps.map fun p => hfW r p.1).reverse ++ Lf, []⟩) dG ⟨(ps.map fun p => tfW r p.1).reverse ++ Lg, []⟩)
        (ps.length * (2 * r * (25 * w + 200) + 50 * r + 402))
  | [], τ, Lx, R, Lh, Lt, Lf, Lg, D, _, hX, hO, hH, hT, hF, hG => by
    refine (Runs.loop_done (by simp [hH]) rfl).mono (fun τ' e => ?_) (by simp)
    rw [← e]; funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hX, hO, hH, hT, hF, hG, arrWords])
  | (E, f) :: ps, τ, Lx, R, Lh, Lt, Lf, Lg, D, hI, hX, hO, hH, hT, hF, hG => by
    have s1 := runs_body w E f τ hI (Lx := Lx) (Lh := Lh) (Lt := Lt) (Lf := Lf) (Lg := Lg) (D := D)
      (R := arrWords w (ps.map Prod.snd) ++ R) (Hs := ps.map fun p => hdW r p.1)
      (Ts := ps.map fun p => tlW r p.1) (Fs := ps.map fun p => hfW r p.1) (Gs := ps.map fun p => tfW r p.1)
      (by rw [hX]; simp [arrWords]) hO (by rw [hH]; rfl) (by rw [hT]; rfl) (by rw [hF]; rfl) (by rw [hG]; rfl)
    set τ₁ := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update τ xX ⟨(recordWords w f.1 f.2).reverse ++ Lx, arrWords w (ps.map Prod.snd) ++ R⟩)
      xO ⟨(recordWords w (twistRec E f).1 (twistRec E f).2).reverse ++ D, []⟩)
      dH ⟨hdW r E :: Lh, ps.map fun p => hdW r p.1⟩) dT ⟨tlW r E :: Lt, ps.map fun p => tlW r p.1⟩)
      dF ⟨hfW r E :: Lf, ps.map fun p => hfW r p.1⟩) dG ⟨tfW r E :: Lg, ps.map fun p => tfW r p.1⟩
    obtain ⟨hC, hA, hxH, hxT, hxG, hxF, hQ, hJ, hW⟩ := hI
    have ih := runs_twistArray w ps τ₁ ((recordWords w f.1 f.2).reverse ++ Lx) R (hdW r E :: Lh)
      (tlW r E :: Lt) (hfW r E :: Lf) (tfW r E :: Lg)
      ((recordWords w (twistRec E f).1 (twistRec E f).2).reverse ++ D)
      ⟨by tsimp [τ₁, hC], by tsimp [τ₁, hA], by tsimp [τ₁, hxH], by tsimp [τ₁, hxT], by tsimp [τ₁, hxG],
        by tsimp [τ₁, hxF], by tsimp [τ₁, hQ], by tsimp [τ₁, hJ], by tsimp [τ₁, hW]⟩
      (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁]) (by tsimp [τ₁])
    refine (Runs.loop_step (by simp [hH]) (s1.mono (fun τ' e => by rw [e]; exact ih) le_rfl)).mono
      (fun τ' e => ?_) ?_
    · rw [e]; funext y
      simp only [τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [arrWords])
    · simp only [List.length_cons]; nlinarith

end TwistArray

end IntegerMultBounds.Schoenhage
