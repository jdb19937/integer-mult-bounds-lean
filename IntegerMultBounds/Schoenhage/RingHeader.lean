module

public import IntegerMultBounds.Schoenhage.RingConst
public import IntegerMultBounds.Spec.PointwiseProducts

/-! Decoding the `Γ` header on tapes. A streaming rule counts the leading
zeros of a code in unary; the code's binary digits, most significant first,
are then cut off with `take` and `drop`, and turned into unary by doubling an
accumulator and adding each bit (`runs_binLoop`, value `binaryValue`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-! ### Leading zeros -/

namespace Rules

/-- One `true` per leading zero of the driver. -/
abbrev lead : Rule 0 where
  Q := Bool
  q0 := false
  step q b _ := if q || b then (true, none, fun _ => false) else (false, some (some true), fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

theorem go_lead_done (w : List Bool) (ws : Fin 0 → List Bool) : (go lead true w ws).2.1 = [] := by
  induction w generalizing ws with
  | nil => simp [go]
  | cons b w ih => simp [go, ih]

theorem go_lead (w : List Bool) (ws : Fin 0 → List Bool) :
    (go lead false w ws).2.1 = (ones (w.takeWhile (· = false)).length).map some := by
  induction w generalizing ws with
  | nil => simp [go, ones]
  | cons b w ih =>
    cases b
    · simp only [go, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Option.toList_some, List.singleton_append]
      rw [ih]; simp [ones, List.replicate_succ]
    · simp only [go, Bool.or_true, ↓reduceIte, Option.toList_none, List.nil_append]
      rw [go_lead_done]; simp [ones]

theorem output_lead (w : List Bool) (ws : Fin 0 → List Bool) :
    output lead w ws = syms [ones (w.takeWhile (· = false)).length] := by
  simp [output, go_lead, syms_cons]

end Rules

/-! ### Binary to unary -/

theorem binaryValue_append_one (bs : List Bool) (b : Bool) :
    binaryValue (bs ++ [b]) = 2 * binaryValue bs + (if b then 1 else 0) := by
  induction bs with
  | nil => cases b <;> simp [binaryValue]
  | cons c bs ih =>
    simp only [List.cons_append, binaryValue, List.length_append, List.length_singleton, ih, pow_succ]
    ring

/-- Take the first bit into `tE`, drop it from `tO2`, double `tL` into `tH` (head left at the end). -/
noncomputable def binA : Cmd 0 𝕌 :=
  .seq (op1 Rules.take false (ι c1) (ι tO2) (ι tE) (by decide) (by decide) (by decide)) <|
  .seq (rewind (ι c1)) <| .seq (rewind (ι tO2)) <| .seq (rewind (ι tE)) <|
  .seq (op1 Rules.drop false (ι tO2) (ι c1) (ι tE2) (by decide) (by decide) (by decide)) <|
  .seq (rewind (ι tO2)) <| .seq (rewind (ι c1)) <| .seq (rewind (ι tE2)) <| .seq (clear (ι tO2)) <|
  .seq (regMove (ι tE2) (ι tO2) (by decide)) <|
  .seq (op0 Rules.copy false (ι tL) (ι tH) (by decide)) <| .seq (rewind (ι tL)) <|
  .seq (op0 Rules.copy true (ι tL) (ι tH) (by decide)) (clear (ι tL))

set_option maxHeartbeats 4000000 in
theorem runs_binA (τ : Fin 𝕌 → WTape) {b : Bool} {B : List Bool} {u : ℕ} (h1 : τ (ι c1) = reg [true])
    (hB : τ (ι tO2) = reg (b :: B)) (hL : τ (ι tL) = reg (ones u)) (hE : τ (ι tE) = emp) (hE2 : τ (ι tE2) = emp)
    (hH : τ (ι tH) = emp) :
    Runs binA τ (· = Function.update (Function.update (Function.update (Function.update τ
      (ι tE) (reg [b])) (ι tO2) (reg B)) (ι tL) emp) (ι tH) ⟨[ones (u + u)], []⟩)
      (12 * B.length + 8 * u + 120) := by
  apply Runs.of_wp
  simp only [binA, regMove, regIn, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [h1, hB, hL, hE, hE2, hH, emp, reg, Rules.output_take, Rules.output_drop, Rules.output_copy, Rules.fit,
    ones_append]
  have t1 := time_le Rules.take [true] (fun _ => b :: B) (B.length + 1) (fun _ => by simp)
  have t2 := time_le Rules.drop (b :: B) (fun _ => [true]) 1 (fun _ => by simp)
  have bt : Rules.take.B = 1 := rfl
  have bd : Rules.drop.B = 1 := rfl
  rw [bt] at t1; rw [bd] at t2
  generalize time Rules.take [true] (fun _ => b :: B) = T1 at t1 ⊢
  generalize time Rules.drop (b :: B) (fun _ => [true]) = T2 at t2 ⊢
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [h1, hB, hL, hE, hE2, hH, emp, reg, ones_append] at *
  · simp only [time_copy, length_ones, WTape.words, clen_cons, clen_nil, List.reverse_nil, List.nil_append,
      List.length_cons, List.length_nil, List.length_singleton, List.length_drop, List.reverse_cons,
      List.singleton_append, List.append_nil] at *
    omega

theorem ones_snoc (v : ℕ) : ones v ++ [true] = ones (v + 1) := by
  simp [ones, List.replicate_succ']

/-- Add the bit. -/
noncomputable def binC : Cmd 0 𝕌 :=
  .cond (ι tE) (.seq (op0 Rules.copy true (ι c1) (ι tH) (by decide)) (rewind (ι c1))) (rewind (ι tJ))

theorem runs_binC (τ : Fin 𝕌 → WTape) {b : Bool} {v : ℕ} (h1 : τ (ι c1) = reg [true]) (hE : τ (ι tE) = reg [b])
    (hH : τ (ι tH) = ⟨[ones v], []⟩) (hJ : τ (ι tJ) = emp) :
    Runs binC τ (· = Function.update τ (ι tH) ⟨[ones (v + if b then 1 else 0)], []⟩) 20 := by
  unfold binC
  cases b
  · refine Runs.le (Runs.cond_false (B := 19) (by rw [hE, reg, startsOne_mk]; simp) ?_) (by omega)
    refine (runs_rewind (a := 0) (ι tJ) τ).mono (fun τ' h => ?_) (by rw [hJ]; simp)
    rw [h]; funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hJ, hH, emp] at *
  · refine Runs.le (Runs.cond_true (B := 19) (by rw [hE, reg, startsOne_mk]) ?_) (by omega)
    apply Runs.of_wp
    simp only [WP, wp_op0, wp_rewind]
    tsimp [h1, hH, emp, reg, Rules.output_copy, ones_append]
    funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [h1, hH, emp, reg, ones_append, ones_snoc] at *

/-- Install the new accumulator, drop the bit and one tick. -/
noncomputable def binD : Cmd 0 𝕌 :=
  .seq (rewind (ι tH)) <| .seq (regMove (ι tH) (ι tL) (by decide)) <| .seq (clear (ι tE)) (skp (ι qT) (ι tJ) (by decide))

theorem runs_binD (τ : Fin 𝕌 → WTape) {v : ℕ} {b : Bool} {Tl : List (List Bool)} {n : ℕ}
    (hH : τ (ι tH) = ⟨[ones v], []⟩) (hL : τ (ι tL) = emp) (hE : τ (ι tE) = reg [b])
    (hT : τ (ι qT) = ⟨Tl, List.replicate (n + 1) []⟩) (hJ : τ (ι tJ) = emp) :
    Runs binD τ (· = Function.update (Function.update (Function.update (Function.update τ
      (ι tH) emp) (ι tL) (reg (ones v))) (ι tE) emp) (ι qT) ⟨[] :: Tl, List.replicate n []⟩) (6 * v + 50) := by
  apply Runs.of_wp
  simp only [binD, regMove, regIn, cpy, skp, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hH, hL, hE, hT, hJ, emp, reg, Rules.output_copy, Rules.output_skip, List.replicate_succ]
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hH, hL, hE, hT, hJ, emp, reg, List.replicate_succ] at *
  · simp [time_copy, time_skip, clen, WTape.words]; omega

/-- One bit. -/
noncomputable def binStep : Cmd 0 𝕌 := .seq binA <| .seq binC binD

/-- Every bit of `tO2` into the unary accumulator `tL`. -/
noncomputable def binLoop : Cmd 0 𝕌 := .loop (ι qT) binStep

theorem binFinal_step (u : ℕ) (b : Bool) (B : List Bool) :
    (u + u + (if b then 1 else 0)) * 2 ^ B.length + binaryValue B = u * 2 ^ (b :: B).length + binaryValue (b :: B) := by
  simp only [binaryValue, List.length_cons, pow_succ]; cases b <;> simp <;> ring

theorem runs_binLoop : ∀ (B : List Bool) (u F : ℕ) (τ : Fin 𝕌 → WTape) (Tl : List (List Bool)),
    u * 2 ^ B.length + binaryValue B = F →
    τ (ι c1) = reg [true] → τ (ι tO2) = reg B → τ (ι tL) = reg (ones u) → τ (ι tE) = emp → τ (ι tE2) = emp →
    τ (ι tH) = emp → τ (ι qT) = ⟨Tl, List.replicate B.length []⟩ → τ (ι tJ) = emp →
    Runs binLoop τ (· = Function.update (Function.update (Function.update τ (ι tO2) (reg []))
      (ι tL) (reg (ones F))) (ι qT) ⟨List.replicate B.length [] ++ Tl, []⟩) (B.length * (12 * B.length + 20 * F + 200))
  | [], u, F, τ, Tl, hF, _, hB, hL, _, _, _, hT, _ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ' h => ?_) (by simp)
    subst hF
    rw [← h]; funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hB, hL, hT, binaryValue] at *
  | b :: B, u, F, τ, Tl, hF, h1, hB, hL, hE, hE2, hH, hT, hJ => by
    have s1 := runs_binA τ h1 hB hL hE hE2 hH
    set τ₁ := Function.update (Function.update (Function.update (Function.update τ
      (ι tE) (reg [b])) (ι tO2) (reg B)) (ι tL) emp) (ι tH) ⟨[ones (u + u)], []⟩
    have s2 := runs_binC τ₁ (b := b) (v := u + u) (by tsimp [τ₁, h1]) (by tsimp [τ₁]) (by tsimp [τ₁])
      (by tsimp [τ₁, hJ])
    set v := u + u + if b then 1 else 0
    set τ₂ := Function.update τ₁ (ι tH) ⟨[ones v], []⟩
    have s3 := runs_binD τ₂ (v := v) (b := b) (Tl := Tl) (n := B.length) (by tsimp [τ₂]) (by tsimp [τ₂, τ₁])
      (by tsimp [τ₂, τ₁]) (by tsimp [τ₂, τ₁, hT]) (by tsimp [τ₂, τ₁, hJ])
    set τ₃ := Function.update (Function.update (Function.update (Function.update τ₂
      (ι tH) emp) (ι tL) (reg (ones v))) (ι tE) emp) (ι qT) ⟨[] :: Tl, List.replicate B.length []⟩
    have hF' : v * 2 ^ B.length + binaryValue B = F := by rw [binFinal_step]; exact hF
    have ih := runs_binLoop B v F τ₃ ([] :: Tl) hF' (by tsimp [τ₃, τ₂, τ₁, h1]) (by tsimp [τ₃, τ₂, τ₁])
      (by tsimp [τ₃, τ₂, τ₁]) (by tsimp [τ₃, τ₂, τ₁]) (by tsimp [τ₃, τ₂, τ₁, hE2]) (by tsimp [τ₃, τ₂, τ₁])
      (by tsimp [τ₃]) (by tsimp [τ₃, τ₂, τ₁, hJ])
    refine (Runs.loop_step (by simp [hT]) ((Runs.then s1 (Runs.then s2 s3)).mono
      (fun τ' h => by rw [h]; exact ih) le_rfl)).mono (fun τ' h => ?_) ?_
    · rw [h]; funext x
      simp only [τ₃, τ₂, τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [hE, hE2, hH, emp, replicate_nil_append, List.replicate_succ] at *
    · have hu : u * 2 ^ (b :: B).length ≤ F := by rw [← hF]; omega
      have hu' : u ≤ F := le_trans (Nat.le_mul_of_pos_right u (Nat.two_pow_pos _)) hu
      have hv : v ≤ F := by
        rw [← hF']; exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right v (Nat.two_pow_pos _))
      simp only [List.length_cons]
      nlinarith

/-! ### One code -/

theorem fit_append (a b : List Bool) : Rules.fit a.length (a ++ b) = a := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [Rules.fit, ih]

/-- The pieces of a code followed by more bits. -/
theorem gamma_split {v : ℕ} (hv : 1 ≤ v) (rest : List Bool) :
    ((gamma v ++ rest).takeWhile (· = false)).length = Nat.size v - 1 ∧
      (gamma v ++ rest).drop (Nat.size v - 1) = msbBits (Nat.size v) v ++ rest := by
  have hm := msbBits_size hv
  have e : gamma v ++ rest = List.replicate (Nat.size v - 1) false ++ true :: (msbBits (Nat.size v - 1) v ++ rest) := by
    rw [gamma, hm]; simp
  refine ⟨?_, ?_⟩
  · rw [e, takeWhile_replicate_false]; simp
  · rw [e, List.drop_left' (by simp), hm]; rfl

/-- Leading zeros to `tY`, their count plus one to `sX`, the code's digits to `tO2`, the rest to `tX`. -/
noncomputable def codeA : Cmd 0 𝕌 :=
  .seq (op0 Rules.lead false (ι tX) (ι tY) (by decide)) <| .seq (rewind (ι tX)) <| .seq (rewind (ι tY)) <|
  .seq (op0 Rules.copy false (ι tY) (ι sX) (by decide)) <| .seq (rewind (ι tY)) <|
  .seq (op0 Rules.copy true (ι c1) (ι sX) (by decide)) <| .seq (rewind (ι c1)) <| .seq (rewind (ι sX)) <|
  .seq (op1 Rules.drop false (ι tX) (ι tY) (ι tD) (by decide) (by decide) (by decide)) <|
  .seq (rewind (ι tX)) <| .seq (rewind (ι tY)) <| .seq (rewind (ι tD)) <| .seq (clear (ι tX)) <| .seq (clear (ι tY)) <|
  .seq (op1 Rules.take false (ι sX) (ι tD) (ι tO2) (by decide) (by decide) (by decide)) <|
  .seq (rewind (ι sX)) <| .seq (rewind (ι tD)) <| .seq (rewind (ι tO2)) <|
  .seq (op1 Rules.drop false (ι tD) (ι sX) (ι tX) (by decide) (by decide) (by decide)) <|
  .seq (rewind (ι tD)) <| .seq (rewind (ι sX)) <| .seq (rewind (ι tX)) (clear (ι tD))

set_option maxHeartbeats 8000000 in
theorem runs_codeA {v : ℕ} (hv : 1 ≤ v) {rest : List Bool} (τ : Fin 𝕌 → WTape) (h1 : τ (ι c1) = reg [true])
    (hX : τ (ι tX) = reg (gamma v ++ rest)) (hY : τ (ι tY) = emp) (hS : τ (ι sX) = emp) (hD : τ (ι tD) = emp)
    (hO : τ (ι tO2) = emp) :
    Runs codeA τ (· = Function.update (Function.update (Function.update τ (ι tX) (reg rest))
      (ι sX) (reg (ones (Nat.size v)))) (ι tO2) (reg (msbBits (Nat.size v) v)))
      (40 * (gamma v ++ rest).length + 300) := by
  obtain ⟨hz, hd⟩ := gamma_split hv rest
  set x := gamma v ++ rest
  set n := Nat.size v
  have hn : 1 ≤ n := Nat.size_pos.mpr hv
  have e1 : ones (n - 1) ++ [true] = ones n := by rw [ones_snoc]; congr 1; omega
  have e2 : Rules.fit n (msbBits n v ++ rest) = msbBits n v := by
    have := fit_append (msbBits n v) rest; rwa [length_msbBits] at this
  have e3 : (msbBits n v ++ rest).drop n = rest := by
    have := List.drop_left (l₁ := msbBits n v) (l₂ := rest); rwa [length_msbBits] at this
  have hz' : (x.takeWhile (fun b => !b)).length = n - 1 := by simpa using hz
  have e4 : x.drop (n - 1 + (n - 1 + 1)) = rest := by
    rw [← List.drop_drop, hd, show n - 1 + 1 = n by omega, e3]
  have hxl : n - 1 ≤ x.length := by
    have := congrArg List.length hd; simp at this; omega
  apply Runs.of_wp
  simp only [codeA, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [h1, hX, hY, hS, hD, hO, emp, reg, Rules.output_lead, Rules.output_copy, Rules.output_drop,
    Rules.output_take, hz', hd, e1, e2, e3, e4, length_ones]
  have t1 := time_le Rules.lead x (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.drop x (fun _ => ones (n - 1)) (n - 1) (fun _ => by simp)
  have t3 := time_le Rules.take (ones n) (fun _ => msbBits n v ++ rest) x.length (fun _ => by
    rw [← hd]; simp)
  have t4 := time_le Rules.drop (msbBits n v ++ rest) (fun _ => ones n) n (fun _ => by simp)
  have b1 : Rules.lead.B = 1 := rfl
  have b2 : Rules.drop.B = 1 := rfl
  have b3 : Rules.take.B = 1 := rfl
  rw [b1] at t1; rw [b2] at t2 t4; rw [b3] at t3
  generalize time Rules.lead x (fun j => j.elim0) = T1 at t1 ⊢
  generalize time Rules.drop x (fun _ => ones (n - 1)) = T2 at t2 ⊢
  generalize time Rules.take (ones n) (fun _ => msbBits n v ++ rest) = T3 at t3 ⊢
  generalize time Rules.drop (msbBits n v ++ rest) (fun _ => ones n) = T4 at t4 ⊢
  have hl : (msbBits n v ++ rest).length ≤ x.length := by rw [← hd]; simp
  refine ⟨?_, ?_⟩
  · clear t1 t2 t3 t4 hl hxl e1 e2 e3 e4 hz hz' hd
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [h1, hX, hY, hS, hD, hO, emp, reg] at *
  · simp only [time_copy, length_ones, WTape.words, clen_cons, clen_nil, List.reverse_nil, List.nil_append,
      List.length_cons, List.length_nil, List.length_singleton, List.reverse_cons, List.singleton_append,
      List.append_nil, length_msbBits, List.length_append] at *
    clear_value x n
    clear hz hd e1 e2 e3 hz' e4 h1 hX hY hS hD hO b1 b2 b3
    generalize x.length = X at *
    generalize rest.length = Rl at *
    have hm : n - 1 + 1 = n := by omega
    generalize n - 1 = m at *
    linarith

/-- Decode the code at the front of `tX` into `tL = ones v`; the rest stays in `tX`. -/
noncomputable def decodeOne : Cmd 0 𝕌 :=
  .seq codeA <| .seq (ticksFrom (ι sX) (by decide)) <| .seq (clear (ι sX)) <| .seq (emit [[]] (ι tL)) <|
  .seq (rewind (ι tL)) <| .seq binLoop <| .seq (clear (ι qT)) (clear (ι tO2))

theorem binaryValue_msbBits_size (v : ℕ) : binaryValue (msbBits (Nat.size v) v) = v := by
  rw [binaryValue_msbBits, Nat.mod_eq_of_lt (Nat.lt_size_self v)]

set_option maxHeartbeats 8000000 in
theorem runs_decodeOne {v : ℕ} (hv : 1 ≤ v) {rest : List Bool} (τ : Fin 𝕌 → WTape) (h1 : τ (ι c1) = reg [true])
    (hX : τ (ι tX) = reg (gamma v ++ rest)) (hY : τ (ι tY) = emp) (hS : τ (ι sX) = emp) (hD : τ (ι tD) = emp)
    (hO : τ (ι tO2) = emp) (hT : τ (ι qT) = emp) (hL : τ (ι tL) = emp) (hE : τ (ι tE) = emp)
    (hE2 : τ (ι tE2) = emp) (hH : τ (ι tH) = emp) (hJ : τ (ι tJ) = emp) :
    Runs decodeOne τ (· = Function.update (Function.update τ (ι tX) (reg rest)) (ι tL) (reg (ones v)))
      (40 * (gamma v ++ rest).length + 40 * Nat.size v * (Nat.size v + v + 10) + 600) := by
  set n := Nat.size v
  have s1 := runs_codeA hv τ h1 hX hY hS hD hO
  set τ₁ := Function.update (Function.update (Function.update τ (ι tX) (reg rest))
      (ι sX) (reg (ones n))) (ι tO2) (reg (msbBits n v))
  have s2 := runs_ticksFrom (show ι sX ≠ ι qT by decide) τ₁ (b := n) (by tsimp [τ₁]) (by tsimp [τ₁, hT])
  set τ₂ := Function.update τ₁ (ι qT) ⟨[], List.replicate n []⟩
  have s3 := runs_clear (a := 0) (ι sX) τ₂
  set τ₃ := Function.update τ₂ (ι sX) ⟨[], []⟩
  have s4 := runs_emit (a := 0) [[]] (ι tL) τ₃ (by tsimp [τ₃, τ₂, τ₁, hL, emp])
  set τ₄ := Function.update τ₃ (ι tL) ⟨[[]].reverse ++ (τ₃ (ι tL)).left, []⟩
  have s5 := runs_rewind (a := 0) (ι tL) τ₄
  set τ₅ := Function.update τ₄ (ι tL) ⟨[], (τ₄ (ι tL)).left.reverse ++ (τ₄ (ι tL)).right⟩
  have s6 := runs_binLoop (msbBits n v) 0 v τ₅ [] (by simp [n, binaryValue_msbBits_size])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, h1]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hL, emp, reg, ones]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hE])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hE2]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hH])
    (by tsimp [τ₅, τ₄, τ₃, τ₂]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hJ])
  set τ₆ := Function.update (Function.update (Function.update τ₅ (ι tO2) (reg [])) (ι tL) (reg (ones v)))
    (ι qT) ⟨List.replicate (msbBits n v).length [] ++ [], []⟩
  have s7 := runs_clear (a := 0) (ι qT) τ₆
  have s8 := runs_clear (a := 0) (ι tO2) (Function.update τ₆ (ι qT) ⟨[], []⟩)
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 s8))))))).mono (fun τ' h => ?_) ?_
  · clear s1 s2 s3 s4 s5 s6 s7 s8
    rw [h]; funext y
    simp only [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hS, hT, hO, emp] at *
  · clear s1 s2 s3 s4 s5 s6 s7 s8
    tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hL, emp, reg, WTape.words, clen_cons, clen_nil, length_ones,
      clen_replicate_nil]
    have hvn : v < 2 ^ n := Nat.lt_size_self v
    generalize (gamma v ++ rest).length = X at *
    nlinarith

/-- Step past the code at the front of `tX` without reading its value. -/
noncomputable def skipOne : Cmd 0 𝕌 := .seq codeA <| .seq (clear (ι sX)) (clear (ι tO2))

theorem runs_skipOne {v : ℕ} (hv : 1 ≤ v) {rest : List Bool} (τ : Fin 𝕌 → WTape) (h1 : τ (ι c1) = reg [true])
    (hX : τ (ι tX) = reg (gamma v ++ rest)) (hY : τ (ι tY) = emp) (hS : τ (ι sX) = emp) (hD : τ (ι tD) = emp)
    (hO : τ (ι tO2) = emp) :
    Runs skipOne τ (· = Function.update τ (ι tX) (reg rest)) (50 * (gamma v ++ rest).length + 320) := by
  have s1 := runs_codeA hv τ h1 hX hY hS hD hO
  have s2 := runs_clear (a := 0) (ι sX) (Function.update (Function.update (Function.update τ (ι tX) (reg rest))
      (ι sX) (reg (ones (Nat.size v)))) (ι tO2) (reg (msbBits (Nat.size v) v)))
  have s3 := runs_clear (a := 0) (ι tO2) (Function.update (Function.update (Function.update (Function.update τ
    (ι tX) (reg rest)) (ι sX) (reg (ones (Nat.size v)))) (ι tO2) (reg (msbBits (Nat.size v) v))) (ι sX) ⟨[], []⟩)
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ' h => ?_) ?_
  · rw [h]; funext y
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try tsimp [hS, hO, emp]) <;> tsimp at *
  · have hlg := length_gamma hv
    have hb : (gamma v ++ rest).length = (gamma v).length + rest.length := List.length_append
    tsimp [reg, WTape.words, clen_cons, clen_nil, length_ones]
    omega

/-! ### The header -/

/-- Drop one from the bit length into `iL`. -/
noncomputable def logTail : Cmd 0 𝕌 :=
  .seq (op1 Rules.drop false (ι qB) (ι c1) iL (by decide) (by decide) (by decide)) <|
  .seq (rewind (ι qB)) <| .seq (rewind (ι c1)) <| .seq (rewind iL) (clear (ι qB))

/-- `ℓ = size r - 1` from `tL = ones r`, into `iL`. -/
noncomputable def logOf : Cmd 0 𝕌 :=
  .seq (regMove (ι tL) (ι qR) (by decide)) <| .seq (ticksFrom (ι qR) (by decide)) <|
  .seq (emit [[]] (ι qB)) <| .seq (rewind (ι qB)) <| .seq (up (.seq sizeLoop (.seq (clear qR) (clear qT)))) logTail

set_option maxHeartbeats 8000000 in
theorem runs_logOf {r : ℕ} (τ : Fin 𝕌 → WTape) (hL : τ (ι tL) = reg (ones r)) (hR : τ (ι qR) = emp)
    (hT : τ (ι qT) = emp) (hB : τ (ι qB) = emp) (h1 : τ (ι c1) = reg [true]) (hS : τ (ι qS) = emp)
    (hJ : τ (ι tJ) = emp) (hI : τ iL = emp) :
    Runs logOf τ (· = Function.update (Function.update τ (ι tL) emp) iL (reg (ones (Nat.size r - 1))))
      (200 * r + 300) := by
  have s1 := runs_regMove (a := 0) (show ι tL ≠ ι qR by decide) τ hL hR
  set τ₁ := Function.update (Function.update τ (ι tL) emp) (ι qR) (reg (ones r))
  have s2 := runs_ticksFrom (show ι qR ≠ ι qT by decide) τ₁ (b := r) (by tsimp [τ₁]) (by tsimp [τ₁, hT])
  set τ₂ := Function.update τ₁ (ι qT) ⟨[], List.replicate r []⟩
  have s3 := runs_emit (a := 0) [[]] (ι qB) τ₂ (by tsimp [τ₂, τ₁, hB, emp])
  set τ₃ := Function.update τ₂ (ι qB) ⟨[[]].reverse ++ (τ₂ (ι qB)).left, []⟩
  have s4 := runs_rewind (a := 0) (ι qB) τ₃
  set τ₄ := Function.update τ₃ (ι qB) ⟨[], (τ₃ (ι qB)).left.reverse ++ (τ₃ (ι qB)).right⟩
  have s5 := runs_upSize (n := r) τ₄ (by tsimp [τ₄, τ₃, τ₂, τ₁]) (by tsimp [τ₄, τ₃, τ₂, τ₁, hB, emp, reg])
    (by tsimp [τ₄, τ₃, τ₂]) (by tsimp [τ₄, τ₃, τ₂, τ₁, h1]) (by tsimp [τ₄, τ₃, τ₂, τ₁, hS])
    (by tsimp [τ₄, τ₃, τ₂, τ₁, hJ])
  set τ₅ := Function.update (Function.update (Function.update τ₄ (ι qR) emp) (ι qB) (reg (ones (Nat.size r))))
    (ι qT) emp
  have s6 : Runs logTail τ₅
      (· = Function.update (Function.update τ (ι tL) emp) iL (reg (ones (Nat.size r - 1)))) (6 * r + 40) := by
    have hs := size_le_self r
    have htl : (ones (Nat.size r)).tail = ones (Nat.size r - 1) := by simp [ones, List.tail_replicate]
    apply Runs.of_wp
    simp only [logTail, WP, wp_op1, wp_rewind, wp_clear]
    tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, h1, hI, emp, reg, Rules.output_drop, htl]
    have t1 := time_le Rules.drop (ones (Nat.size r)) (fun _ => [true]) 1 (fun _ => by simp)
    have bd : Rules.drop.B = 1 := rfl
    rw [bd, length_ones] at t1
    generalize time Rules.drop (ones (Nat.size r)) (fun _ => [true]) = T at t1 ⊢
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [h1, hR, hT, hB, reg, emp]) <;> tsimp at *
    · simp [WTape.words, clen]; omega
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono (fun τ' h => h) ?_
  have hs := size_le_self r
  tsimp [τ₄, τ₃, τ₂, τ₁, hB, emp, reg, WTape.words, clen_cons, clen_nil, length_ones]
  omega

/-- Load the header and the unit word. -/
noncomputable def hdrInit : Cmd 0 𝕌 :=
  .seq (emit [[true]] (ι c1)) <| .seq (rewind (ι c1)) (regDup zH (ι tX) (by decide))

/-- Decode `Γ(p)Γ(d)Γ(r)Γ(K)Γ(w)…` from `zH` into `iP = ones p`, `iL = ones (log₂ r)`, `iW = ones w`. -/
noncomputable def decodeHeader : Cmd 0 𝕌 :=
  .seq hdrInit <|
  .seq decodeOne <| .seq (regMove (ι tL) iP (by decide)) <|
  .seq skipOne <|
  .seq decodeOne <| .seq logOf <|
  .seq skipOne <|
  .seq decodeOne <| .seq (regMove (ι tL) iW (by decide)) <| .seq (clear (ι tX)) (clear (ι c1))

/-- A bound on decoding the header. -/
def headerCost (p r w H : ℕ) : ℕ :=
  5 * (50 * H + 600) + 42 * (Nat.size p * (Nat.size p + p + 10) +
    Nat.size r * (Nat.size r + r + 10) + Nat.size w * (Nat.size w + w + 10)) +
    200 * r + 10 * (p + w + H) + 2000

theorem decode_pre (τ : Fin 𝕌 → WTape) (hz : ∀ i : Fin 𝕋, τ (ι i) = emp) (i : Fin 𝕋) : τ (ι i) = emp := hz i

set_option maxHeartbeats 16000000 in
theorem runs_decodeHeader {p d l K w : ℕ} {ts : List ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : 1 ≤ w)
    (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hH : τ zH = reg (transformHeader p d (2 ^ l) K w ts))
    (hP : τ iP = emp) (hL : τ iL = emp) (hW : τ iW = emp) :
    Runs decodeHeader τ (· = Function.update (Function.update (Function.update τ iP (reg (ones p)))
      iL (reg (ones l))) iW (reg (ones w)))
      (headerCost p (2 ^ l) w (transformHeader p d (2 ^ l) K w ts).length) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  set hdr := transformHeader p d (2 ^ l) K w ts
  set tsc := ts.flatMap gamma
  set R4 := gamma w ++ tsc
  set R3 := gamma K ++ R4
  set R2 := gamma (2 ^ l) ++ R3
  set R1 := gamma d ++ R2
  have eh : hdr = gamma p ++ R1 := by simp [hdr, transformHeader, tsc, R1, R2, R3, R4]
  set H := hdr.length
  have s0 : Runs hdrInit τ (· = Function.update (Function.update τ (ι c1) (reg [true])) (ι tX) (reg hdr))
      (3 * H + 30) := by
    apply Runs.of_wp
    simp only [hdrInit, regDup, regIn, cpy, WP, wp_op0, wp_rewind, wp_emit]
    tsimp [hz, hH, emp, reg, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try tsimp [hz, hH, reg, emp]) <;> tsimp at *
    · simp [time_copy, clen, WTape.words]; omega
  set τ₀ := Function.update (Function.update τ (ι c1) (reg [true])) (ι tX) (reg hdr)
  -- p
  have s1 := runs_decodeOne hp (rest := R1) τ₀ (by tsimp [τ₀]) (by tsimp [τ₀, eh])
    (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz])
    (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz]) (by tsimp [τ₀, hz])
  set τ₁ := Function.update (Function.update τ₀ (ι tX) (reg R1)) (ι tL) (reg (ones p))
  have s2 := runs_regMove (a := 0) (show ι tL ≠ iP by decide) τ₁ (w := ones p) (by tsimp [τ₁])
    (by tsimp [τ₁, τ₀, hP])
  set τ₂ := Function.update (Function.update τ₁ (ι tL) emp) iP (reg (ones p))
  -- d
  have s3 := runs_skipOne hd (rest := R2) τ₂ (by tsimp [τ₂, τ₁, τ₀]) (by tsimp [τ₂, τ₁, R1])
    (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz]) (by tsimp [τ₂, τ₁, τ₀, hz])
  set τ₄ := Function.update τ₂ (ι tX) (reg R2)
  -- r
  have s5 := runs_decodeOne (Nat.one_le_two_pow (n := l)) (rest := R3) τ₄ (by tsimp [τ₄, τ₂, τ₁, τ₀])
    (by tsimp [τ₄, R2])
    (by tsimp [τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₄, τ₂, τ₁, τ₀, hz])
  set τ₅ := Function.update (Function.update τ₄ (ι tX) (reg R3)) (ι tL) (reg (ones (2 ^ l)))
  have s6 := runs_logOf (r := 2 ^ l) τ₅ (by tsimp [τ₅]) (by tsimp [τ₅, τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₅, τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₄, τ₂, τ₁, τ₀]) (by tsimp [τ₅, τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₅, τ₄, τ₂, τ₁, τ₀, hL])
  rw [Nat.size_pow, Nat.add_sub_cancel] at s6
  set τ₆ := Function.update (Function.update τ₅ (ι tL) emp) iL (reg (ones l))
  -- K
  have s7 := runs_skipOne hK (rest := R4) τ₆ (by tsimp [τ₆, τ₅, τ₄, τ₂, τ₁, τ₀]) (by tsimp [τ₆, τ₅, R3])
    (by tsimp [τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz])
  set τ₈ := Function.update τ₆ (ι tX) (reg R4)
  -- w
  have s9 := runs_decodeOne hw (rest := tsc) τ₈ (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀]) (by tsimp [τ₈, R4])
    (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz])
    (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz]) (by tsimp [τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz])
  set τ₉ := Function.update (Function.update τ₈ (ι tX) (reg tsc)) (ι tL) (reg (ones w))
  have s10 := runs_regMove (a := 0) (show ι tL ≠ iW by decide) τ₉ (w := ones w) (by tsimp [τ₉])
    (by tsimp [τ₉, τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hW])
  set τ₁₀ := Function.update (Function.update τ₉ (ι tL) emp) iW (reg (ones w))
  have s11 := runs_clear (a := 0) (ι tX) τ₁₀
  have s12 := runs_clear (a := 0) (ι c1) (Function.update τ₁₀ (ι tX) ⟨[], []⟩)
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s9 (Runs.then s10 (Runs.then s11 s12)))))))))).mono
    (fun τ' h => ?_) ?_
  · clear s0 s1 s2 s3 s5 s6 s7 s9 s10 s11 s12
    rw [h]; funext y
    by_cases hm : y ∈ [iP, iL, iW, ι c1, ι tX, ι tL]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [τ₁₀, τ₉, τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀] <;> tsimp [hz, emp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hm
      simp only [τ₁₀, τ₉, τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, Function.update_apply, n1, n2, n3, n4, n5, n6,
        if_false]
  · clear s0 s1 s2 s3 s5 s6 s7 s9 s10 s11 s12
    tsimp [τ₁₀, τ₉, τ₈, τ₆, τ₅, τ₄, τ₂, τ₁, τ₀, hz, emp, reg, WTape.words, clen_cons, clen_nil,
      length_ones]
    have l1 : (gamma p).length + R1.length = H := by simp [H, eh]
    have l2 : (gamma d).length + R2.length = R1.length := by simp [R1]
    have l3 : (gamma (2 ^ l)).length + R3.length = R2.length := by simp [R2]
    have l4 : (gamma K).length + R4.length = R3.length := by simp [R3]
    have l5 : (gamma w).length + tsc.length = R4.length := by simp [R4]
    have fd : d ≤ d.size * (d.size + d + 10) := by
      have := Nat.size_pos.mpr hd; nlinarith
    have fK : K ≤ K.size * (K.size + K + 10) := by
      have := Nat.size_pos.mpr hK; nlinarith
    unfold headerCost
    simp only [Nat.mul_assoc] at *
    generalize p.size * (p.size + p + 10) = A1 at *
    generalize d.size * (d.size + d + 10) = A2 at *
    generalize (2 ^ l).size * ((2 ^ l).size + 2 ^ l + 10) = A3 at *
    generalize K.size * (K.size + K + 10) = A4 at *
    generalize w.size * (w.size + w + 10) = A5 at *
    generalize 2 ^ l = R at *
    clear_value H R1 R2 R3 R4 tsc hdr
    omega

end IntegerMultBounds.Schoenhage
