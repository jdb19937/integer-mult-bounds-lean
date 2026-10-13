module

public import IntegerMultBounds.Schoenhage.LayoutSwapTape

/-! Setup machines of the §6 layout-script writer. A growing binary increment
(`incG`, the counter's `increment`) turns a unary value into its canonical binary
word `bin v` in `v` increments (`runs_binOf`); a nested loop writes the
axis-major arrangement `axisArr q D` as unary words (`runs_arrGen`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Resampling Script TwistDescriptors LayoutScriptTape

namespace LayoutGenSetup

/-! ### A growing increment -/

/-- Binary increment, least significant bit first, growing by a final one on overflow. -/
abbrev incG : Rule 0 where
  Q := Bool
  q0 := true
  step c b _ := (b && c, some (some (b ^^ c)), fun _ => false)
  flush c := if c then [some true, none] else [none]
  B := 2
  hB c := by cases c <;> simp

theorem go_incG : ∀ (c : Bool) (y : List Bool) (ws : Fin 0 → List Bool),
    (go incG c y ws).2.1 = (incW c y).map some ∧ (go incG c y ws).1 = (c && y.all id)
  | c, [], _ => by simp [go, incW]
  | c, b :: y, ws => by
    have ih := go_incG (b && c) y (fun j => j.elim0)
    simp only [go]
    have hws : (fun j : Fin 0 => if (fun _ : Fin 0 => false) j then (ws j).tail else ws j) = fun j => j.elim0 :=
      funext fun j => j.elim0
    rw [hws]
    refine ⟨by simp [incW, ih.1], ?_⟩
    rw [ih.2]; cases b <;> cases c <;> simp

theorem incW_false : ∀ y : List Bool, incW false y = y
  | [] => rfl
  | b :: y => by simp [incW, incW_false y]

theorem incW_increment : ∀ y : List Bool,
    incW true y ++ (if y.all id then [true] else []) = GrowingCounterData.increment y
  | [] => rfl
  | false :: y => by simp [incW, incW_false, GrowingCounterData.increment]
  | true :: y => by
    have := incW_increment y
    simp only [incW, Bool.and_true, Bool.true_xor, Bool.not_true, List.all_cons, id, Bool.true_and,
      List.cons_append, GrowingCounterData.increment]
    rw [this]

theorem output_incG (y : List Bool) (ws : Fin 0 → List Bool) :
    output incG y ws = syms [GrowingCounterData.increment y] := by
  obtain ⟨h1, h2⟩ := go_incG true y ws
  rw [← incW_increment]
  unfold output
  rw [h1, h2]
  cases hy : y.all id <;> simp [syms, List.map_append]

theorem advance_succ (n : ℕ) (bs : List Bool) :
    GrowingCounterData.advance (n + 1) bs = GrowingCounterData.increment (GrowingCounterData.advance n bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => rw [GrowingCounterData.advance, ih]; rfl

theorem bin_succ (n : ℕ) : bin (n + 1) = GrowingCounterData.increment (bin n) := advance_succ n []

theorem length_increment : ∀ y : List Bool, (GrowingCounterData.increment y).length ≤ y.length + 1
  | [] => by simp [GrowingCounterData.increment]
  | false :: y => by simp [GrowingCounterData.increment]
  | true :: y => by have := length_increment y; simp [GrowingCounterData.increment]; omega

theorem length_bin_le : ∀ n : ℕ, (bin n).length ≤ n
  | 0 => by simp [bin_zero]
  | n + 1 => by rw [bin_succ]; have := length_increment (bin n); have := length_bin_le n; omega

/-! ### Unary to binary -/

/-- The source `ones v`. -/
abbrev bSrc : Fin 5 := 0
/-- The result `bin v`. -/
abbrev bDst : Fin 5 := 1
/-- One tick per increment. -/
abbrev bTk : Fin 5 := 2
/-- Scratch. -/
abbrev bTmp : Fin 5 := 3
/-- The junk tape. -/
abbrev bJ : Fin 5 := 4

/-- One increment of the word on `bDst`. -/
noncomputable def incBody : Cmd 0 5 :=
  .seq (op0 incG false bDst bTmp (by decide)) <| .seq (clear bDst) <| .seq (rewind bTmp) <|
  .seq (cpy bTmp bDst (by decide)) <| .seq (clear bTmp) <| .seq (rewind bDst) (skp bTk bJ (by decide))

/-- Ticks for the increments and `bin 0` on `bDst`. -/
noncomputable def binPrep : Cmd 0 5 :=
  .seq (op0 Rules.ticks false bSrc bTk (by decide)) <| .seq (rewind bSrc) <| .seq (rewind bTk) <|
  .seq (emit [[]] bDst) (rewind bDst)

/-- `bin v` from `ones v`. -/
noncomputable def binOf : Cmd 0 5 := .seq binPrep <| .seq (.loop bTk incBody) (clear bTk)

/-- The converter's bank: the source, the result, the ticks. -/
def bbank (v : ℕ) (D T : WTape) : Fin 5 → WTape :=
  fun i => match i.val with
  | 0 => reg (ones v) | 1 => D | 2 => T | _ => emp

set_option maxHeartbeats 8000000 in
theorem runs_incBody {v j : ℕ} {L : List (List Bool)} (e : ℕ) :
    Runs incBody (bbank v (reg (bin j)) ⟨L, List.replicate (e + 1) []⟩)
      (· = bbank v (reg (bin (j + 1))) ⟨[] :: L, List.replicate e []⟩) (8 * j + 60) := by
  have t1 : time incG (bin j) (fun j => j.elim0) ≤ (bin j).length + 7 :=
    (time_le incG (bin j) (fun j => j.elim0) 0 (fun j => j.elim0)).trans (by simp)
  have hl := length_bin_le j
  have hl' := length_bin_le (j + 1)
  apply Runs.of_wp
  simp only [incBody, cpy, skp, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [bbank, reg, emp, output_incG, Rules.output_copy, Rules.output_skip, ← bin_succ, List.replicate_succ]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · simp [time_copy, time_skip, clen, WTape.words] at t1 ⊢
    omega

set_option maxHeartbeats 8000000 in
theorem runs_incLoop {v : ℕ} : ∀ (e j : ℕ) (L : List (List Bool)),
    Runs (.loop bTk incBody) (bbank v (reg (bin j)) ⟨L, List.replicate e []⟩)
      (· = bbank v (reg (bin (j + e))) ⟨List.replicate e [] ++ L, []⟩) (e * (8 * (j + e) + 62))
  | 0, j, L => by
    refine (Runs.loop_done (by simp [bbank]) rfl).mono (fun τ h => ?_) (by simp)
    rw [← h]; rfl
  | e + 1, j, L => by
    have s1 := runs_incBody (v := v) (j := j) (L := L) e
    have ih := runs_incLoop (v := v) e (j + 1) ([] :: L)
    refine (Runs.loop_step (by simp [bbank]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h, show j + 1 + e = j + (e + 1) by omega, List.replicate_succ', List.append_assoc]; rfl
    · rw [show j + 1 + e = j + (e + 1) by omega]
      nlinarith

set_option maxHeartbeats 8000000 in
theorem runs_binPrep (v : ℕ) :
    Runs binPrep (bbank v emp emp) (· = bbank v (reg (bin 0)) ⟨[], List.replicate v []⟩) (4 * v + 20) := by
  have t1 : time Rules.ticks (ones v) (fun j => j.elim0) ≤ v + 5 :=
    (time_le Rules.ticks (ones v) (fun j => j.elim0) 0 (fun j => j.elim0)).trans (by simp)
  apply Runs.of_wp
  simp only [binPrep, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [bbank, reg, emp, Rules.output_ticks, length_ones]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [bbank, reg, emp, bin_zero, List.reverse_replicate]
  · omega

set_option maxHeartbeats 8000000 in
/-- `runs_binOf`: `bin v` from `ones v`, the source restored. -/
theorem runs_binOf (v : ℕ) :
    Runs binOf (bbank v emp emp) (· = bbank v (reg (bin v)) emp) (8 * v * v + 70 * v + 40) := by
  have s1 := runs_binPrep v
  have s2 := runs_incLoop (v := v) v 0 []
  have s3 := runs_clear (a := 0) bTk (bbank v (reg (bin (0 + v))) ⟨List.replicate v [] ++ [], []⟩)
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> first | rfl | tsimp [bbank, emp]
  · simp [bbank, clen, WTape.words]; nlinarith

/-! ### The arrangement -/

theorem flatMap_range_getElem? {q : ℕ} (g : ℕ → List ℕ) (hg : ∀ a, (g a).length = q) :
    ∀ (D x : ℕ), x < q * D → ((List.range D).flatMap g)[x]? = (g (x / q))[x % q]?
  | 0, x, hx => by simp at hx
  | D + 1, x, hx => by
    have hq : 0 < q := by rcases Nat.eq_zero_or_pos q with h | h <;> simp_all
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((List.range D).flatMap g).length = q * D := by
      simp [List.length_flatMap, hg, mul_comm]
    by_cases hxD : x < q * D
    · rw [List.getElem?_append_left (by rw [hlen]; exact hxD)]
      exact flatMap_range_getElem? g hg D x hxD
    · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      have h1 : x / q = D := by
        have : q * (D + 1) = q * D + q := by ring
        apply Nat.div_eq_of_lt_le
        · rw [mul_comm]; omega
        · rw [Nat.succ_mul, mul_comm]; omega
      have h2 : x % q = x - q * D := by
        have := Nat.div_add_mod x q
        rw [h1] at this; omega
      rw [h1, h2]

/-- `axisArr_rows`: the arrangement axis by axis, chunk by chunk. -/
theorem axisArr_rows (q D : ℕ) :
    LayoutScript.axisArr q D = (List.range D).flatMap fun a => (List.range q).map fun c => c * D + a := by
  apply List.ext_getElem?
  intro x
  by_cases hx : x < q * D
  · have hq : 0 < q := by rcases Nat.eq_zero_or_pos q with h | h <;> simp_all
    rw [flatMap_range_getElem? (q := q) _ (by simp) D x hx]
    have hm : x % q < q := Nat.mod_lt _ hq
    simp [LayoutScript.axisArr, hx, hm]
  · have h1 : (LayoutScript.axisArr q D).length = q * D := by simp [LayoutScript.axisArr]
    have h2 : ((List.range D).flatMap fun a => (List.range q).map fun c => c * D + a).length = q * D := by
      simp [List.length_flatMap, mul_comm]
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- The words. -/
abbrev aOut : Fin 9 := 0
/-- One tick per axis. -/
abbrev aDt : Fin 9 := 1
/-- One tick per chunk. -/
abbrev aQt : Fin 9 := 2
/-- `ones D`. -/
abbrev aKN : Fin 9 := 3
/-- The axis `a`. -/
abbrev aA : Fin 9 := 4
/-- The block `c D + a`. -/
abbrev aV : Fin 9 := 5
/-- `ones 1`. -/
abbrev aOne : Fin 9 := 6
/-- The junk tape. -/
abbrev aJ : Fin 9 := 7

/-- Add the constant on `s` to the value on `d`. -/
noncomputable def addA (s d : Fin 9) (h : s ≠ d) : Cmd 0 9 := .seq (op0 Rules.copy true s d h) (rewind s)

set_option maxHeartbeats 4000000 in
theorem runs_addA {s d : Fin 9} (h : s ≠ d) {c v : ℕ} (σ : Fin 9 → WTape) (hs : σ s = reg (ones c))
    (hd : σ d = endv v) :
    Runs (addA s d h) σ (· = Function.update σ d (endv (v + c))) (2 * c + 10) := by
  apply Runs.of_wp
  simp only [addA, WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hd, h, ↓reduceIte, endv, reg, WTape.next_mk,
    WTape.cur_mk, List.headD_cons, List.tail_cons, Rules.output_copy, ↓parse_syms]
  refine ⟨⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [ones_append', WTape.put, reg, endv]
  · simp [time_copy]; omega

/-- One chunk: write the block, then add `D`. -/
noncomputable def innerBody : Cmd 0 9 :=
  .seq (back aV) <| .seq (cpy aV aOut (by decide)) <| .seq (addA aKN aV (by decide)) (skp aQt aJ (by decide))

/-- One axis: start the block at `a`, every chunk, then `a + 1`. -/
noncomputable def outerBody : Cmd 0 9 :=
  .seq (clear aV) <| .seq (back aA) <| .seq (cpy aA aV (by decide)) <| .seq (.loop aQt innerBody) <|
  .seq (rewind aQt) <| .seq (addA aOne aA (by decide)) (skp aDt aJ (by decide))

/-- The arrangement's words on `aOut`. -/
noncomputable def arrGen : Cmd 0 9 :=
  .seq (emit [[]] aA) <| .seq (emit [[]] aV) <| .seq (.loop aDt outerBody) <| .seq (rewind aDt) <|
  .seq (clear aA) (clear aV)

/-- The generator's bank. -/
def abank (D : ℕ) (O Dt Qt A V : WTape) : Fin 9 → WTape :=
  fun i => match i.val with
  | 0 => O | 1 => Dt | 2 => Qt | 3 => reg (ones D) | 4 => A | 5 => V | 6 => reg (ones 1)
  | _ => emp

set_option maxHeartbeats 8000000 in
theorem runs_innerBody {D : ℕ} {O : List (List Bool)} {Dt A : WTape} {LQ : List (List Bool)} {e v : ℕ} :
    Runs innerBody (abank D ⟨O, []⟩ Dt ⟨LQ, List.replicate (e + 1) []⟩ A (endv v))
      (· = abank D ⟨ones v :: O, []⟩ Dt ⟨[] :: LQ, List.replicate e []⟩ A (endv (v + D)))
      (3 * v + 2 * D + 40) := by
  set σ := abank D ⟨O, []⟩ Dt ⟨LQ, List.replicate (e + 1) []⟩ A (endv v) with hσ
  have s0 := runs_back (a := 0) aV σ (by tsimp [hσ, abank, endv])
  set σ₀ := Function.update σ aV ⟨(σ aV).left.tail, (σ aV).left.headD [] :: (σ aV).right⟩ with hσ₀
  have s1 := runs_cpy (a := 0) (show aV ≠ aOut by decide) σ₀ (by tsimp [hσ₀, hσ, abank, endv])
    (by tsimp [hσ₀, hσ, abank])
  set σ₁ := abank D ⟨ones v :: O, []⟩ Dt ⟨LQ, List.replicate (e + 1) []⟩ A (endv v) with hσ₁
  have e1 : Function.update (Function.update σ₀ aV (σ₀ aV).next) aOut ((σ₀ aOut).put false [(σ₀ aV).cur]) = σ₁ := by
    funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hσ₀, hσ, abank, endv, WTape.put]
  rw [e1] at s1
  have s2 := runs_addA (c := D) (v := v) (show aKN ≠ aV by decide) σ₁ (by tsimp [hσ₁, abank]) (by tsimp [hσ₁, abank])
  set σ₂ := Function.update σ₁ aV (endv (v + D)) with hσ₂
  have s3 := runs_skp (a := 0) (show aQt ≠ aJ by decide) σ₂ (by tsimp [hσ₂, hσ₁, abank, List.replicate_succ])
    (by tsimp [hσ₂, hσ₁, abank, emp])
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 s3))).mono (fun τ h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, abank, WTape.next, List.replicate_succ]
  · tsimp [hσ₂, hσ₁, hσ₀, hσ, abank, endv, WTape.cur, List.replicate_succ, length_ones]; omega

theorem range_succ_map_reverse {β : Type*} (f : ℕ → β) (e : ℕ) :
    ((List.range (e + 1)).map f).reverse = ((List.range e).map fun j => f (j + 1)).reverse ++ [f 0] := by
  rw [List.range_succ_eq_map, List.map_cons, List.reverse_cons, List.map_map]; rfl

set_option maxHeartbeats 8000000 in
theorem runs_innerLoop {D : ℕ} {Dt A : WTape} :
    ∀ (e v : ℕ) (O LQ : List (List Bool)),
      Runs (.loop aQt innerBody) (abank D ⟨O, []⟩ Dt ⟨LQ, List.replicate e []⟩ A (endv v))
        (· = abank D ⟨((List.range e).map fun j => ones (v + j * D)).reverse ++ O, []⟩ Dt
          ⟨List.replicate e [] ++ LQ, []⟩ A (endv (v + e * D)))
        (e * (3 * (v + e * D) + 2 * D + 42))
  | 0, v, O, LQ => by
    refine (Runs.loop_done (by simp [abank]) rfl).mono (fun τ h => ?_) (by simp)
    rw [← h]; simp
  | e + 1, v, O, LQ => by
    have s1 := runs_innerBody (D := D) (O := O) (Dt := Dt) (A := A) (LQ := LQ) (e := e) (v := v)
    have ih := runs_innerLoop (D := D) (Dt := Dt) (A := A) e (v + D) (ones v :: O) ([] :: LQ)
    refine (Runs.loop_step (by simp [abank]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h, range_succ_map_reverse]
      have e1 : (fun j => ones (v + (j + 1) * D)) = fun j => ones (v + D + j * D) := by
        funext j; congr 1; ring
      have e2 : v + D + e * D = v + (e + 1) * D := by ring
      rw [e1, e2, List.append_assoc, List.replicate_succ', List.append_assoc]
      simp
    · have : v + D + e * D = v + (e + 1) * D := by ring
      rw [this]; nlinarith

/-- The cost of one axis. -/
def outerCost (D q V : ℕ) : ℕ := q * (3 * V + 2 * D + 42) + 4 * V + 2 * q + 2 * D + 80

set_option maxHeartbeats 8000000 in
theorem runs_outerBody {D q : ℕ} {O LD : List (List Bool)} {e a vp V : ℕ} (hV : a + q * D ≤ V) (hvp : vp ≤ V)
    (haV : a ≤ V) :
    Runs outerBody (abank D ⟨O, []⟩ ⟨LD, List.replicate (e + 1) []⟩ ⟨[], List.replicate q []⟩ (endv a) (endv vp))
      (· = abank D ⟨((List.range q).map fun j => ones (a + j * D)).reverse ++ O, []⟩
        ⟨[] :: LD, List.replicate e []⟩ ⟨[], List.replicate q []⟩ (endv (a + 1)) (endv (a + q * D)))
      (outerCost D q V) := by
  set σ := abank D ⟨O, []⟩ ⟨LD, List.replicate (e + 1) []⟩ ⟨[], List.replicate q []⟩ (endv a) (endv vp) with hσ
  have c1 := runs_clear (a := 0) aV σ
  set σa := Function.update σ aV ⟨[], []⟩ with hσa
  have c2 := runs_back (a := 0) aA σa (by tsimp [hσa, hσ, abank, endv])
  set σb := Function.update σa aA ⟨(σa aA).left.tail, (σa aA).left.headD [] :: (σa aA).right⟩ with hσb
  have c3 := runs_cpy (a := 0) (show aA ≠ aV by decide) σb (by tsimp [hσb, hσa, hσ, abank, endv])
    (by tsimp [hσb, hσa])
  have e0 : Function.update (Function.update σb aA (σb aA).next) aV ((σb aV).put false [(σb aA).cur]) =
      abank D ⟨O, []⟩ ⟨LD, List.replicate (e + 1) []⟩ ⟨[], List.replicate q []⟩ (endv a) (endv a) := by
    funext i; fin_cases i <;> first | rfl | tsimp [hσb, hσa, hσ, abank, endv, WTape.put]
  rw [e0] at c3
  set σ₁ := abank D ⟨O, []⟩ ⟨LD, List.replicate (e + 1) []⟩ ⟨[], List.replicate q []⟩ (endv a) (endv a) with hσ₁
  have s2 := runs_innerLoop (D := D) (Dt := ⟨LD, List.replicate (e + 1) []⟩) (A := endv a) q a O []
  set σ₂ := abank D ⟨((List.range q).map fun j => ones (a + j * D)).reverse ++ O, []⟩ ⟨LD, List.replicate (e + 1) []⟩
    ⟨List.replicate q [] ++ [], []⟩ (endv a) (endv (a + q * D)) with hσ₂
  have s3 := runs_rewind (a := 0) aQt σ₂
  set σ₃ := Function.update σ₂ aQt ⟨[], (σ₂ aQt).left.reverse ++ (σ₂ aQt).right⟩ with hσ₃
  have s4 := runs_addA (c := 1) (v := a) (show aOne ≠ aA by decide) σ₃ (by tsimp [hσ₃, hσ₂, abank])
    (by tsimp [hσ₃, hσ₂, abank])
  set σ₄ := Function.update σ₃ aA (endv (a + 1)) with hσ₄
  have s5 := runs_skp (a := 0) (show aDt ≠ aJ by decide) σ₄ (by tsimp [hσ₄, hσ₃, hσ₂, abank, List.replicate_succ])
    (by tsimp [hσ₄, hσ₃, hσ₂, abank, emp])
  refine (Runs.then c1 (Runs.then c2 (Runs.then c3 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))))).mono
    (fun τ h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₄, hσ₃, hσ₂, abank, WTape.next, List.replicate_succ,
      List.reverse_replicate]
  · have hc0 : clen (σ aV).words = vp + 1 := by tsimp [hσ, abank, endv, WTape.words, clen, length_ones]
    have hc1 : ((σa aA).left.headD []).length = a := by tsimp [hσa, hσ, abank, endv, length_ones]
    have hc2 : (σb aA).cur.length = a := by tsimp [hσb, hσa, hσ, abank, endv, WTape.cur, length_ones]
    rw [hc0, hc1, hc2]
    have hc : clen (σ₂ aQt).left = q := by tsimp [hσ₂, abank, clen]
    have hcur : (σ₄ aDt).cur.length = 0 := by tsimp [hσ₄, hσ₃, hσ₂, abank, WTape.cur, List.replicate_succ]
    rw [hc, hcur]
    simp only [outerCost]
    have : q * (3 * (a + q * D) + 2 * D + 42) ≤ q * (3 * V + 2 * D + 42) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- The words of the first `e` axes. -/
def arrWords (D q e : ℕ) : List (List Bool) :=
  ((List.range e).flatMap fun a => (List.range q).map fun j => ones (a + j * D))

theorem arrWords_succ (D q e : ℕ) :
    arrWords D q (e + 1) = arrWords D q e ++ (List.range q).map fun j => ones (e + j * D) := by
  simp [arrWords, List.range_succ, List.flatMap_append]

set_option maxHeartbeats 8000000 in
theorem runs_outerLoop {D q V : ℕ} (hV : D + q * D ≤ V) :
    ∀ (e a : ℕ) (LD : List (List Bool)) (vp : ℕ), a + e = D → vp ≤ V →
      Runs (.loop aDt outerBody) (abank D ⟨(arrWords D q a).reverse, []⟩ ⟨LD, List.replicate e []⟩
          ⟨[], List.replicate q []⟩ (endv a) (endv vp))
        (fun σ' => ∃ vf, vf ≤ V ∧ σ' = abank D ⟨(arrWords D q D).reverse, []⟩ ⟨List.replicate e [] ++ LD, []⟩
          ⟨[], List.replicate q []⟩ (endv D) (endv vf))
        (e * (outerCost D q V + 2))
  | 0, a, LD, vp, ha, hvp => by
    refine (Runs.loop_done (by simp [abank]) ⟨vp, hvp, ?_⟩).mono (fun τ h => h) (by simp)
    rw [show a = D by omega]; rfl
  | e + 1, a, LD, vp, ha, hvp => by
    have s1 := runs_outerBody (D := D) (q := q) (O := (arrWords D q a).reverse) (LD := LD) (e := e) (a := a) (vp := vp)
      (V := V) (by nlinarith) hvp (by omega)
    have ih := runs_outerLoop hV e (a + 1) ([] :: LD) (a + q * D) (by omega) (by nlinarith)
    have e1 : ((List.range q).map fun j => ones (a + j * D)).reverse ++ (arrWords D q a).reverse =
        (arrWords D q (a + 1)).reverse := by
      rw [arrWords_succ, List.reverse_append]
    rw [e1] at s1
    refine (Runs.loop_step (by simp [abank]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · obtain ⟨vf, hvf, e2⟩ := h
      refine ⟨vf, hvf, ?_⟩
      rw [e2, List.replicate_succ', List.append_assoc]; rfl
    · rw [Nat.succ_mul]; omega

theorem arrWords_axisArr (D q : ℕ) : arrWords D q D = (LayoutScript.axisArr q D).map ones := by
  rw [axisArr_rows, arrWords, List.map_flatMap]
  congr 1; funext a; rw [List.map_map]; congr 1; funext j; simp [Function.comp, add_comm]

/-- The cost of the arrangement generator. -/
def arrCost (D q V : ℕ) : ℕ := D * (outerCost D q V + 2) + 4 * D + 4 * V + 40

set_option maxHeartbeats 8000000 in
/-- `runs_arrGen`: the axis-major arrangement of `D` axes of `q` chunks as unary words on `aOut`. -/
theorem runs_arrGen {D q V : ℕ} (hV : D + q * D ≤ V) :
    Runs arrGen (abank D ⟨[], []⟩ ⟨[], List.replicate D []⟩ ⟨[], List.replicate q []⟩ emp emp)
      (· = abank D ⟨((LayoutScript.axisArr q D).map ones).reverse, []⟩ ⟨[], List.replicate D []⟩
        ⟨[], List.replicate q []⟩ emp emp)
      (arrCost D q V) := by
  set σ0 := abank D ⟨[], []⟩ ⟨[], List.replicate D []⟩ ⟨[], List.replicate q []⟩ emp emp with hσ0
  have c1 := runs_emit (a := 0) [[]] aA σ0 (by tsimp [hσ0, abank, emp])
  set σa := Function.update σ0 aA ⟨[[]].reverse ++ (σ0 aA).left, []⟩ with hσa
  have c2 := runs_emit (a := 0) [[]] aV σa (by tsimp [hσa, hσ0, abank, emp])
  have e0 : Function.update σa aV ⟨[[]].reverse ++ (σa aV).left, []⟩ =
      abank D ⟨(arrWords D q 0).reverse, []⟩ ⟨[], List.replicate D []⟩ ⟨[], List.replicate q []⟩ (endv 0) (endv 0) := by
    funext i; fin_cases i <;> first | rfl | tsimp [hσa, hσ0, abank, emp, endv, arrWords]
  rw [e0] at c2
  have s2 := runs_outerLoop (D := D) (q := q) (V := V) hV D 0 [] 0 (by omega) (by omega)
  obtain ⟨σ₂', k₂, hx₂, ⟨vf, hvf, h₂⟩, hk₂⟩ := s2
  subst h₂
  set σ₂ := abank D ⟨(arrWords D q D).reverse, []⟩ ⟨List.replicate D [] ++ [], []⟩ ⟨[], List.replicate q []⟩
    (endv D) (endv vf) with hσ₂
  have s2' : Runs (.loop aDt outerBody) (abank D ⟨(arrWords D q 0).reverse, []⟩ ⟨[], List.replicate D []⟩
      ⟨[], List.replicate q []⟩ (endv 0) (endv 0)) (· = σ₂) (D * (outerCost D q V + 2)) :=
    ⟨σ₂, k₂, hx₂, rfl, by simpa using hk₂⟩
  have t1 := runs_rewind (a := 0) aDt σ₂
  set σ₃ := Function.update σ₂ aDt ⟨[], (σ₂ aDt).left.reverse ++ (σ₂ aDt).right⟩ with hσ₃
  have t2 := runs_clear (a := 0) aA σ₃
  set σ₄ := Function.update σ₃ aA ⟨[], []⟩ with hσ₄
  have t3 := runs_clear (a := 0) aV σ₄
  refine (Runs.then c1 (Runs.then c2 (Runs.then s2' (Runs.then t1 (Runs.then t2 t3))))).mono (fun τ h => ?_) ?_
  · rw [h, ← arrWords_axisArr]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₄, hσ₃, hσ₂, abank, emp,
      List.reverse_replicate]
  · have h1 : clen (σ₂ aDt).left = D := by tsimp [hσ₂, abank, clen]
    have h2 : clen (σ₃ aA).words = D + 1 := by tsimp [hσ₃, hσ₂, abank, endv, WTape.words, clen, length_ones]
    have h3 : clen (σ₄ aV).words = vf + 1 := by tsimp [hσ₄, hσ₃, hσ₂, abank, endv, WTape.words, clen, length_ones]
    rw [h1, h2, h3]
    simp [arrCost, clen]
    omega

end LayoutGenSetup

end IntegerMultBounds.Schoenhage
