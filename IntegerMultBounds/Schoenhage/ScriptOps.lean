module

public import IntegerMultBounds.Schoenhage.Lists

/-! Small word programs on arbitrary tapes used by the round-script writer: append a
register's word to another register's word (`appendReg`), truncated unary subtraction
into a register (`dropReg`), a unary register as ticks (`ticksReg`), copy a register out
(`cpyReg`), copy the word before the head and step back over it (`readBack`), double a
unary word (`dbl`), write `ones (2^e)` (`pow2`), and append a list of words preceded by
its length in unary (`emitTab`). Each has an exact effect and a step bound. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a t : ℕ}

namespace ScriptOps

theorem ones_append_ones (m n : ℕ) : ones m ++ ones n = ones (m + n) := by
  unfold ones; rw [List.replicate_add]

@[simp] theorem clen_rep (k : ℕ) : clen (List.replicate k ([] : List Bool)) = k := by
  simp [clen]

theorem time_ticks (w : List Bool) (ws : Fin 0 → List Bool) : time Rules.ticks w ws = w.length + 5 := by
  simp [time, rest]

/-! ### Primitive steps in clean form -/

theorem runs_copyApp {s d : Fin t} (h : s ≠ d) (σ : Fin t → WTape) {u v : List Bool} {M : List (List Bool)}
    (hs : σ s = reg u) (hd : σ d = ⟨v :: M, []⟩) :
    Runs (a := a) (op0 Rules.copy true s d h) σ
      (· = Function.update (Function.update σ s ⟨[u], []⟩) d ⟨(v ++ u) :: M, []⟩) (u.length + 6) := by
  apply Runs.of_wp
  rw [wp_op0]
  simp only [Rules.output_copy, parse_syms]
  refine ⟨⟨by simp [hs], by simp [hd], by simp, fun _ => ⟨by simp [hd], by simp⟩⟩, ?_, ?_⟩
  · simp [hs, hd]
  · simp [hs, time_copy]

theorem runs_drop1 {d e o : Fin t} (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o) (σ : Fin t → WTape)
    {u v : List Bool} (hd : σ d = reg u) (he : σ e = reg v) (ho : σ o = emp) :
    Runs (a := a) (op1 Rules.drop false d e o h1 h2 h3) σ
      (· = Function.update (Function.update (Function.update σ d ⟨[u], []⟩) e ⟨[v], []⟩) o
        ⟨[u.drop v.length], []⟩) (u.length + v.length + 6) := by
  have t1 : time Rules.drop u (fun _ => v) ≤ u.length + v.length + 6 :=
    (time_le Rules.drop u (fun _ => v) v.length (fun _ => le_rfl)).trans (by simp)
  apply Runs.of_wp
  rw [wp_op1]
  simp only [Rules.output_drop, parse_syms]
  refine ⟨⟨by simp [hd], by simp [he], by simp [ho], by simp [hd, he], by simp⟩, ?_, ?_⟩
  · simp [hd, he, ho, emp]
  · simpa [hd, he] using t1

theorem runs_ticks1 {s o : Fin t} (h : s ≠ o) (σ : Fin t → WTape) {u : List Bool}
    (hs : σ s = reg u) (ho : σ o = emp) :
    Runs (a := a) (op0 Rules.ticks false s o h) σ
      (· = Function.update (Function.update σ s ⟨[u], []⟩) o ⟨List.replicate u.length [], []⟩)
      (u.length + 5) := by
  apply Runs.of_wp
  rw [wp_op0]
  simp only [Rules.output_ticks, parse_syms]
  refine ⟨⟨by simp [hs], by simp [ho], by simp, by simp⟩, ?_, ?_⟩
  · simp [hs, ho, emp]
  · simp [hs, time_ticks]

theorem runs_rewind' (i : Fin t) (σ : Fin t → WTape) {L R : List (List Bool)} (hi : σ i = ⟨L, R⟩) :
    Runs (a := a) (rewind i) σ (· = Function.update σ i ⟨[], L.reverse ++ R⟩) (clen L + 2) := by
  have := runs_rewind (a := a) i σ
  rw [hi] at this
  exact this

theorem runs_clear' (i : Fin t) (σ : Fin t → WTape) {T : WTape} (hi : σ i = T) :
    Runs (a := a) (clear i) σ (· = Function.update σ i emp) (2 * clen T.words + 2) := by
  have := runs_clear (a := a) i σ
  rw [hi] at this
  exact this

/-! ### Append a register to a register -/

/-- Append the word of register `s` to the last word of `d` (head after it); `s` is kept. -/
noncomputable def appendReg (s d : Fin t) (h : s ≠ d) : Cmd a t := .seq (op0 Rules.copy true s d h) (rewind s)

theorem runs_appendReg {s d : Fin t} (h : s ≠ d) (σ : Fin t → WTape) {u v : List Bool} {M : List (List Bool)}
    (hs : σ s = reg u) (hd : σ d = ⟨v :: M, []⟩) :
    Runs (a := a) (appendReg s d h) σ (· = Function.update σ d ⟨(v ++ u) :: M, []⟩) (2 * u.length + 10) := by
  have s1 := runs_copyApp (a := a) h σ hs hd
  set σ₁ := Function.update (Function.update σ s ⟨[u], []⟩) d ⟨(v ++ u) :: M, []⟩ with hσ₁
  have s2 := runs_rewind' (a := a) s σ₁ (L := [u]) (R := []) (by simp [hσ₁, h])
  refine (Runs.then s1 s2).mono (fun σ' e => ?_) ?_
  · rw [e, hσ₁, Function.update_comm h, Function.update_idem, Function.update_comm h.symm]
    have : Function.update σ s ⟨[], [u].reverse ++ []⟩ = σ := by
      rw [show (⟨[], [u].reverse ++ []⟩ : WTape) = reg u by simp [reg], ← hs, Function.update_eq_self]
    rw [this]
  · simp [clen]; omega

/-! ### Truncated subtraction -/

/-- `o := d - e` on unary registers (`o` empty before). -/
noncomputable def dropReg (d e o : Fin t) (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o) : Cmd a t :=
  .seq (op1 Rules.drop false d e o h1 h2 h3) <| .seq (rewind d) <| .seq (rewind e) (rewind o)

theorem runs_dropReg {d e o : Fin t} (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o) (σ : Fin t → WTape)
    {u v : List Bool} (hd : σ d = reg u) (he : σ e = reg v) (ho : σ o = emp) :
    Runs (a := a) (dropReg d e o h1 h2 h3) σ (· = Function.update σ o (reg (u.drop v.length)))
      (4 * u.length + 4 * v.length + 40) := by
  have s1 := runs_drop1 (a := a) h1 h2 h3 σ hd he ho
  set σ₁ := Function.update (Function.update (Function.update σ d ⟨[u], []⟩) e ⟨[v], []⟩) o
    ⟨[u.drop v.length], []⟩ with hσ₁
  have s2 := runs_rewind' (a := a) d σ₁ (L := [u]) (R := []) (by simp [hσ₁, h1, h2])
  set σ₂ := Function.update σ₁ d ⟨[], [u].reverse ++ []⟩ with hσ₂
  have s3 := runs_rewind' (a := a) e σ₂ (L := [v]) (R := []) (by simp [hσ₂, hσ₁, h1.symm, h3])
  set σ₃ := Function.update σ₂ e ⟨[], [v].reverse ++ []⟩ with hσ₃
  have s4 := runs_rewind' (a := a) o σ₃ (L := [u.drop v.length]) (R := [])
    (by simp [hσ₃, hσ₂, hσ₁, h2.symm, h3.symm])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext x
    by_cases hxo : x = o
    · subst hxo; simp [reg]
    · by_cases hxe : x = e
      · subst hxe; simp [hσ₃, hxo, he, reg]
      · by_cases hxd : x = d
        · subst hxd; simp [hσ₃, hσ₂, hxo, hxe, hd, reg]
        · simp [hσ₃, hσ₂, hσ₁, hxo, hxe, hxd]
  · simp [clen]; omega

/-! ### Ticks -/

/-- `o := ticks |s|` (`o` empty before). -/
noncomputable def ticksReg (s o : Fin t) (h : s ≠ o) : Cmd a t :=
  .seq (op0 Rules.ticks false s o h) <| .seq (rewind s) (rewind o)

theorem runs_ticksReg {s o : Fin t} (h : s ≠ o) (σ : Fin t → WTape) {u : List Bool}
    (hs : σ s = reg u) (ho : σ o = emp) :
    Runs (a := a) (ticksReg s o h) σ (· = Function.update σ o ⟨[], List.replicate u.length []⟩)
      (3 * u.length + 20) := by
  have s1 := runs_ticks1 (a := a) h σ hs ho
  set σ₁ := Function.update (Function.update σ s ⟨[u], []⟩) o ⟨List.replicate u.length [], []⟩ with hσ₁
  have s2 := runs_rewind' (a := a) s σ₁ (L := [u]) (R := []) (by simp [hσ₁, h])
  set σ₂ := Function.update σ₁ s ⟨[], [u].reverse ++ []⟩ with hσ₂
  have s3 := runs_rewind' (a := a) o σ₂ (L := List.replicate u.length []) (R := []) (by simp [hσ₂, hσ₁, h.symm])
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext x
    by_cases hxo : x = o
    · subst hxo; simp
    · by_cases hxs : x = s
      · subst hxs; simp [hσ₂, hxo, hs, reg]
      · simp [hσ₂, hσ₁, hxo, hxs]
  · simp [clen]; omega

/-! ### Copy a register out -/

/-- Append the word of register `r` as a new word of `d`; `r` is kept. -/
noncomputable def cpyReg (r d : Fin t) (h : r ≠ d) : Cmd a t := .seq (cpy r d h) (rewind r)

theorem runs_cpyReg {r d : Fin t} (h : r ≠ d) (σ : Fin t → WTape) {u : List Bool} {M : List (List Bool)}
    (hr : σ r = reg u) (hd : σ d = ⟨M, []⟩) :
    Runs (a := a) (cpyReg r d h) σ (· = Function.update σ d ⟨u :: M, []⟩) (2 * u.length + 10) := by
  have s1 := runs_cpy (a := a) h σ (by simp [hr]) (by simp [hd])
  set σ₁ := Function.update (Function.update σ r ⟨[u], []⟩) d ⟨u :: M, []⟩ with hσ₁
  have e1 : Function.update (Function.update σ r (σ r).next) d ((σ d).put false [(σ r).cur]) = σ₁ := by
    simp [hσ₁, hr, hd]
  rw [e1] at s1
  have s2 := runs_rewind' (a := a) r σ₁ (L := [u]) (R := []) (by simp [hσ₁, h])
  refine (Runs.then s1 s2).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext x
    by_cases hxr : x = r
    · subst hxr; simp [h, hr, reg]
    · by_cases hxd : x = d
      · subst hxd; simp [hσ₁, hxr]
      · simp [hσ₁, hxr, hxd]
  · simp [hr, time_copy, clen]; omega

/-! ### Read the word before the head -/

/-- Copy the word just before the head of `s` to `d` and leave the head before it. -/
noncomputable def readBack (s d : Fin t) (h : s ≠ d) : Cmd a t := .seq (back s) <| .seq (cpy s d h) (back s)

theorem runs_readBack {s d : Fin t} (h : s ≠ d) (σ : Fin t → WTape) {w : List Bool}
    {L R M : List (List Bool)} (hs : σ s = ⟨w :: L, R⟩) (hd : σ d = ⟨M, []⟩) :
    Runs (a := a) (readBack s d h) σ (· = Function.update (Function.update σ s ⟨L, w :: R⟩) d ⟨w :: M, []⟩)
      (3 * w.length + 15) := by
  have s1 := runs_back (a := a) s σ (by simp [hs])
  set σ₁ := Function.update σ s ⟨L, w :: R⟩ with hσ₁
  have e1 : Function.update σ s ⟨(σ s).left.tail, (σ s).left.headD [] :: (σ s).right⟩ = σ₁ := by
    simp [hσ₁, hs]
  rw [e1] at s1
  have s2 := runs_cpy (a := a) h σ₁ (by simp [hσ₁]) (by simp [hσ₁, h.symm, hd])
  set σ₂ := Function.update (Function.update σ₁ s ⟨w :: L, R⟩) d ⟨w :: M, []⟩ with hσ₂
  have e2 : Function.update (Function.update σ₁ s (σ₁ s).next) d ((σ₁ d).put false [(σ₁ s).cur]) = σ₂ := by
    simp [hσ₂, hσ₁, h.symm, hd]
  rw [e2] at s2
  have s3 := runs_back (a := a) s σ₂ (by simp [hσ₂, h])
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext x
    by_cases hxd : x = d
    · subst hxd; simp [hσ₂, h.symm]
    · by_cases hxs : x = s
      · subst hxs; simp [hσ₂, hσ₁, h]
      · simp [hσ₂, hσ₁, hxd, hxs]
  · simp [hσ₂, hσ₁, h, hs, time_copy]; omega

/-! ### Doubling -/

/-- Double the unary word of `w` (head after it), using the scratch register `s`. -/
noncomputable def dbl (w s : Fin t) (h : w ≠ s) : Cmd a t :=
  .seq (rewind w) <| .seq (cpy w s h) <| .seq (rewind s) <| .seq (op0 Rules.copy true s w h.symm) (clear s)

theorem runs_dbl {w s : Fin t} (h : w ≠ s) (σ : Fin t → WTape) {n : ℕ} (hw : σ w = ⟨[ones n], []⟩)
    (hs : σ s = emp) :
    Runs (a := a) (dbl w s h) σ (· = Function.update σ w ⟨[ones (2 * n)], []⟩) (8 * n + 40) := by
  have s1 := runs_rewind' (a := a) w σ hw
  set σ₁ := Function.update σ w (reg (ones n)) with hσ₁
  have e1 : Function.update σ w ⟨[], [ones n].reverse ++ []⟩ = σ₁ := by simp [hσ₁, reg]
  rw [e1] at s1
  have s2 := runs_cpy (a := a) h σ₁ (by simp [hσ₁]) (by simp [hσ₁, h.symm, hs])
  set σ₂ := Function.update (Function.update σ₁ w ⟨[ones n], []⟩) s ⟨[ones n], []⟩ with hσ₂
  have e2 : Function.update (Function.update σ₁ w (σ₁ w).next) s ((σ₁ s).put false [(σ₁ w).cur]) = σ₂ := by
    simp [hσ₂, hσ₁, h.symm, hs, emp]
  rw [e2] at s2
  have s3 := runs_rewind' (a := a) s σ₂ (L := [ones n]) (R := []) (by simp [hσ₂])
  set σ₃ := Function.update σ₂ s (reg (ones n)) with hσ₃
  have e3 : Function.update σ₂ s ⟨[], [ones n].reverse ++ []⟩ = σ₃ := by simp [hσ₃, reg]
  rw [e3] at s3
  have s4 := runs_copyApp (a := a) h.symm σ₃ (u := ones n) (v := ones n) (M := []) (by simp [hσ₃])
    (by simp [hσ₃, hσ₂, h])
  set σ₄ := Function.update (Function.update σ₃ s ⟨[ones n], []⟩) w ⟨(ones n ++ ones n) :: [], []⟩ with hσ₄
  have s5 := runs_clear' (a := a) s σ₄ (T := ⟨[ones n], []⟩) (by simp [hσ₄, h.symm])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext x
    by_cases hxw : x = w
    · subst hxw; simp [hσ₄, h, ones_append_ones, two_mul]
    · by_cases hxs : x = s
      · subst hxs; simp [hs, h.symm]
      · simp [hσ₄, hσ₃, hσ₂, hσ₁, hxw, hxs]
  · simp [hσ₁, time_copy, clen, WTape.words]; omega

/-! ### Powers of two -/

/-- The doubling loop over the ticks of `k`. -/
noncomputable def dblLoop (k w s j : Fin t) (h1 : w ≠ s) (h2 : k ≠ j) : Cmd a t :=
  .loop k (.seq (dbl w s h1) (skp k j h2))

theorem runs_dblLoop {k w s j : Fin t} (h1 : w ≠ s) (h2 : k ≠ j) (hkw : k ≠ w) (hks : k ≠ s) (hwj : w ≠ j)
    (hsj : s ≠ j) :
    ∀ (e n : ℕ) (σ : Fin t → WTape) (L : List (List Bool)), σ k = ⟨L, List.replicate e []⟩ →
      σ w = ⟨[ones n], []⟩ → σ s = emp → (σ j).right = [] →
      Runs (a := a) (dblLoop k w s j h1 h2) σ
        (· = Function.update (Function.update σ k ⟨List.replicate e [] ++ L, []⟩) w ⟨[ones (2 ^ e * n)], []⟩)
        (e * (8 * (2 ^ e * n) + 50))
  | 0, n, σ, L, hk, hw, hs, hj => by
    show Runs (Cmd.loop k _) _ _ _
    refine (Runs.loop_done (by simp [hk]) rfl).mono (fun σ' e => ?_) (by simp)
    subst e
    funext x
    by_cases hxw : x = w
    · subst hxw; simp [hw]
    · by_cases hxk : x = k
      · subst hxk; simp [hxw, hk]
      · simp [hxw, hxk]
  | e + 1, n, σ, L, hk, hw, hs, hj => by
    show Runs (Cmd.loop k _) _ _ _
    have s1 := runs_dbl (a := a) h1 σ hw hs
    set σ₁ := Function.update σ w ⟨[ones (2 * n)], []⟩ with hσ₁
    have hk₁ : σ₁ k = ⟨L, [] :: List.replicate e []⟩ := by simp [hσ₁, hkw, hk, List.replicate_succ]
    have s2 := runs_skp (a := a) h2 σ₁ (by simp [hk₁]) (by simp [hσ₁, hwj.symm, hj])
    set σ₂ := Function.update σ₁ k ⟨[] :: L, List.replicate e []⟩ with hσ₂
    have e2 : Function.update σ₁ k (σ₁ k).next = σ₂ := by simp [hσ₂, hk₁]
    rw [e2] at s2
    have ih := runs_dblLoop h1 h2 hkw hks hwj hsj e (2 * n) σ₂ ([] :: L) (by simp [hσ₂])
      (by simp [hσ₂, hσ₁, hkw.symm]) (by simp [hσ₂, hσ₁, hks.symm, h1.symm, hs])
      (by simp [hσ₂, hσ₁, h2.symm, hwj.symm, hj])
    refine (Runs.loop_step (by simp [hk]) ((Runs.then s1 s2).mono (fun σ' e' => by rw [e']; exact ih)
      le_rfl)).mono (fun σ' e' => ?_) ?_
    · rw [e']
      have e1 : 2 ^ e * (2 * n) = 2 ^ (e + 1) * n := by ring
      have e3 : List.replicate e [] ++ [] :: L = List.replicate (e + 1) ([] : List Bool) ++ L := by
        simp [List.replicate_succ']
      funext x
      by_cases hxw : x = w
      · subst hxw; simp [e1]
      · by_cases hxk : x = k
        · subst hxk; simp [hxw, e3]
        · simp [hσ₂, hσ₁, hxw, hxk]
    · have hc : (σ₁ k).cur.length = 0 := by simp [hk₁]
      rw [hc]
      have e1 : 2 ^ e * (2 * n) = 2 ^ (e + 1) * n := by ring
      rw [e1]
      have hp : 2 * n ≤ 2 ^ (e + 1) * n := by
        have : 2 ≤ 2 ^ (e + 1) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith
      nlinarith

/-- `w := ones (2^e)` from the unary register `s = ones e`, with the tick tape `k`, the doubling
scratch `c` and the junk tape `j`. -/
noncomputable def pow2 (s k w c j : Fin t) (h1 : s ≠ k) (h2 : w ≠ c) (h3 : k ≠ j) : Cmd a t :=
  .seq (ticksReg s k h1) <| .seq (emit [[true]] w) <| .seq (dblLoop k w c j h2 h3) (clear k)

theorem runs_pow2 {s k w c j : Fin t} (h1 : s ≠ k) (h2 : w ≠ c) (h3 : k ≠ j) (hkw : k ≠ w) (hkc : k ≠ c)
    (hwj : w ≠ j) (hcj : c ≠ j) (hsw : s ≠ w) (hsc : s ≠ c) (σ : Fin t → WTape) {e : ℕ}
    (hs : σ s = reg (ones e)) (hk : σ k = emp) (hw : σ w = emp) (hc : σ c = emp) (hj : (σ j).right = []) :
    Runs (a := a) (pow2 s k w c j h1 h2 h3) σ (· = Function.update σ w ⟨[ones (2 ^ e)], []⟩)
      (e * (8 * 2 ^ e + 50) + 6 * e + 30) := by
  have s1 := runs_ticksReg (a := a) h1 σ hs hk
  set σ₁ := Function.update σ k ⟨[], List.replicate e []⟩ with hσ₁
  have e1 : Function.update σ k ⟨[], List.replicate (ones e).length []⟩ = σ₁ := by simp [hσ₁]
  rw [e1] at s1
  have s2 := runs_emit (a := a) [[true]] w σ₁ (by simp [hσ₁, hkw.symm, hw])
  set σ₂ := Function.update σ₁ w ⟨[ones 1], []⟩ with hσ₂
  have e2 : Function.update σ₁ w ⟨[[true]].reverse ++ (σ₁ w).left, []⟩ = σ₂ := by
    simp [hσ₂, hσ₁, hkw.symm, hw, ones]
  rw [e2] at s2
  have s3 := runs_dblLoop (a := a) h2 h3 hkw hkc hwj hcj e 1 σ₂ [] (by simp [hσ₂, hσ₁, hkw]) (by simp [hσ₂])
    (by simp [hσ₂, hσ₁, hkc.symm, h2.symm, hc]) (by simp [hσ₂, hσ₁, h3.symm, hwj.symm, hj])
  set σ₃ := Function.update (Function.update σ₂ k ⟨List.replicate e [] ++ [], []⟩) w ⟨[ones (2 ^ e * 1)], []⟩
    with hσ₃
  have s4 := runs_clear' (a := a) k σ₃ (T := ⟨List.replicate e [] ++ [], []⟩) (by simp [hσ₃, hkw])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext x
    by_cases hxw : x = w
    · subst hxw; simp [hσ₃, hkw.symm]
    · by_cases hxk : x = k
      · subst hxk; simp [hσ₃, hσ₂, hσ₁, hxw, hk]
      · simp [hσ₃, hσ₂, hσ₁, hxw, hxk]
  · simp [clen, WTape.words]; omega

/-! ### A list of words with its length -/

/-- The counting loop: one tick of `c` per word of `s`. -/
noncomputable def countLoop (s c one j : Fin t) (h1 : s ≠ j) (h2 : one ≠ c) : Cmd a t :=
  .loop s (.seq (skp s j h1) (appendReg one c h2))

theorem runs_countLoop {s c one j : Fin t} (h1 : s ≠ j) (h2 : one ≠ c) (hsc : s ≠ c) (hso : s ≠ one)
    (hcj : c ≠ j) (hoj : one ≠ j) (W : ℕ) :
    ∀ (R : List (List Bool)) (σ : Fin t → WTape) (L : List (List Bool)) (n : ℕ), σ s = ⟨L, R⟩ →
      σ c = ⟨[ones n], []⟩ → σ one = reg [true] → (σ j).right = [] → (∀ w ∈ R, w.length ≤ W) →
      Runs (a := a) (countLoop s c one j h1 h2) σ
        (· = Function.update (Function.update σ s ⟨R.reverse ++ L, []⟩) c ⟨[ones (n + R.length)], []⟩)
        (R.length * (W + 20))
  | [], σ, L, n, hs, hc, ho, hj, _ => by
    show Runs (Cmd.loop s _) _ _ _
    refine (Runs.loop_done (by simp [hs]) rfl).mono (fun σ' e => ?_) (by simp)
    subst e
    funext x
    by_cases hxc : x = c
    · subst hxc; simp [hc]
    · by_cases hxs : x = s
      · subst hxs; simp [hxc, hs]
      · simp [hxc, hxs]
  | w :: R, σ, L, n, hs, hc, ho, hj, hW => by
    show Runs (Cmd.loop s _) _ _ _
    have s1 := runs_skp (a := a) h1 σ (by simp [hs]) hj
    set σ₁ := Function.update σ s ⟨w :: L, R⟩ with hσ₁
    have e1 : Function.update σ s (σ s).next = σ₁ := by simp [hσ₁, hs]
    rw [e1] at s1
    have s2 := runs_appendReg (a := a) h2 σ₁ (u := [true]) (v := ones n) (M := []) (by simp [hσ₁, hso.symm, ho])
      (by simp [hσ₁, hsc.symm, hc])
    set σ₂ := Function.update σ₁ c ⟨(ones n ++ [true]) :: [], []⟩ with hσ₂
    have hc₂ : σ₂ c = ⟨[ones (n + 1)], []⟩ := by simp [hσ₂, ones, List.replicate_succ']
    have ih := runs_countLoop h1 h2 hsc hso hcj hoj W R σ₂ (w :: L) (n + 1) (by simp [hσ₂, hσ₁, hsc]) hc₂
      (by simp [hσ₂, hσ₁, hso.symm, h2, ho]) (by simp [hσ₂, hσ₁, hcj.symm, h1.symm, hj])
      (fun v hv => hW v (by simp [hv]))
    refine (Runs.loop_step (by simp [hs]) ((Runs.then s1 s2).mono (fun σ' e' => by rw [e']; exact ih)
      le_rfl)).mono (fun σ' e' => ?_) ?_
    · rw [e']
      have e1' : n + 1 + R.length = n + (w :: R).length := by simp; ring
      funext x
      by_cases hxc : x = c
      · subst hxc; simp [e1']
      · by_cases hxs : x = s
        · subst hxs; simp [hxc]
        · simp [hσ₂, hσ₁, hxc, hxs]
    · have hw : w.length ≤ W := hW w (by simp)
      simp only [List.length_cons, List.length_singleton, hs, WTape.cur_mk, List.headD_cons, List.length_nil]
      nlinarith

/-- Append the words of `s` (head after them) to `d`, preceded by their number in unary; `s` is
emptied, `c` is a scratch register, `one = [true]`, `j` a junk tape. -/
noncomputable def emitTab (s d c one j : Fin t) (h1 : s ≠ j) (h2 : one ≠ c) (h3 : c ≠ d) (h4 : s ≠ d) : Cmd a t :=
  .seq (rewind s) <| .seq (emit [[]] c) <| .seq (countLoop s c one j h1 h2) <| .seq (rewind c) <|
  .seq (cpy c d h3) <| .seq (clear c) <| .seq (rewind s) <| .seq (appendAll s d h4) (clear s)

theorem runs_emitTab {s d c one j : Fin t} (h1 : s ≠ j) (h2 : one ≠ c) (h3 : c ≠ d) (h4 : s ≠ d)
    (hsc : s ≠ c) (hso : s ≠ one) (hcj : c ≠ j) (hoj : one ≠ j) (hod : one ≠ d) (hdj : d ≠ j) (W : ℕ)
    (σ : Fin t → WTape) (ws : List (List Bool)) (M : List (List Bool)) (hs : σ s = ⟨ws.reverse, []⟩)
    (hd : σ d = ⟨M, []⟩) (hc : σ c = emp) (ho : σ one = reg [true]) (hj : (σ j).right = [])
    (hW : ∀ w ∈ ws, w.length ≤ W) :
    Runs (a := a) (emitTab s d c one j h1 h2 h3 h4) σ
      (· = Function.update (Function.update σ s emp) d ⟨ws.reverse ++ ones ws.length :: M, []⟩)
      (ws.length * (7 * W + 60) + 80) := by
  have hsumW : (ws.map List.length).sum ≤ ws.length * W := by
    have := List.sum_le_length_nsmul (ws.map List.length) W (fun x hx => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hW w hw)
    simpa [mul_comm] using this
  have hcl : clen ws.reverse = clen ws := by simp [clen, List.map_reverse, List.sum_reverse]
  have s1 := runs_rewind' (a := a) s σ hs
  set σ₁ := Function.update σ s ⟨[], ws⟩ with hσ₁
  have e1 : Function.update σ s ⟨[], ws.reverse.reverse ++ []⟩ = σ₁ := by simp [hσ₁]
  rw [e1] at s1
  have s2 := runs_emit (a := a) [[]] c σ₁ (by simp [hσ₁, hsc.symm, hc])
  set σ₂ := Function.update σ₁ c ⟨[ones 0], []⟩ with hσ₂
  have e2 : Function.update σ₁ c ⟨[[]].reverse ++ (σ₁ c).left, []⟩ = σ₂ := by simp [hσ₂, hσ₁, hsc.symm, hc, ones]
  rw [e2] at s2
  have s3 := runs_countLoop (a := a) h1 h2 hsc hso hcj hoj W ws σ₂ [] 0 (by simp [hσ₂, hσ₁, hsc])
    (by simp [hσ₂]) (by simp [hσ₂, hσ₁, h2, hso.symm, ho]) (by simp [hσ₂, hσ₁, hcj.symm, h1.symm, hj]) hW
  set σ₃ := Function.update (Function.update σ₂ s ⟨ws.reverse ++ [], []⟩) c ⟨[ones (0 + ws.length)], []⟩
    with hσ₃
  have s4 := runs_rewind' (a := a) c σ₃ (L := [ones (0 + ws.length)]) (R := []) (by simp [hσ₃])
  set σ₄ := Function.update σ₃ c (reg (ones ws.length)) with hσ₄
  have e4 : Function.update σ₃ c ⟨[], [ones (0 + ws.length)].reverse ++ []⟩ = σ₄ := by simp [hσ₄, reg]
  rw [e4] at s4
  have s5 := runs_cpy (a := a) h3 σ₄ (by simp [hσ₄, reg]) (by simp [hσ₄, hσ₃, hσ₂, hσ₁, h3.symm, h4.symm, hd])
  set σ₅ := Function.update (Function.update σ₄ c ⟨[ones ws.length], []⟩) d ⟨ones ws.length :: M, []⟩ with hσ₅
  have e5 : Function.update (Function.update σ₄ c (σ₄ c).next) d ((σ₄ d).put false [(σ₄ c).cur]) = σ₅ := by
    simp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, h3.symm, h4.symm, hd, reg]
  rw [e5] at s5
  have s6 := runs_clear' (a := a) c σ₅ (T := ⟨[ones ws.length], []⟩) (by simp [hσ₅, h3])
  set σ₆ := Function.update σ₅ c emp with hσ₆
  have s7 := runs_rewind' (a := a) s σ₆ (L := ws.reverse ++ []) (R := []) (by simp [hσ₆, hσ₅, hσ₄, hσ₃, hsc, h4])
  set σ₇ := Function.update σ₆ s ⟨[], ws⟩ with hσ₇
  have e7 : Function.update σ₆ s ⟨[], (ws.reverse ++ []).reverse ++ []⟩ = σ₇ := by simp [hσ₇]
  rw [e7] at s7
  have s8 := runs_appendAll (a := a) h4 W ws σ₇ [] (ones ws.length :: M) (by simp [hσ₇])
    (by simp [hσ₇, hσ₆, hσ₅, h4.symm, h3.symm]) hW
  set σ₈ := Function.update (Function.update σ₇ s ⟨ws.reverse ++ [], []⟩) d
    ⟨ws.reverse ++ ones ws.length :: M, []⟩ with hσ₈
  have s9 := runs_clear' (a := a) s σ₈ (T := ⟨ws.reverse ++ [], []⟩) (by simp [hσ₈, h4])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 s9)))))))).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext x
    by_cases hxs : x = s
    · subst hxs; simp [h4]
    · by_cases hxd : x = d
      · subst hxd; simp [hσ₈, hxs]
      · by_cases hxc : x = c
        · subst hxc; simp [hσ₈, hσ₇, hσ₆, hxs, hxd, hc]
        · simp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hxs, hxd, hxc]
  · have hcl2 : clen ws = (ws.map List.length).sum + ws.length := by
      simp [clen, List.sum_map_add]
    simp [hσ₄, reg, WTape.words, time_copy, hcl, hcl2, clen_cons, clen_nil, clen_append]
    nlinarith

end ScriptOps

end IntegerMultBounds.Schoenhage
