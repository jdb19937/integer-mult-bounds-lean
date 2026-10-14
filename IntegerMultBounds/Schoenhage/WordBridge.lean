module

public import IntegerMultBounds.Schoenhage.Chunk
public import IntegerMultBounds.Schoenhage.Lists

/-! Between a contiguous bit array and a list of fixed-width words with the
bit order turned, on word tapes. `revLoop` moves every word of a tape to
another, reversed (`runs_revLoop`); `joinLoop` appends every word of a tape
to one growing word (`runs_joinLoop`). `toWords` cuts the array on tape `0`
into words of the width on tape `1` and reverses each onto tape `2`
(`runs_toWords`); `fromWords` reverses the words on tape `2` and joins them
into one array on tape `0` (`runs_fromWords`). The paper's arrays store their
components most significant bit first; the resampling machines store them
least significant bit first. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a t : ℕ}

/-! ### Moving and joining words -/

/-- Move every word of `src` to `dst`, reversed. -/
noncomputable def revLoop (src dst : Fin t) (h : src ≠ dst) : Cmd a t := .loop src (revw src dst h)

theorem runs_revLoop {src dst : Fin t} (h : src ≠ dst) {W : ℕ} :
    ∀ (ws : List (List Bool)) (σ : Fin t → WTape) (Ls D : List (List Bool)),
      (∀ x ∈ ws, x.length ≤ W) → σ src = ⟨Ls, ws⟩ → σ dst = ⟨D, []⟩ →
      Runs (a := a) (revLoop src dst h) σ (· = Function.update (Function.update σ
        src ⟨ws.reverse ++ Ls, []⟩) dst ⟨(ws.map List.reverse).reverse ++ D, []⟩) (ws.length * (3 * W + 12))
  | [], σ, Ls, D, _, hs, hd => by
    refine (Runs.loop_done (by simp [hs]) rfl).mono (fun σ' e => ?_) (by simp)
    rw [← e]; funext y
    by_cases a1 : y = src <;> by_cases a2 : y = dst <;> simp_all
  | x :: ws, σ, Ls, D, hW, hs, hd => by
    have hx := hW x (by simp)
    have s1 := runs_revw (a := a) h σ (L := Ls) (R := ws) (w := x) hs (by simp [hd])
    have ih := runs_revLoop h ws (Function.update (Function.update σ src ⟨x :: Ls, ws⟩) dst
        ⟨x.reverse :: (σ dst).left, []⟩) (x :: Ls) (x.reverse :: D) (fun y hy => hW y (by simp [hy]))
      (by simp [Function.update_of_ne h]) (by simp [hd])
    refine (Runs.loop_step (by simp [hs]) (s1.mono (fun σ' e => by rw [e]; exact ih) le_rfl)).mono
      (fun σ' e => ?_) ?_
    · rw [e]; funext y
      by_cases a1 : y = src <;> by_cases a2 : y = dst <;> simp_all
    · simp only [List.length_cons]; nlinarith

/-- Append every word of `src` to the last word of `dst`. -/
noncomputable def joinLoop (src dst : Fin t) (h : src ≠ dst) : Cmd a t :=
  .loop src (op0 Rules.copy true src dst h)

theorem runs_joinLoop {src dst : Fin t} (h : src ≠ dst) {W : ℕ} :
    ∀ (ws : List (List Bool)) (σ : Fin t → WTape) (Ls : List (List Bool)) (acc : List Bool),
      (∀ x ∈ ws, x.length ≤ W) → σ src = ⟨Ls, ws⟩ → σ dst = ⟨[acc], []⟩ →
      Runs (a := a) (joinLoop src dst h) σ (· = Function.update (Function.update σ
        src ⟨ws.reverse ++ Ls, []⟩) dst ⟨[acc ++ ws.flatten], []⟩) (ws.length * (W + 9))
  | [], σ, Ls, acc, _, hs, hd => by
    refine (Runs.loop_done (by simp [hs]) rfl).mono (fun σ' e => ?_) (by simp)
    rw [← e]; funext y
    by_cases a1 : y = src <;> by_cases a2 : y = dst <;> simp_all
  | x :: ws, σ, Ls, acc, hW, hs, hd => by
    have hx := hW x (by simp)
    have s1 := runs_op0 (a := a) Rules.copy true h σ (by simp [hs]) (by simp [hd]) [x]
      (by simp [hs, WTape.cur, Rules.output_copy]) (fun _ => ⟨by simp [hd], by simp⟩)
    have ih := runs_joinLoop h ws (Function.update (Function.update σ src (σ src).next) dst
        ((σ dst).put true [x])) (x :: Ls) (acc ++ x) (fun y hy => hW y (by simp [hy]))
      (by simp [Function.update_of_ne h, hs, WTape.next, WTape.cur])
      (by simp [hd, WTape.put])
    refine (Runs.loop_step (by simp [hs]) (s1.mono (fun σ' e => by rw [e]; exact ih) le_rfl)).mono
      (fun σ' e => ?_) ?_
    · rw [e]; funext y
      by_cases a1 : y = src <;> by_cases a2 : y = dst <;> simp_all
    · have t1 := time_le Rules.copy x (fun j => j.elim0) 0 (fun j => j.elim0)
      simp only [hs, WTape.cur, List.headD_cons, List.length_cons] at t1 ⊢
      nlinarith

/-! ### Arrays and words on four tapes -/

theorem clen_eq (L : List (List Bool)) : clen L = L.flatten.length + L.length := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [ih]; ring

theorem clen_map_reverse (L : List (List Bool)) : clen (L.map List.reverse) = clen L := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [ih]

/-- Tape `0`: the array; tape `1`: the width in unary; tape `2`: the words; tape `3`: scratch. -/
noncomputable def toWords : Cmd a 4 :=
  .seq (chunkw 0 1 3 (by decide) (by decide) (by decide)) <| .seq (rewind 3) <|
  .seq (revLoop 3 2 (by decide)) <| .seq (rewind 2) <| .seq (clear 3) (rewind 0)

/-- `toWords` with pieces of length at most `W`. -/
theorem runs_toWordsW {w W : ℕ} (hw : 1 ≤ w) (A : List Bool) (hle : ∀ x ∈ cut w A, x.length ≤ W)
    (σ : Fin 4 → WTape)
    (h0 : σ 0 = reg A) (h1 : σ 1 = reg (ones w)) (h2 : σ 2 = emp) (h3 : σ 3 = emp) :
    Runs (a := a) toWords σ (· = Function.update σ 2 ⟨[], (cut w A).map List.reverse⟩)
      (30 * A.length + 20 * (cut w A).length * (W + 1) + 60) := by
  have hcl : clen (cut w A) = A.length + (cut w A).length := by rw [clen_eq, cut_flatten]
  have s1 := runs_chunkw (a := a) (s := 0) (r := 1) (d := 3) (by decide) (by decide) (by decide) σ
    (L := []) (R := []) (x := A) (by rw [h0]; rfl) h1 hw (by simp [h3, emp])
  set σ₁ := Function.update (Function.update σ 0 ⟨[A], []⟩) 3 ⟨(cut w A).reverse ++ (σ 3).left, []⟩
  have s2 := runs_rewind (a := a) 3 σ₁
  set σ₂ := Function.update σ₁ 3 ⟨[], (σ₁ 3).left.reverse ++ (σ₁ 3).right⟩
  have s3 := runs_revLoop (a := a) (show (3 : Fin 4) ≠ 2 by decide) (W := W) (cut w A) σ₂ [] []
    hle (by simp [σ₂, σ₁, h3, emp]) (by simp [σ₂, σ₁, h2, emp])
  set σ₃ := Function.update (Function.update σ₂ 3 ⟨(cut w A).reverse ++ [], []⟩) 2
    ⟨((cut w A).map List.reverse).reverse ++ [], []⟩
  have s4 := runs_rewind (a := a) 2 σ₃
  set σ₄ := Function.update σ₃ 2 ⟨[], (σ₃ 2).left.reverse ++ (σ₃ 2).right⟩
  have s5 := runs_clear (a := a) 3 σ₄
  set σ₅ := Function.update σ₄ 3 ⟨[], []⟩
  have s6 := runs_rewind (a := a) 0 σ₅
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun σ' e => ?_) ?_
  · rw [e]; funext y
    fin_cases y <;> simp [σ₅, σ₄, σ₃, σ₂, σ₁, h0, h1, h3, emp, reg]
  · simp only [σ₅, σ₄, σ₃, σ₂, σ₁, Function.update_self, Function.update_of_ne (show (3 : Fin 4) ≠ 2 by decide),
      Function.update_of_ne (show (0 : Fin 4) ≠ 3 by decide), Function.update_of_ne (show (0 : Fin 4) ≠ 2 by decide),
      h3, emp, WTape.words, List.append_nil, clen_reverse, clen_map_reverse, hcl, clen_cons, clen_nil]
    nlinarith


theorem runs_toWords {w : ℕ} (hw : 1 ≤ w) (A : List Bool) (σ : Fin 4 → WTape)
    (h0 : σ 0 = reg A) (h1 : σ 1 = reg (ones w)) (h2 : σ 2 = emp) (h3 : σ 3 = emp) :
    Runs (a := a) toWords σ (· = Function.update σ 2 ⟨[], (cut w A).map List.reverse⟩)
      (30 * A.length + 20 * (cut w A).length * (A.length + 1) + 60) :=
  runs_toWordsW hw A (fun x hx => by
    have := List.Sublist.length_le (List.sublist_flatten_of_mem hx)
    rwa [cut_flatten] at this) σ h0 h1 h2 h3

/-- Reverse the words on tape `2` and join them into one array on tape `0`. -/
noncomputable def fromWords : Cmd a 4 :=
  .seq (revLoop 2 3 (by decide)) <| .seq (rewind 3) <| .seq (emit [[]] 0) <|
  .seq (joinLoop 3 0 (by decide)) <| .seq (rewind 0) <| .seq (clear 2) (clear 3)

theorem runs_fromWords {W : ℕ} (ws : List (List Bool)) (hW : ∀ x ∈ ws, x.length ≤ W) (σ : Fin 4 → WTape)
    (h0 : σ 0 = emp) (h2 : σ 2 = ⟨[], ws⟩) (h3 : σ 3 = emp) :
    Runs (a := a) fromWords σ (· = Function.update (Function.update σ 0 (reg (ws.map List.reverse).flatten)) 2 emp)
      (ws.length * (8 * W + 40) + 10 * clen ws + 30) := by
  have s1 := runs_revLoop (a := a) (show (2 : Fin 4) ≠ 3 by decide) ws σ [] [] hW h2 (by rw [h3]; rfl)
  set σ₁ := Function.update (Function.update σ 2 ⟨ws.reverse ++ [], []⟩) 3
    ⟨(ws.map List.reverse).reverse ++ [], []⟩
  have s2 := runs_rewind (a := a) 3 σ₁
  set σ₂ := Function.update σ₁ 3 ⟨[], (σ₁ 3).left.reverse ++ (σ₁ 3).right⟩
  have s3 := runs_emit (a := a) [[]] 0 σ₂ (by simp [σ₂, σ₁, h0, emp])
  set σ₃ := Function.update σ₂ 0 ⟨[[]].reverse ++ (σ₂ 0).left, []⟩
  have hW' : ∀ x ∈ ws.map List.reverse, x.length ≤ W := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; simpa using hW y hy
  have s4 := runs_joinLoop (a := a) (show (3 : Fin 4) ≠ 0 by decide) (ws.map List.reverse) σ₃ [] []
    hW' (by simp [σ₃, σ₂, σ₁]) (by simp [σ₃, σ₂, σ₁, h0, emp])
  set σ₄ := Function.update (Function.update σ₃ 3 ⟨(ws.map List.reverse).reverse ++ [], []⟩) 0
    ⟨[[] ++ (ws.map List.reverse).flatten], []⟩
  have s5 := runs_rewind (a := a) 0 σ₄
  set σ₅ := Function.update σ₄ 0 ⟨[], (σ₄ 0).left.reverse ++ (σ₄ 0).right⟩
  have s6 := runs_clear (a := a) 2 σ₅
  set σ₆ := Function.update σ₅ 2 ⟨[], []⟩
  have s7 := runs_clear (a := a) 3 σ₆
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 s7)))))).mono
    (fun σ' e => ?_) ?_
  · rw [e]; funext y
    fin_cases y <;> simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, h3, emp, reg]
  · have hf : (ws.map List.reverse).flatten.length + ws.length = clen ws := by
      have := clen_eq (ws.map List.reverse); rw [clen_map_reverse] at this; simp at this ⊢; omega
    simp only [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, Function.update_self, Function.update_of_ne (show (3 : Fin 4) ≠ 2 by decide),
      Function.update_of_ne (show (2 : Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3 : Fin 4) ≠ 0 by decide),
      Function.update_of_ne (show (2 : Fin 4) ≠ 3 by decide),
      WTape.words, List.append_nil, clen_reverse, clen_map_reverse, clen_cons, clen_nil, List.length_map,
      List.nil_append, List.reverse_cons, List.reverse_nil, List.length_nil]
    nlinarith

end IntegerMultBounds.Schoenhage
