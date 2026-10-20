module
public import IntegerMultBounds.Schoenhage.Ops
public import IntegerMultBounds.MathlibTM2.Host.WordCopy
public import IntegerMultBounds.Schoenhage.Rules


/-! Cutting a word into pieces of a fixed width, as a primitive (`Chunk.prim`, `chunkw`; host
program `chunkHProg`): the source advances one word and the destination gains the pieces
`cut w x` of the width held in unary by the register (`runs_chunkw`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a t : ℕ}

theorem cells_cons (c : List Bool) (cs : List (List Bool)) :
    cells (a := a) (c :: cs) = c.map bitSymbol ++ [separator] ++ cells cs := by
  simp [cells, syms_cons, sym, Function.comp_def]

namespace Chunk

/-- Chunk: the source's current word, cut into pieces of the register's width, as new words of
the destination. -/
noncomputable abbrev prim : Prim a where
  s := 3
  pre σ := (σ 0).right ≠ [] ∧ 1 ≤ (σ 1).cur.length ∧ σ 1 = reg (ones (σ 1).cur.length) ∧ (σ 2).right = []
  sem σ := fun i => if i.val = 0 then (σ 0).next else if i.val = 1 then σ 1
    else ⟨(cut (σ 1).cur.length (σ 0).cur).reverse ++ (σ 2).left, []⟩
  cost σ := 4 * (σ 0).cur.length + 3
  nQ := 0
  prog := MathlibTM2.Host.WordCmd.chunkHProg
  hspec := MathlibTM2.Host.WordCmd.chunk_hostSpec
  hcalls := MathlibTM2.Host.WordCmd.chunkHProg_noCalls

end Chunk

/-- Three slots: source, width register, destination. -/
def slot3 (s r d : Fin t) : Fin 3 → Fin t := fun i => if i.val = 0 then s else if i.val = 1 then r else d

theorem slot3_inj {s r d : Fin t} (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d) : Function.Injective (slot3 s r d) := by
  intro i j hij
  simp only [slot3] at hij
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt
  split_ifs at hij <;> omega

/-- Cut the current word of `s` into pieces of the width in `r`, appended to `d`. -/
noncomputable def chunkw (s r d : Fin t) (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d) : Cmd a t :=
  .prim Chunk.prim (slot3 s r d) (slot3_inj h1 h2 h3)

theorem upd_slot3 (σ : Fin t → WTape) {s r d : Fin t} (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d)
    (τ : Fin 3 → WTape) :
    upd σ (slot3 s r d) τ = Function.update (Function.update (Function.update σ s (τ 0)) r (τ 1)) d (τ 2) := by
  have hi := slot3_inj h1 h2 h3
  funext x
  by_cases hxd : x = d
  · subst hxd
    rw [Function.update_self]
    have := upd_slot σ hi τ 2
    rwa [show slot3 s r x 2 = x by simp [slot3]] at this
  · rw [Function.update_of_ne hxd]
    by_cases hxr : x = r
    · subst hxr
      rw [Function.update_self]
      have := upd_slot σ hi τ 1
      rwa [show slot3 s x d 1 = x by simp [slot3]] at this
    · rw [Function.update_of_ne hxr]
      by_cases hxs : x = s
      · subst hxs
        rw [Function.update_self]
        have := upd_slot σ hi τ 0
        rwa [show slot3 x r d 0 = x by simp [slot3]] at this
      · rw [Function.update_of_ne hxs]
        refine upd_other σ _ τ x (fun i hi => ?_)
        simp only [slot3] at hi; split_ifs at hi <;> simp_all

theorem runs_chunkw {s r d : Fin t} (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d) (σ : Fin t → WTape)
    {L R : List (List Bool)} {x : List Bool} {w : ℕ}
    (hs : σ s = ⟨L, x :: R⟩) (hr : σ r = reg (ones w)) (hw : 1 ≤ w) (hd : (σ d).right = []) :
    Runs (a := a) (chunkw s r d h1 h2 h3) σ
      (· = Function.update (Function.update σ s ⟨x :: L, R⟩) d ⟨(cut w x).reverse ++ (σ d).left, []⟩)
      (4 * x.length + 3) := by
  have ew : (σ r).cur.length = w := by rw [hr]; simp [WTape.cur, reg]
  have hpre : Chunk.prim.pre (a := a) (σ ∘ slot3 s r d) :=
    ⟨by simp [slot3, hs], by simp [slot3, ew, hw], by simp [slot3, hr], by simpa [slot3, h2.symm, h3.symm] using hd⟩
  refine ⟨_, _, Exec.prim (P := Chunk.prim) hpre, ?_, ?_⟩
  · rw [upd_slot3 σ h1 h2 h3]
    have c0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have c1 : ((1 : Fin 3) : ℕ) = 1 := rfl
    have c2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    simp only [slot3, Function.comp_apply, c0, c1, c2, ↓reduceIte, one_ne_zero, hs, WTape.next, WTape.cur,
      List.headD_cons, List.tail_cons, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide]
    rw [show (σ r).right.headD [] = ones w by rw [hr]; rfl, length_ones]
    funext y
    by_cases hy : y = d
    · subst hy; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hy, Function.update_of_ne hy]
      by_cases hy2 : y = r
      · subst hy2; rw [Function.update_self, Function.update_of_ne h1.symm]
      · rw [Function.update_of_ne hy2]
  · simp [slot3, hs, WTape.cur]

end IntegerMultBounds.Schoenhage
