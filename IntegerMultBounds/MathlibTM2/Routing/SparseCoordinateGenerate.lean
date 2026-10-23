module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateCompile
public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorRestore

/-! Generate compact gaps from absolute coordinates, restore the complete input
and original cursor, and erase its saved copy. Only compact output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseCoordinateGenerateProgram (rg : SparseCoordinateReg → Fin T) (saved : Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg .cursor) saved (rg .tx) (rg .ty))
    (.seq (sparseCoordinateCompileProgram rg) (sparseCursorRestoreProgram (rg .cursor) saved (rg .tx) (rg .ty)))

theorem sparseCoordinateGenerate_exec (body : P → Pr P T Q A U)
    (rg : SparseCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (L Ls cursor : ℕ) (entries : List (ℕ × ℕ)) (hready : SparseCoordinatesReady L cursor entries)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = sparseCoordinateFrames L Ls entries) (harchive : S.R (rg .archive) = [])
    (hcursor : S.R (rg .cursor) = binSyms L cursor) (hone : S.R (rg .one) = binSyms L 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseCoordinateGenerateProgram rg saved) (mk v S)
        (entries.length * (32 * L + 12 * Ls + 54) + 2 * (sparseCoordinateFrames (A := A) L Ls entries).length + 16 * L + 20)
        (mk v' { S with R := Function.update S.R (rg .dst) (sparseCoordinateOutput L Ls cursor entries ++ S.R (rg .dst)) }) := by
  have ht := hblank .tx (by decide) (by decide) (by decide) (by decide) (by decide)
  have hw := hblank .ty (by decide) (by decide) (by decide) (by decide) (by decide)
  have hregs : [rg .cursor, saved, rg .tx, rg .ty].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff, hsep, Ne.symm (hsep .cursor)]
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body hregs v S ht hw
  rw [hcursor, hsaved, List.append_nil, length_binSyms] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R saved (binSyms L cursor) }
  have hk (r : SparseCoordinateReg) : S₁.R (rg r) = S.R (rg r) := Function.update_of_ne (hsep r).symm _ _
  obtain ⟨v₂, hu₂, he₂⟩ := sparseCoordinateCompile_exec body rg hrg L Ls cursor entries hready v₁ S₁
    ((hk .src).trans hsrc) ((hk .archive).trans harchive) ((hk .cursor).trans hcursor) ((hk .one).trans hone)
    (by intro r hs ha hc ho hd; rw [hk]; exact hblank r hs ha hc ho hd)
  have hd : S₁.R (rg .dst) = S.R (rg .dst) := hk .dst
  rw [hd] at he₂
  let out := sparseCoordinateOutput (A := A) L Ls cursor entries ++ S.R (rg .dst)
  let S₂ : Stacks T A := { S₁ with R := Function.update (Function.update S₁.R (rg .dst) out) (rg .cursor) (binSyms L (sparseCoordinateEnd cursor entries)) }
  obtain ⟨v₃, hu₃, he₃⟩ := sparseCursorRestore_exec body (rg .cursor) saved (rg .tx) (rg .ty) hregs
    L (sparseCoordinateEnd cursor entries) cursor v₂ S₂
    (by simp [S₂]) (by simp [S₂, S₁, hsep])
    (by simp [S₂, S₁, (hsep .tx).symm, hrg.eq_iff, ht]) (by simp [S₂, S₁, (hsep .ty).symm, hrg.eq_iff, hw])
  have hf : Function.update (Function.update S₂.R (rg .cursor) (binSyms L cursor)) saved [] =
      Function.update S.R (rg .dst) out := by
    funext j
    by_cases hs : j = saved
    · subst j; simp [hsep, hsaved]
    · by_cases hc : j = rg .cursor
      · subst j; simp [hs, hrg.eq_iff, hcursor]
      · by_cases hd : j = rg .dst
        · subst j; simp [S₂, S₁, hs, hc]
        · simp [S₂, S₁, hs, hc, hd]
  rw [hf] at he₃
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
