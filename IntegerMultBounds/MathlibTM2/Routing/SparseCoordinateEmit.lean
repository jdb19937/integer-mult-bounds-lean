module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWrite

/-! Compute a compact gap from live target and cursor coordinates, serialize
it with a live selector, and clear the temporary gap. No dense table is supplied.
All input words and scratch are restored; only the accumulating stream changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseCoordinateEmitProgram (target cursor gap entry dst tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bsub target cursor gap tx ty tz cy)
    (.seq (configurationWrite dst tx ty [gap, entry]) (bclear gap))

theorem sparseCoordinateEmit_exec (body : P → Pr P T Q A U)
    (target cursor gap entry dst tx ty tz cy : Fin T)
    (hregs : [target, cursor, gap, entry, dst, tx, ty, tz].Nodup)
    (hcyTarget : cy ≠ target) (hcyCursor : cy ≠ cursor)
    (L Ls x y q : ℕ) (hx : x < 2 ^ L) (hyx : y ≤ x)
    (v : HS T Q A U) (S : Stacks T A)
    (htarget : S.R target = binSyms L x) (hcursor : S.R cursor = binSyms L y)
    (hentry : S.R entry = binSyms Ls q) (hgap : S.R gap = [])
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseCoordinateEmitProgram target cursor gap entry dst tx ty tz cy)
        (mk v S) (16 * L + 6 * Ls + 25)
        (mk v' { S with R := Function.update S.R dst (binSyms L (x - y) ++ separator :: (binSyms Ls q ++ separator :: S.R dst)) }) := by
  have hn := hregs
  regs_ne hn
  have hy : y < 2 ^ L := lt_of_le_of_lt hyx hx
  have hsub : (x + 2 ^ L - y) % 2 ^ L = x - y := by
    have he : x + 2 ^ L - y = (x - y) + 2 ^ L := by omega
    rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (by omega : x - y < 2 ^ L)]
  obtain ⟨v₁, hu₁, _, _, he₁⟩ := bsub_exec body (a := target) (b := cursor) (c := gap)
    (tx := tx) (ty := ty) (tz := tz) (cy := cy) (by regs_nodup) hcyTarget hcyCursor hx hy v S htarget hcursor htx hty htz
  rw [hsub, hgap, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R gap (binSyms L (x - y)) }
  obtain ⟨v₂, hu₂, he₂⟩ := configurationWrite_exec body dst tx ty (by regs_nodup) [gap, entry]
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> exact ⟨by assumption, by assumption, by assumption⟩)
    v₁ S₁ (by simp [S₁, Ne.symm ‹gap ≠ tx›, htx]) (by simp [S₁, Ne.symm ‹gap ≠ ty›, hty])
  have hg₁ : S₁.R gap = binSyms L (x - y) := by simp [S₁]
  have he₁' : S₁.R entry = binSyms Ls q := by simp [S₁, Ne.symm ‹gap ≠ entry›, hentry]
  have hd₁ : S₁.R dst = S.R dst := by simp [S₁, Ne.symm ‹gap ≠ dst›]
  simp only [configurationWriteCost, List.map_cons, List.map_nil, configurationWords, hg₁, he₁', hd₁, length_binSyms] at he₂
  simp only [List.append_assoc, List.cons_append, List.nil_append] at he₂
  let out := binSyms L (x - y) ++ separator :: (binSyms Ls q ++ separator :: S.R dst)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst out }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body gap v₂ S₂
  have hg₂ : S₂.R gap = binSyms L (x - y) := by simp [S₂, S₁, ‹gap ≠ dst›]
  have hf : Function.update S₂.R gap [] = Function.update S.R dst out := by
    funext j
    by_cases hg : j = gap
    · subst j; simp [‹gap ≠ dst›, hgap]
    · by_cases hd : j = dst
      · subst j; simp [S₂, S₁, hg]
      · simp [S₂, S₁, hg, hd]
  rw [hf, hg₂, length_binSyms] at he₃
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
