module

public import IntegerMultBounds.MathlibTM2.Host.BinArithMul
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalExec

/-!
# Uniform canonical generation of three times a binary input

Putting the two-bit constant in the multiplier's first operand keeps the cost
linear in input width. Constant setup, multiplication, clearing and normalization
all execute; the original input and every scratch stack are restored.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryTripleProgram (src dst three s t tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt three) (fun _ => bitSymbol true)
    (.push (.rt three) (fun _ => bitSymbol true) .done)))
    (.seq (bmul three src dst s t tx ty tz cy)
      (.seq (bclear three) (binaryCanonicalProgram dst t)))

/-- Produce a canonical triple with a uniform program and linear width cost. -/
theorem binaryTriple_exec (body : P → Pr P T Q A U) (src dst three s t tx ty tz cy : Fin T)
    (hreg : [three, src, dst, s, t, tx, ty, tz].Nodup) (hcd : cy ≠ dst) (hcs : cy ≠ s)
    (L x : ℕ) (hx : x < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms L x)
    (hthree : S.R three = []) (hdst : S.R dst = []) (hs : S.R s = []) (ht : S.R t = [])
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (bs : List Bool) (v' : HS T Q A U) (m : ℕ), GrowingCounterData.Canonical bs ∧
      Counter.value bs = 3 * x ∧ bs.length ≤ L + 2 ∧ v'.user = v.user ∧ m ≤ 44 * L + 165 ∧
      Exec body (binaryTripleProgram src dst three s t tx ty tz cy) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (bs.map bitSymbol) }) := by
  have hn := hreg
  regs_ne hn
  let S₁ : Stacks T A := { S with R := Function.update S.R three [bitSymbol true, bitSymbol true] }
  have hpush : (Action.push (.rt three) (fun _ => bitSymbol true)
      (.push (.rt three) (fun _ => bitSymbol true) .done) : Act T Q A U).run (mk v S) = mk v S₁ := by
    simp [Action.run, update_rt, hthree, S₁]
  have hkeep (j : Fin T) (hj : j ≠ three) : S₁.R j = S.R j := Function.update_of_ne hj _ _
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := bmul_exec body hreg hcd hcs (by decide : 3 < 2 ^ 2) hx v S₁
    (by simp only [S₁, Function.update_self]; rfl)
    (by rw [hkeep src (Ne.symm ‹three ≠ src›)]; exact hsrc)
    (by rw [hkeep dst (Ne.symm ‹three ≠ dst›)]; exact hdst)
    (by rw [hkeep s (Ne.symm ‹three ≠ s›)]; exact hs)
    (by rw [hkeep t (Ne.symm ‹three ≠ t›)]; exact ht)
    (by rw [hkeep tx (Ne.symm ‹three ≠ tx›)]; exact htx)
    (by rw [hkeep ty (Ne.symm ‹three ≠ ty›)]; exact hty)
    (by rw [hkeep tz (Ne.symm ‹three ≠ tz›)]; exact htz)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (binSyms (2 + L) (3 * x)) }
  have hthree₂ : S₂.R three = [bitSymbol true, bitSymbol true] := by simp [S₂, S₁, ‹three ≠ dst›]
  obtain ⟨v₂, hu₂, _, he₂⟩ := bclear_exec body three v₁ S₂
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R three [] }
  have hfit : 3 * x < 2 ^ (2 + L) := by
    rw [pow_add]
    norm_num
    omega
  have hdst₃ : S₃.R dst = binSyms (2 + L) (3 * x) := by simp [S₃, S₂, Ne.symm ‹three ≠ dst›]
  have ht₃ : S₃.R t = [] := by simp [S₃, S₂, S₁, Ne.symm ‹three ≠ t›, Ne.symm ‹dst ≠ t›, ht]
  obtain ⟨bs, v₃, hc, hv, hl, hu₃, he₃⟩ := binaryCanonical_exec body dst t ‹dst ≠ t›
    (2 + L) (3 * x) hfit v₂ S₃ hdst₃ ht₃
  have hfinal : Function.update S₃.R dst (bs.map bitSymbol) = Function.update S.R dst (bs.map bitSymbol) := by
    funext j
    by_cases hj : j = dst
    · subst j; simp
    · by_cases hk : j = three
      · subst j; simp [S₃, hj, hthree]
      · simp [S₃, S₂, S₁, hj, hk]
  refine ⟨bs, v₃, 1 + (m₁ + ((2 * (S₂.R three).length + 2) + (4 * (2 + L) + 6))),
    hc, hv, by omega, hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [hthree₂]
    simp only [List.length_cons, List.length_nil]
    omega
  · refine Exec.cast (Exec.seq (hpush ▸ Exec.act (body := body) _ (mk v S))
      (Exec.seq he₁ (Exec.seq he₂ he₃))) rfl ?_
    simp only [hfinal]
    rfl

end IntegerMultBounds.MathlibTM2.Routing
