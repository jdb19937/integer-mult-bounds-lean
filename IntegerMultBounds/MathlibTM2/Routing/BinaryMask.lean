module

public import IntegerMultBounds.MathlibTM2.Routing.UnaryComplement
public import IntegerMultBounds.MathlibTM2.Routing.SourceMask
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! A full-width one-hot descriptor row generated from two binary inputs.
Unary coordinates and padding are computed and cleared by the fixed program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive BinaryMaskReg where
  | width | source | low | high | dst | scratch (i : Fin 7)
  deriving DecidableEq

def binaryMaskProgram {T Q A : ℕ} {P U : Type} (rg : BinaryMaskReg → Fin T) : Pr P T Q A U :=
  .seq (toUnary (rg .source) (rg .low) (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)))
    (.seq (unaryComplementProgram (rg .width) (rg .source) (rg (.scratch 0)) (rg (.scratch 1))
      (rg .high) (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6)))
      (.seq (sourceMaskProgram (rg .low) (rg .high) (rg .dst) (rg (.scratch 3)) (rg (.scratch 4)))
        (metadataClean [rg .low, rg .high])))

theorem binSyms_oneHot {A M : ℕ} (q : Fin M) :
    binSyms (A := A) M (2 ^ q.val) = (List.ofFn (fun j : Fin M => decide (j = q))).map bitSymbol := by
  rw [binSyms_eq]
  congr 1
  unfold binBits
  congr 1
  funext j
  simp [Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

theorem binaryMask_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryMaskReg → Fin T) (hrg : Function.Injective rg)
    (L M : ℕ) (hM : M < 2 ^ L) (q : Fin M)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L M) (hsource : S.R (rg .source) = binSyms L q.val)
    (hlow : S.R (rg .low) = []) (hhigh : S.R (rg .high) = []) (hdst : S.R (rg .dst) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 2 * (L * (4 * M + 33) + 2 * M + 31) + 12 * M + 24 ∧
      Exec body (binaryMaskProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .dst) (binSyms M (2 ^ q.val)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body (a := rg .source) (z := rg .low)
    (w := rg (.scratch 2)) (t := rg (.scratch 3)) (t₂ := rg (.scratch 4))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by omega : q.val < 2 ^ L) v S hsource
    (hscratch 2) (hscratch 3) (hscratch 4)
  rw [hlow, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .low) (List.replicate q.val tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryComplement_exec body (rg .width) (rg .source)
    (rg (.scratch 0)) (rg (.scratch 1)) (rg .high) (rg (.scratch 2)) (rg (.scratch 3))
    (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L M q.val hM q.isLt v₁ S₁
    (by simp [S₁, hrg.eq_iff, hwidth]) (by simp [S₁, hrg.eq_iff, hsource])
    (by simp [S₁, hrg.eq_iff, hscratch]) (by simp [S₁, hrg.eq_iff, hscratch])
    (by simp [S₁, hrg.eq_iff, hhigh]) (by simp [S₁, hrg.eq_iff, hscratch])
    (by simp [S₁, hrg.eq_iff, hscratch]) (by simp [S₁, hrg.eq_iff, hscratch])
    (by simp [S₁, hrg.eq_iff, hscratch])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .high) (List.replicate (M - (q.val + 1)) tick) }
  obtain ⟨v₃, hu₃, he₃⟩ := sourceMask_exec body (rg .low) (rg .high) (rg .dst)
    (rg (.scratch 3)) (rg (.scratch 4)) (by simp [List.nodup_cons, hrg.eq_iff]) v₂ S₂
    (by simp [S₂, S₁, hrg.eq_iff, hdst]) (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
  have hlo₂ : S₂.R (rg .low) = List.replicate q.val tick := by simp [S₂, S₁, hrg.eq_iff]
  have hhi₂ : S₂.R (rg .high) = List.replicate (M - (q.val + 1)) tick := by simp [S₂]
  have hsize : (S₂.R (rg .low)).length + 1 + (S₂.R (rg .high)).length = M := by
    rw [hlo₂, hhi₂, List.length_replicate, List.length_replicate]
    omega
  rw [hsize] at he₃
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (rg .dst) (binSyms M (2 ^ q.val)) }
  have he₃' : Exec body (sourceMaskProgram (rg .low) (rg .high) (rg .dst) (rg (.scratch 3)) (rg (.scratch 4)))
      (mk v₂ S₂) (10 * q.val + 6 * (M - (q.val + 1)) + 19) (mk v₃ S₃) := by
    simpa only [hlo₂, hhi₂, List.length_replicate] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := metadataClean_exec body [rg .low, rg .high]
    (by simp [hrg.eq_iff]) v₃ S₃
  have hcost : metadataCleanCost S₃.R [rg .low, rg .high] = 2 * q.val + 2 * (M - (q.val + 1)) + 5 := by
    simp [metadataCleanCost, S₃, S₂, S₁, hrg.eq_iff]
    omega
  have hfinal : metadataCleared S₃.R [rg .low, rg .high] = Function.update S.R (rg .dst) (binSyms M (2 ^ q.val)) := by
    funext j
    by_cases hl : j = rg .low
    · subst j; simp [metadataCleared, hrg.eq_iff, hlow]
    · by_cases hh : j = rg .high
      · subst j; simp [metadataCleared, hrg.eq_iff, hhigh]
      · by_cases hd : j = rg .dst
        · subst j; simp [metadataCleared, S₃, hl, hh]
        · simp [metadataCleared, S₃, S₂, S₁, hl, hh, hd]
  rw [hcost, hfinal] at he₄
  refine ⟨v₄, m₁ + (m₂ + ((10 * q.val + 6 * (M - (q.val + 1)) + 19) +
    (2 * q.val + 2 * (M - (q.val + 1)) + 5))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))⟩
  have h₁ := Nat.mul_le_mul_left L (by omega : 4 * q.val + 11 ≤ 4 * M + 33)
  have h₂ := Nat.mul_le_mul_left L (by omega : 4 * (M - (q.val + 1)) + 33 ≤ 4 * M + 33)
  omega

end IntegerMultBounds.MathlibTM2.Routing
