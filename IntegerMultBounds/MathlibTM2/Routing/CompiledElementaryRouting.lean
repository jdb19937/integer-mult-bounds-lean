module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileTableCost
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopCost

/-!
# Compile a coordinate table, execute its routing, and clear generated metadata

Both programs are fixed. The raw coordinate table is restored by the compiler;
the generated instruction stream is restored by routing and then cleared.
Only the routed record stream changes in the complete register bank.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t₀ T Q K : ℕ} {P U : Type}

noncomputable def compiledElementaryProgram
    (compiler : ElementaryCompilerReg → Fin T) (src archive : Fin T)
    (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) (saved : Fin T) : Pr P T Q (prime + K) U :=
  .seq (elementaryCompileTableProgram compiler src archive)
    (.seq (elementaryRoutingProgram rg hrg hd pay hhd hQ hT (compiler .output) saved) (bclear (compiler .output)))

private theorem compiledElementary_cost (k C b f O F x y : ℝ)
    (hf : 0 ≤ f) (hx : x ≤ k * C + 4) (hy : y ≤ k * (b + 2) + f * O + 4) (ho : O ≤ k * F) :
    x + (y + (2 * O + 2)) ≤ k * (C + b + 2 + (f + 2) * F) + 10 := by
  have hz := mul_le_mul_of_nonneg_left ho (show 0 ≤ f + 2 by linarith)
  calc
    x + (y + (2 * O + 2)) ≤ k * C + 4 + (k * (b + 2) + f * O + 4) + (2 * O + 2) := by linarith
    _ = k * (C + b + 2) + (f + 2) * O + 10 := by ring
    _ ≤ k * (C + b + 2) + (f + 2) * (k * F) + 10 := by linarith only [hz]
    _ = k * (C + b + 2 + (f + 2) * F) + 10 := by ring

/-- Complete compiled routing from binary coordinate pairs; only shared scan
setup remains prepared at this layer. All generated metadata is cleared. -/
theorem compiledElementary_exec {n rows B : ℕ}
    (body : P → Pr P T Q (prime + K) U)
    (compiler : ElementaryCompilerReg → Fin T) (hcompiler : Function.Injective compiler)
    (src archive : Fin T) (hsa : src ≠ archive)
    (hsrc : ∀ r, src ≠ compiler r) (harchive : ∀ r, archive ≠ compiler r)
    (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ j, hd j ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) (saved : Fin T)
    (hcs : compiler .output ≠ saved) (hconfig : ∀ r, compiler .output ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L Lb : ℕ) (hn : n < 2 ^ L) (hBin : B < 2 ^ Lb) (hnB : n ≤ B) (hrows : 0 < rows) (hB : 1 ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows) (cs : List (ElementaryCoordinate n))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hcompileReady : ElementaryCompileReady compiler S.R n L Lb B rowBits)
    (hrouteReady : ElementaryLoopReady rg hd pay S.R n rows B) (hL : ∀ j, S.L j = [])
    (hinput : S.R src = elementaryCoordinateFrames L cs) (harchive0 : S.R archive = [])
    (hconfig0 : S.R (compiler .output) = []) (hsaved0 : S.R saved = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hstream : S.R (rg .str) = l.flatten) :
    ∃ (ds : List (ElementaryInstruction n)) (v' : HS T Q (prime + K) U) (m : ℕ),
      ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key ∧ v'.user = v.user ∧
      (m : ℝ) ≤ (cs.length : ℝ) *
        ((elementaryCompileBase n L Lb rowBits.length + 7 * (rowBits.length + 3 * n + Lb + 11) + 4 * L + 6 : ℕ) +
          elementaryBaseCost rg n rows B S + 2 +
          (12 * swapT t₀ + 22 : ℕ) * (rowBits.length + 3 * n + Lb + 11 : ℕ)) + 10 ∧
      Exec body (compiledElementaryProgram compiler src archive rg hrg hd pay hhd hQ hT saved) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) := by
  obtain ⟨ds, v₁, m₁, hv, hsize, hk, hu₁, hm₁, he₁⟩ := elementaryCompileTable_exec_le body compiler hcompiler src archive
    hsa hsrc harchive L Lb rows B hn hBin rowBits hrow hrowNe hrowValue cs v S hcompileReady hinput harchive0
  rw [hconfig0, List.append_nil] at he₁
  let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R (compiler .output) (elementaryFrames ds) }
  have hkeep (r : LayReg t₀) : S₁.R (rg r) = S.R (rg r) := Function.update_of_ne (hconfig r).symm _ _
  have hr₁ : ElementaryLoopReady rg hd pay S₁.R n rows B := hrouteReady.congr (fun r _ => hkeep r)
  have hs₁ : S₁.R saved = [] := by simp [S₁, hcs.symm, hsaved0]
  have ht₁ : S₁.R (rg .str) = l.flatten := (hkeep .str).trans hstream
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := elementaryRouting_exec_le body rg hrg hd pay hhd hpay hQ hT
    (compiler .output) saved hcs hconfig hsaved hrows hB hnB ds hv v₁ S₁ hL hr₁ hs₁ l hl hlB h8 ht₁ (by simp [S₁])
  let out := (moveRecs (elementaryInstructionsRank rows ds) l).flatten
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R (rg .str) out }
  have htable : S₂.R (compiler .output) = elementaryFrames ds := by simp [S₂, S₁, hconfig .str]
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (compiler .output) v₂ S₂
  have hfinal : Function.update S₂.R (compiler .output) [] = Function.update S.R (rg .str) out := by
    funext j
    by_cases hj : j = compiler .output
    · subst j; simp [hconfig .str, hconfig0]
    · by_cases hs : j = rg .str
      · subst j; simp [S₂, hj]
      · simp [S₂, S₁, hj, hs]
  have he₃' : Exec body (bclear (compiler .output)) (mk v₂ S₂)
      (2 * (elementaryFrames (A := prime + K) ds).length + 2)
      (mk v₃ { S with R := Function.update S.R (rg .str) out }) := by
    simpa only [htable, hfinal] using he₃
  have hlen := congrArg List.length hk
  simp only [List.length_map, List.length_reverse] at hlen
  have hf := elementaryFrames_length_le (A := prime + K) ds (rowBits.length + 3 * n + Lb + 11) hsize
  rw [hlen] at hf
  have hbase : elementaryBaseCost rg n rows B S₁ = elementaryBaseCost rg n rows B S := by
    unfold elementaryBaseCost
    simp only [hkeep]
  rw [hbase, hlen] at hm₂
  have hx : (m₁ : ℝ) ≤ (cs.length : ℝ) *
      (elementaryCompileBase n L Lb rowBits.length + 7 * (rowBits.length + 3 * n + Lb + 11) + 4 * L + 6 : ℕ) + 4 := by
    exact_mod_cast hm₁
  have ho : ((elementaryFrames (A := prime + K) ds).length : ℝ) ≤
      (cs.length : ℝ) * (rowBits.length + 3 * n + Lb + 11 : ℕ) := by exact_mod_cast hf
  refine ⟨ds, v₃, m₁ + (m₂ + (2 * (elementaryFrames (A := prime + K) ds).length + 2)), hk,
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃')⟩
  have h := compiledElementary_cost _ _ _ _ _ _ _ _ (by positivity) hx hm₂ ho
  have hcoeff : ((12 * swapT t₀ + 20 : ℕ) : ℝ) + 2 = ((12 * swapT t₀ + 22 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcoeff] at h
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

end IntegerMultBounds.MathlibTM2.Routing
