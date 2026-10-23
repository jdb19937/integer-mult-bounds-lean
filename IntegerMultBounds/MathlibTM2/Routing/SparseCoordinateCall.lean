module

public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoad
public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateStep
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! One streamed coordinate iteration. Target/selector frames are archived,
the gap is computed, the cursor advanced, and loaded operands erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive SparseCoordinateReg where
  | src | archive | target | entry | loadTmp | cursor | gap | one | dst | tx | ty | tz
  deriving DecidableEq

variable {T Q A : ℕ} {P U : Type}

def sparseCoordinateCallProgram (rg : SparseCoordinateReg → Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram (rg .src) (rg .archive) (rg .target) (rg .entry) (rg .loadTmp))
    (.seq (sparseCoordinateStepProgram (rg .target) (rg .cursor) (rg .gap) (rg .entry) (rg .one)
      (rg .dst) (rg .tx) (rg .ty) (rg .tz) (rg .gap)) (metadataClean [rg .target, rg .entry]))

def sparseCoordinateCallBank (R : Fin T → List (Fin (A + 4))) (rg : SparseCoordinateReg → Fin T)
    (L Ls x y q : ℕ) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update (Function.update R (rg .src) rest)
    (rg .archive) ((binSyms L x ++ separator :: (binSyms Ls q ++ [separator])).reverse ++ R (rg .archive)))
    (rg .dst) (binSyms L (x - y) ++ separator :: (binSyms Ls q ++ separator :: R (rg .dst))))
    (rg .cursor) (binSyms L (x + 1))

theorem sparseCoordinateCall_exec (body : P → Pr P T Q A U)
    (rg : SparseCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L Ls x y q : ℕ) (hx : x + 1 < 2 ^ L) (hyx : y ≤ x)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = binSyms L x ++ separator :: (binSyms Ls q ++ separator :: rest))
    (hcursor : S.R (rg .cursor) = binSyms L y) (hone : S.R (rg .one) = binSyms L 1)
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseCoordinateCallProgram rg) (mk v S) (32 * L + 12 * Ls + 52)
        (mk v' { S with R := sparseCoordinateCallBank S.R rg L Ls x y q rest }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := selectorRunLoad_exec body (rg .src) (rg .archive) (rg .target) (rg .entry) (rg .loadTmp)
    (by simp [List.nodup_cons, hrg.eq_iff]) L Ls x q rest v S hsrc
    (hblank _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (hblank _ (by decide) (by decide) (by decide) (by decide) (by decide))
  let S₁ : Stacks T A := { S with R := selectorRunLoaded S.R (rg .src) (rg .archive) (rg .target) (rg .entry) (binSyms L x) (binSyms Ls q) rest }
  have hk (r : SparseCoordinateReg) (hs : r ≠ .src) (ha : r ≠ .archive) (ht : r ≠ .target) (he : r ≠ .entry) :
      S₁.R (rg r) = S.R (rg r) := by simp [S₁, selectorRunLoaded, hrg.eq_iff, hs, ha, ht, he]
  have hb (r : SparseCoordinateReg) (hs : r ≠ .src) (ha : r ≠ .archive) (ht : r ≠ .target) (he : r ≠ .entry)
      (hc : r ≠ .cursor) (ho : r ≠ .one) (hd : r ≠ .dst) : S₁.R (rg r) = [] :=
    (hk r hs ha ht he).trans (hblank r hs ha hc ho hd)
  obtain ⟨v₂, hu₂, he₂⟩ := sparseCoordinateStep_exec body (rg .target) (rg .cursor) (rg .gap) (rg .entry)
    (rg .one) (rg .dst) (rg .tx) (rg .ty) (rg .tz) (rg .gap)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L Ls x y q hx hyx v₁ S₁
    (by simp [S₁, selectorRunLoaded, hrg.eq_iff])
    ((hk .cursor (by decide) (by decide) (by decide) (by decide)).trans hcursor)
    (by simp [S₁, selectorRunLoaded])
    ((hk .one (by decide) (by decide) (by decide) (by decide)).trans hone)
    (hb _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  let out := binSyms L (x - y) ++ separator :: (binSyms Ls q ++ separator :: S₁.R (rg .dst))
  let S₂ : Stacks T A := { S₁ with R := Function.update (Function.update S₁.R (rg .dst) out) (rg .cursor) (binSyms L (x + 1)) }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body [rg .target, rg .entry] (by simp [hrg.eq_iff]) v₂ S₂
  have hc : metadataCleanCost S₂.R [rg .target, rg .entry] = 2 * L + 2 * Ls + 5 := by
    simp [metadataCleanCost, S₂, S₁, selectorRunLoaded, hrg.eq_iff]; omega
  have hf : metadataCleared S₂.R [rg .target, rg .entry] = sparseCoordinateCallBank S.R rg L Ls x y q rest := by
    funext j
    by_cases ht : j = rg .target
    · subst j; simp [metadataCleared, sparseCoordinateCallBank, hrg.eq_iff, hblank]
    · by_cases he : j = rg .entry
      · subst j; simp [metadataCleared, sparseCoordinateCallBank, hrg.eq_iff, hblank]
      · by_cases hc : j = rg .cursor
        · subst j; simp [metadataCleared, sparseCoordinateCallBank, S₂, hrg.eq_iff]
        · by_cases hd : j = rg .dst
          · subst j; simp [metadataCleared, sparseCoordinateCallBank, S₂, out, S₁, selectorRunLoaded, hrg.eq_iff]
          · simp [metadataCleared, sparseCoordinateCallBank, S₂, S₁, selectorRunLoaded, ht, he, hc, hd]
  rw [hc, hf] at he₃
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
