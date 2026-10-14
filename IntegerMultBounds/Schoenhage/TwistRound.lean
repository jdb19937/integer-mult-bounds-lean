module

public import IntegerMultBounds.Schoenhage.TwistArray
public import IntegerMultBounds.Schoenhage.DifOpposite

/-! The twist of a §6 round on a whole record array. The rounds twist the
record at physical address `y` by `y^(-e y)` (`twist e`); the record monomial
`twistRec E` multiplies by `y^E`, so the round uses `E = twistExp r (e y)`, the
residue of `-e y` modulo `2r` (`gridPoly_twistRec_exp`). On the record list,
twisting every record by its exponent is the array twist (`arrayVec_twist`),
and the untwist of an opposite round uses `E = e y mod 2r`
(`arrayVec_untwist`). With the four descriptor lists of these exponents,
`TwistArray.twistArray` therefore applies the round's twist to the whole
array within `O(M r w)` steps (`runs_twistRound`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct NLogN

namespace TwistRound

variable {r : ℕ} [NeZero r]

/-- The record exponent of the twist by `y^(-e)`: the residue of `-e` modulo `2r`. -/
def twistExp (r e : ℕ) : ℕ := (2 * r - e % (2 * r)) % (2 * r)

theorem gridPoly_twistRec_exp (p e : ℕ) (f : Rec r) :
    gridPoly p (twistRec (twistExp r e) f).1 (twistRec (twistExp r e) f).2 = shiftInv e (gridPoly p f.1 f.2) := by
  rw [gridPoly_twistRec]; rfl

theorem shiftInv_zero_vec (e : ℕ) : shiftInv e (0 : Fin r → ℂ) = 0 := by
  rw [shiftInv_clm, map_zero]

/-- The records twisted by their exponents. -/
def twistRecs (f : ℕ → ℕ) (fs : List (Rec r)) : List (Rec r) :=
  fs.mapIdx fun y g => twistRec (twistExp r (f y)) g

/-- `arrayVec_twist`: twisting every record by `y^(-f y)` is the array twist `twist f`. -/
theorem arrayVec_twist (p : ℕ) (f : ℕ → ℕ) (fs : List (Rec r)) :
    arrayVec p (twistRecs f fs) = twist f (arrayVec p fs) := by
  funext y
  simp only [twist, arrayVec, twistRecs, List.getElem?_mapIdx]
  cases h : fs[y]? with
  | none => simp [shiftInv_zero_vec]
  | some g => simp [gridPoly_twistRec_exp]

/-- The records multiplied by `y^(f y)`, the inverse monomial of an opposite round. -/
def untwistRecs (f : ℕ → ℕ) (fs : List (Rec r)) : List (Rec r) :=
  fs.mapIdx fun y g => twistRec (f y % (2 * r)) g

/-- `arrayVec_untwist`: multiplying every record by `y^(f y)` is the array untwist `untwist f`. -/
theorem arrayVec_untwist (p : ℕ) (f : ℕ → ℕ) (fs : List (Rec r)) :
    arrayVec p (untwistRecs f fs) = untwist f (arrayVec p fs) := by
  funext y
  simp only [untwist, arrayVec, untwistRecs, List.getElem?_mapIdx]
  cases h : fs[y]? with
  | none => simp [shiftNegZ_zero_vec]
  | some g => simp [gridPoly_twistRec, ← shiftNegZ_mod]

open TwistArray in
/-- `runs_twistRound`: with the descriptor lists of the exponents `twistExp r (f y)` of the
records in order, the array monomial outputs the records of the array twist `twist f`, in
`O(M r w)` steps for `M` records. -/
theorem runs_twistRound (w : ℕ) (f : ℕ → ℕ) (fs : List (Rec r)) (τ : Fin 15 → WTape)
    (Lx R Lh Lt Lf Lg D : List (List Bool)) (hI : Idle r τ)
    (hX : τ xX = ⟨Lx, arrWords w fs ++ R⟩) (hO : τ xO = ⟨D, []⟩)
    (hH : τ dH = ⟨Lh, (List.range fs.length).map fun y => hdW r (twistExp r (f y))⟩)
    (hT : τ dT = ⟨Lt, (List.range fs.length).map fun y => tlW r (twistExp r (f y))⟩)
    (hF : τ dF = ⟨Lf, (List.range fs.length).map fun y => hfW r (twistExp r (f y))⟩)
    (hG : τ dG = ⟨Lg, (List.range fs.length).map fun y => tfW r (twistExp r (f y))⟩) :
    ∃ gs : List (Rec r), arrayVec p gs = twist f (arrayVec p fs) ∧ gs.length = fs.length ∧
      Runs twistArray τ (fun τ' => τ' xO = ⟨(arrWords w gs).reverse ++ D, []⟩)
        (fs.length * (2 * r * (25 * w + 200) + 50 * r + 402)) := by
  set ps : List (ℕ × Rec r) := fs.mapIdx fun y g => (twistExp r (f y), g)
  have hsnd : ps.map Prod.snd = fs := by
    apply List.ext_getElem (by simp [ps]); intro n h1 h2; simp [ps]
  have hdesc : ∀ (q : ℕ → List Bool), ps.map (fun p => q p.1) =
      (List.range fs.length).map fun y => q (twistExp r (f y)) := by
    intro q; apply List.ext_getElem (by simp [ps]); intro n h1 h2; simp [ps]
  have htw : ps.map (fun p => twistRec p.1 p.2) = twistRecs f fs := by
    apply List.ext_getElem (by simp [ps, twistRecs]); intro n h1 h2; simp [ps, twistRecs]
  have hrun := runs_twistArray w ps τ Lx R Lh Lt Lf Lg D hI (by rw [hsnd]; exact hX) hO
    (by rw [hdesc (hdW r)]; exact hH) (by rw [hdesc (tlW r)]; exact hT)
    (by rw [hdesc (hfW r)]; exact hF) (by rw [hdesc (tfW r)]; exact hG)
  have hlen : ps.length = fs.length := by simp [ps]
  refine ⟨twistRecs f fs, arrayVec_twist p f fs, by simp [twistRecs], ?_⟩
  rw [hlen] at hrun
  refine hrun.mono (fun τ' e => ?_) le_rfl
  rw [e, htw]
  simp only [Function.update_apply]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  simp

end TwistRound

end IntegerMultBounds.Schoenhage
