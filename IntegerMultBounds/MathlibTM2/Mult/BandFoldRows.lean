module

public import IntegerMultBounds.MathlibTM2.Mult.BandSolveFold
public import IntegerMultBounds.Resampling.WeightTable

/-! The folded matrix rows the table machine emits. Coefficients are the Gaussian
table entries `tableE` at precision `P` off the diagonal and exactly `2^P` on it.
Row `i` of the stream holds the folded entries on columns `i - min(i,B), …`,
`2B+1` of them; rows `0, …, B` form the initial window and the remaining rows are
the inputs of the window factorization. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.BandFactor

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Resampling.WeightTable

variable (s : ℕ) [NeZero s]

/-- The coefficient numerators: `2^P` on the diagonal, the Gaussian table off it. -/
def coefZ (t α P : ℕ) (j : ZMod s) (k : ℤ) : ℤ := if k=0 then 2^P else tableE s t α P j k

/-- One folded entry, by the forward residue of the folded vertices. -/
def foldEntryZ (t α P w i c : ℕ) : ℤ :=
  if i<s ∧ c<s then
    (if fdist s (foldAt s i) (foldAt s c)=0 then 2^P
    else if fdist s (foldAt s i) (foldAt s c) ≤ w then
      tableE s t α P (foldAt s i) (fdist s (foldAt s i) (foldAt s c))
    else if s-w ≤ fdist s (foldAt s i) (foldAt s c) then
      tableE s t α P (foldAt s i) ((fdist s (foldAt s i) (foldAt s c) : ℤ)-s)
    else 0)
  else 0

theorem foldEntryZ_eq (t α P w : ℕ) (hsw : 2*w+1 < s) (i c : ℕ) :
    foldEntryZ s t α P w i c=foldZ s w (coefZ s t α P) i c := by
  unfold foldEntryZ foldZ
  split
  · rw [wmZ_single s w hsw]
    have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
    by_cases h0 : fdist s (foldAt s i) (foldAt s c)=0
    · rw [h0]; simp [coefZ]
    · have hd := Nat.mod_lt ((foldAt s c).val+s-(foldAt s i).val) hs
      have h0' : ((fdist s (foldAt s i) (foldAt s c) : ℕ) : ℤ)≠0 := by exact_mod_cast h0
      have h0'' : ((fdist s (foldAt s i) (foldAt s c) : ℕ) : ℤ)-s≠0 := by
        unfold fdist; omega
      simp only [h0, ite_false, coefZ, h0', h0'']
  · rfl

/-- The folded row `i` on its `2B+1` columns. -/
def foldRowZ (t α P w B i : ℕ) : List ℤ :=
  (List.range' (i-min i B) (2*B+1)).map (foldEntryZ s t α P w i)

/-- The full row stream: the initial window followed by the factorization inputs. -/
theorem foldRows_eq (t α P w B : ℕ) (hsw : 2*w+1 < s) :
    (List.range' 0 (B+1+s)).map (foldRowZ s t α P w B)=
      windowZ B (foldZ s w (coefZ s t α P))++inputsZ B (foldZ s w (coefZ s t α P)) s := by
  rw [show B+1+s=(B+1)+s by rfl, ← List.range'_append, List.map_append]
  congr 1
  · simp only [windowZ]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range'_1.mp hi
    simp only [foldRowZ, winRowZ]
    rw [show i-min i B=0 by omega]
    exact List.map_congr_left fun c _ => foldEntryZ_eq s t α P w hsw i c
  · simp only [inputsZ, winRowZ, zero_add, one_mul]
    rw [show List.range' (B+1) s=(List.range' 0 s).map (·+(B+1)) from
      List.ext_getElem (by simp) (fun n h1 h2 => by simp; omega), List.map_map]
    refine List.map_congr_left fun m hm => ?_
    simp only [Function.comp, foldRowZ]
    rw [show m+(B+1)-min (m+(B+1)) B=m+1 by omega, show m+B+1=m+(B+1) by omega]
    exact List.map_congr_left fun c _ => foldEntryZ_eq s t α P w hsw _ c

/-- Each coefficient numerator is within `2` of `2^P exp(normExp)`. -/
theorem coefZ_err (t α P : ℕ) [NeZero t] (hst : s < t) (hP : 13 ≤ P) (j : ZMod s) (k : ℤ) :
    |gv P (coefZ s t α P j k)-Real.exp (normExp s t (α : ℝ) j.val k)|≤2/2^P := by
  have hP0 : (0 : ℝ)<2^P := by positivity
  unfold coefZ
  split
  · rename_i hk
    subst hk
    have : normExp s t (α : ℝ) j.val 0=0 := by simp [normExp]
    rw [this, Real.exp_zero]
    simp [gv]
    positivity
  · have h := tableE_err s t α P hst hP j k
    have e : gv P (tableE s t α P j k)-Real.exp (normExp s t (α : ℝ) j.val k)=
        ((tableE s t α P j k : ℝ)-2^P*Real.exp (normExp s t (α : ℝ) j.val k))/2^P := by
      simp only [gv]; field_simp
    rw [e, abs_div, abs_of_pos hP0]
    exact div_le_div_of_nonneg_right h hP0.le

end IntegerMultBounds.MathlibTM2.Mult.BandFactor
