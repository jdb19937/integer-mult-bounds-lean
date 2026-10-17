module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateTraversal
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateLayout
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Semantic invariant of runtime descriptor selection -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node TableVM

/-- The zero packet is parked only between visiting zero and visiting the target. -/
def crtControlParkedZero {d A : ℕ} (W : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (m : ℕ) : List (Fin (A + 4)) :=
  if 0 < m ∧ m ≤ i.val then (crtControlPacket W (crtControlAxisField a s i 0)).reverse else []

/-- The target marker changes once, when its original axis is visited. -/
def crtControlPast {A : ℕ} (i m : ℕ) : List (Fin (A + 4)) :=
  if i < m then [tick] else []

/-- The selector's three persistent outputs, separate from the arithmetic bank. -/
def CrtControlLayoutInvariant {d T A : ℕ} (W : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (zero dst past : Fin T) (tail : List (Fin (A + 4)))
    (m : ℕ) (R : Regs T A) : Prop :=
  R dst = crtControlTape W (crtControlGeneratedFields a s i m) ++ tail ∧
  R zero = crtControlParkedZero W a s i m ∧ R past = crtControlPast i.val m

/-- A blank semantic workspace starts with an arbitrary preserved tape suffix. -/
theorem CrtControlLayoutInvariant_zero {d T A : ℕ} (W : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (zero dst past : Fin T) (tail : List (Fin (A + 4)))
    (R : Regs T A) (hd : R dst = tail) (hz : R zero = []) (hp : R past = []) :
    CrtControlLayoutInvariant W a s i zero dst past tail 0 R := by
  simp [CrtControlLayoutInvariant, crtControlGeneratedFields, crtControlTape,
    crtControlParkedZero, crtControlPast, hd, hz, hp]

/-- Preparing the current entries supplies the two changing arithmetic inputs. -/
theorem crtControlPreparedField_eq_axisField {d A : ℕ} (a s : Fin (d + 1) → ℕ)
    (i j : Fin (d + 1)) (hji : j ≠ i) (st : TblSt 10 A)
    (h0 : st.val 0 = j.val) (h1 : st.val 1 = i.val)
    (h3 : st.val 3 = 2 ^ a i) (h4 : st.val 4 = 2 ^ a 0)
    (h6 : st.val 6 = prefixProd s j) (h9 : st.val 9 = 2 ^ crtPre a i.val) :
    crtControlGeneratedField (crtControlPreparedState st (s j) (crtPre a j.val)) =
      crtControlAxisField a s i j := by
  apply crtControlGeneratedField_eq_axisField a s i j hji
  all_goals simp [crtControlPreparedState, h0, h1, h3, h4, h6, h9]

/-- Runtime branch selection agrees with ascending original-axis generation. -/
theorem crtControlSelectRegs_layout {d T A : ℕ} (W : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (left seen past packet zero dst : Fin T)
    (hreg : [left, seen, past, packet, zero, dst].Nodup)
    (tail : List (Fin (A + 4))) (m : ℕ) (hm : m < d + 1) (R : Regs T A)
    (hl : R left = [] ↔ i.val ≤ m) (hs : R seen = [] ↔ m = 0)
    (hp : m ≠ i.val → R packet = crtControlPacket W (crtControlAxisField a s i ⟨m, hm⟩))
    (hI : CrtControlLayoutInvariant W a s i zero dst past tail m R) :
    CrtControlLayoutInvariant W a s i zero dst past tail (m + 1)
      (crtControlSelectRegs left seen past packet zero dst R) := by
  have hreg' := hreg
  regs_ne hreg'
  have hdp := Ne.symm ‹packet ≠ dst›
  have hdz := Ne.symm ‹zero ≠ dst›
  have hdt := Ne.symm ‹past ≠ dst›
  have hzp := Ne.symm ‹packet ≠ zero›
  have hzt := Ne.symm ‹past ≠ zero›
  obtain ⟨hd, hz, ht⟩ := hI
  unfold CrtControlLayoutInvariant
  by_cases hm0 : m = 0
  · subst m
    have hseen := hs.mpr rfl
    by_cases hi0 : i.val = 0
    · have hleft := hl.mpr (by omega)
      simp [crtControlSelectRegs, ↓reduceIte, crtControlPast, lt_self_iff_false, crtControlInsertZeroRegs,
    crtControlParkedZero, Std.le_refl, and_true, List.reverse_nil, crtControlTape, crtControlGeneratedFields,
    List.flatMap_nil, List.nil_append, ne_eq, not_false_eq_true, Function.update_of_ne, Function.update_self,
    ↓reduceDIte, zero_add, Order.lt_one_iff, nonpos_iff_eq_zero, one_ne_zero, and_false, and_self, *]
    · have hleft : R left ≠ [] := fun h => hi0 (by have := hl.mp h; omega)
      have hpacket := hp (Ne.symm hi0)
      have hfin : (⟨0, hm⟩ : Fin (d + 1)) = 0 := rfl
      simp [crtControlSelectRegs, ↓reduceIte, crtControlParkedZero, lt_self_iff_false, zero_le, and_true,
    List.append_nil, ne_eq, not_false_eq_true, Function.update_of_ne, crtControlTape, crtControlGeneratedFields,
    List.flatMap_nil, List.nil_append, ↓reduceDIte, Function.update_self, zero_add, Order.lt_one_iff, true_and,
    left_eq_ite_iff, not_le, List.reverse_eq_nil_iff, IsEmpty.forall_iff, crtControlPast, not_lt_zero, and_self, *]
  · have hseen : R seen ≠ [] := fun h => hm0 (hs.mp h)
    by_cases hmi : m = i.val
    · have hleft := hl.mpr (by omega)
      have hfin : (⟨m, hm⟩ : Fin (d + 1)) = i := Fin.ext hmi
      have hi : i ≠ 0 := by intro h; exact hm0 (hmi.trans (congrArg Fin.val h))
      have hib : i.val ≤ d := by omega
      simp [crtControlSelectRegs, ↓reduceIte, crtControlPast, lt_self_iff_false, crtControlInsertZeroRegs,
    crtControlParkedZero, show 0 < i.val by omega, Std.le_refl, and_self, List.reverse_reverse, crtControlTape, ne_eq,
    not_false_eq_true, Function.update_of_ne, Function.update_self, crtControlGeneratedFields, Order.lt_add_one_iff,
    ↓reduceDIte, Fin.val_eq_zero_iff, Fin.eta, Equiv.swap_apply_left, List.flatMap_cons, List.append_assoc,
    lt_add_iff_pos_left, zero_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, and_false,
    lt_add_iff_pos_right, Order.lt_one_iff, *]
    · have hn : (⟨m, hm⟩ : Fin (d + 1)) ≠ i := fun h => hmi (congrArg Fin.val h)
      have hn0 : (⟨m, hm⟩ : Fin (d + 1)) ≠ 0 := fun h => hm0 (congrArg Fin.val h)
      have hpacket := hp hmi
      by_cases hlt : m < i.val
      · have hleft : R left ≠ [] := fun h => by have := hl.mp h; omega
        simp [crtControlSelectRegs, ↓reduceIte, crtControlTape, ne_eq, not_false_eq_true, Function.update_of_ne,
    Function.update_self, crtControlGeneratedFields, ↓reduceDIte, Equiv.swap_apply_of_ne_of_ne hn hn0,
    List.flatMap_cons, List.append_assoc, crtControlParkedZero, show 0 < m by omega, show m ≤ i.val by omega, and_self,
    lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, show m + 1 ≤ i.val by omega, crtControlPast,
    show ¬i.val < m by omega, show ¬i.val < m + 1 by omega, show ¬i.val ≤ m by omega, *]
      · have hgt : i.val < m := by omega
        have hleft := hl.mpr (by omega)
        simp [crtControlSelectRegs, ↓reduceIte, crtControlPast, List.cons_ne_self, crtControlTape, ne_eq,
    not_false_eq_true, Function.update_of_ne, Function.update_self, crtControlGeneratedFields, ↓reduceDIte,
    Equiv.swap_apply_of_ne_of_ne hn hn0, List.flatMap_cons, List.append_assoc, crtControlParkedZero,
    show ¬m ≤ i.val by omega, and_false, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    show ¬m + 1 ≤ i.val by omega, show i.val < m + 1 by omega, and_self, *]

/-- The arithmetic and entry-stream operations frame the selector outputs. -/
theorem crtControlGenerateAxisRegs_layout_outputs {T A : ℕ} {rg : TblR 10 → Fin T}
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst].Nodup)
    (hd : ∀ j, ∀ r ∈ [left, savedWidths, past, packet, zero, dst], rg j ≠ r)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (a b e : ℕ) (as bs : List ℕ) (hp : R packet = [])
    (r : Fin T) (hr : r ∈ [past, zero, dst]) :
    crtControlGenerateAxisRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl st R a b e as bs r =
    crtControlSelectRegs left savedWidths past packet zero dst
      (Function.update R packet (crtControlPacket W
        (crtControlGeneratedField (crtControlPreparedState st b e)))) r := by
  have hreg' := hreg
  regs_ne hreg'
  have hb (j : TblR 10) (r : Fin T) (hr : r ∈ [left, savedWidths, past, packet, zero, dst]) := hd j r hr
  have ho (S : Regs T A) (ρ : TblR 10 → List (Fin (A + 4))) (r : Fin T)
      (hr : r ∈ [left, savedWidths, past, packet, zero, dst]) :
      crtBankOverlay rg S ρ r = S r := crtBankOverlay_off _ _ _ _ (fun j => hb j r hr)
  have hl := fun S ρ => ho S ρ left (by simp)
  have hs := fun S ρ => ho S ρ savedWidths (by simp)
  have ht := fun S ρ => ho S ρ past (by simp)
  have hp' := fun S ρ => ho S ρ packet (by simp)
  have hz := fun S ρ => ho S ρ zero (by simp)
  have hx := fun S ρ => ho S ρ dst (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr
  all_goals subst r
  all_goals
    simp only [crtControlGenerateAxisRegs,
      crtControlGenerateSelectRegs,
      crtControlSelectRegs,
      crtControlPoppedRegs,
      hp',
      ne_eq,
      Ne.symm ‹axisModulus ≠ packet›,
      not_false_eq_true,
      Function.update_of_ne,
      Ne.symm ‹moduli ≠ packet›,
      Ne.symm ‹axisWidth ≠ packet›,
      Ne.symm ‹widths ≠ packet›,
      hp,
      List.append_nil,
      ‹left ≠ packet›,
      hl,
      Ne.symm ‹axisModulus ≠ left›,
      Ne.symm ‹moduli ≠ left›,
      Ne.symm ‹axisWidth ≠ left›,
      Ne.symm ‹widths ≠ left›,
      ‹past ≠ packet›,
      ht,
      Ne.symm ‹axisModulus ≠ past›,
      Ne.symm ‹moduli ≠ past›,
      Ne.symm ‹axisWidth ≠ past›,
      Ne.symm ‹widths ≠ past›,
      crtControlInsertZeroRegs,
      Function.update_idem,
      Ne.symm ‹packet ≠ zero›,
      hz,
      Ne.symm ‹axisModulus ≠ zero›,
      Ne.symm ‹moduli ≠ zero›,
      Ne.symm ‹axisWidth ≠ zero›,
      Ne.symm ‹widths ≠ zero›,
      Ne.symm ‹packet ≠ dst›,
      hx,
      Ne.symm ‹axisModulus ≠ dst›,
      Ne.symm ‹moduli ≠ dst›,
      Ne.symm ‹axisWidth ≠ dst›,
      Ne.symm ‹widths ≠ dst›,
      Function.update_self,
      ‹savedWidths ≠ packet›,
      hs,
      ‹savedWidths ≠ axisModulus›,
      Ne.symm ‹moduli ≠ savedWidths›,
      ‹savedWidths ≠ axisWidth›,
      Ne.symm ‹widths ≠ savedWidths›,
      Ne.symm ‹lower ≠ left›,
      ite_apply,
      ‹left ≠ past›,
      ‹left ≠ dst›,
      ‹left ≠ zero›,
      ite_self,
      ‹savedWidths ≠ left›,
      ‹savedWidths ≠ lower›,
      ‹savedWidths ≠ past›,
      ‹savedWidths ≠ dst›,
      ‹savedWidths ≠ zero›,
      Ne.symm ‹savedWidths ≠ savedModuli›,
      ‹savedModuli ≠ axisWidth›,
      ‹savedModuli ≠ left›,
      ‹savedModuli ≠ lower›,
      Ne.symm ‹savedModuli ≠ past›,
      Ne.symm ‹savedWidths ≠ past›,
      Ne.symm ‹left ≠ past›,
      Ne.symm ‹lower ≠ past›,
      ‹past ≠ dst›,
      ‹past ≠ zero›,
      Ne.symm ‹savedModuli ≠ zero›,
      Ne.symm ‹savedWidths ≠ zero›,
      Ne.symm ‹left ≠ zero›,
      Ne.symm ‹lower ≠ zero›,
      Ne.symm ‹past ≠ zero›,
      ‹zero ≠ dst›,
      Ne.symm ‹savedModuli ≠ dst›,
      Ne.symm ‹savedWidths ≠ dst›,
      Ne.symm ‹left ≠ dst›,
      Ne.symm ‹lower ≠ dst›,
      Ne.symm ‹past ≠ dst›,
      Ne.symm ‹zero ≠ dst›]

/-- One complete executable axis transition preserves the semantic tape invariant. -/
theorem crtControlGenerateAxisRegs_layout {d T A : ℕ} {rg : TblR 10 → Fin T}
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst].Nodup)
    (hd : ∀ j, ∀ r ∈ [left, savedWidths, past, packet, zero, dst], rg j ≠ r)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1))
    (m : ℕ) (hm : m < d + 1) (as bs : List ℕ) (tail : List (Fin (A + 4)))
    (hp : R packet = []) (hl : R left = [] ↔ i.val ≤ m)
    (hs : R savedWidths = [] ↔ m = 0)
    (hf : m ≠ i.val →
      crtControlGeneratedField (crtControlPreparedState st (s ⟨m, hm⟩) (crtPre a m)) =
        crtControlAxisField a s i ⟨m, hm⟩)
    (hI : CrtControlLayoutInvariant W a s i zero dst past tail m R) :
    CrtControlLayoutInvariant W a s i zero dst past tail (m + 1)
      (crtControlGenerateAxisRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
        lower left past packet zero dst W wl nl st R (a ⟨m, hm⟩) (s ⟨m, hm⟩)
          (crtPre a m) as bs) := by
  have hreg' := hreg
  regs_ne hreg'
  let R' := Function.update R packet (crtControlPacket W
    (crtControlGeneratedField (crtControlPreparedState st (s ⟨m, hm⟩) (crtPre a m))))
  have hI' : CrtControlLayoutInvariant W a s i zero dst past tail m R' := by
    simpa [CrtControlLayoutInvariant, R', Ne.symm ‹packet ≠ dst›,
      Ne.symm ‹packet ≠ zero›, ‹past ≠ packet›] using hI
  have h := crtControlSelectRegs_layout W a s i left savedWidths past packet zero dst
    (by regs_nodup) tail m hm R'
    (by simpa [R', ‹left ≠ packet›] using hl)
    (by simpa [R', ‹savedWidths ≠ packet›] using hs)
    (by intro hn; simp [R', hf hn]) hI'
  unfold CrtControlLayoutInvariant at h ⊢
  have hout := crtControlGenerateAxisRegs_layout_outputs widths moduli savedWidths savedModuli
    axisWidth axisModulus lower left past packet zero dst hreg hd W wl nl st R
      (a ⟨m, hm⟩) (s ⟨m, hm⟩) (crtPre a m) as bs hp
  rw [hout dst (by simp), hout zero (by simp), hout past (by simp)]
  exact h

/-- The unary prefix sum consumed by the program is the original bit prefix. -/
theorem crtControl_ofFn_take_sum {d : ℕ} (a : Fin (d + 1) → ℕ) :
    ∀ m ≤ d + 1, ((List.ofFn a).take m).sum = crtPre a m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    have hm' : m < d + 1 := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hm')]
    simp only [List.getElem_ofFn, Option.toList_some, List.sum_append, List.sum_singleton]
    rw [ih (by omega), crtPre_succ a hm']

/-- Induction on the actual recursive register trajectory, including parked zero. -/
theorem crtControlTraversal_layout {d T A : ℕ} {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp].Nodup)
    (hd : ∀ j, ∀ r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp], rg j ≠ r)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1)) (tail : List (Fin (A + 4)))
    (hinit : CrtControlTraversalInvariant rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left packet pad tmp W wl nl st (List.ofFn a) (List.ofFn s) i.val 0 R)
    (hI : CrtControlLayoutInvariant W a s i zero dst past tail 0 R)
    (hf : ∀ m (hm : m < d + 1), m ≠ i.val →
      crtControlGeneratedField (crtControlPreparedState
        (crtControlTraversalState st (List.ofFn a) (List.ofFn s) m)
        (s ⟨m, hm⟩) (crtPre a m)) = crtControlAxisField a s i ⟨m, hm⟩) :
    ∀ m ≤ d + 1, CrtControlLayoutInvariant W a s i zero dst past tail m
      (crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
        lower left past packet zero dst W wl nl st R (List.ofFn a) (List.ofFn s) m) := by
  have hreg12 : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst].Nodup := by
    exact (List.nodup_append.mp (show ([widths, moduli, savedWidths, savedModuli, axisWidth,
      axisModulus, lower, left, past, packet, zero, dst] ++ [pad, tmp]).Nodup from hreg)).1
  have hstruct := crtControlTraversal_invariant hrg widths moduli savedWidths savedModuli
    axisWidth axisModulus lower left past packet zero dst pad tmp hreg hd W wl nl st R
      (List.ofFn a) (List.ofFn s) i.val (by simp) hinit
  intro m
  induction m with
  | zero => intro _; exact hI
  | succ m ih =>
    intro hm
    have hm' : m < d + 1 := by omega
    have hS := hstruct m (by simp; omega)
    have hleft : _ := hS.left
    have hseen : _ := hS.savedWidths
    have hseen' : (crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
        lower left past packet zero dst W wl nl st R (List.ofFn a) (List.ofFn s) m) savedWidths = [] ↔ m = 0 := by
      rw [hseen, crtEnts_eq_nil, List.reverse_eq_nil_iff]
      constructor
      · intro h
        have hlen := congrArg List.length h
        simp only [List.length_take, List.length_ofFn, List.length_nil] at hlen
        omega
      · intro h; subst m; simp
    have hstep := crtControlGenerateAxisRegs_layout widths moduli savedWidths savedModuli
      axisWidth axisModulus lower left past packet zero dst hreg12
      (fun j r hr => hd j r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
      W wl nl (crtControlTraversalState st (List.ofFn a) (List.ofFn s) m) _ a s i m hm'
      ((List.ofFn a).drop (m + 1)) ((List.ofFn s).drop (m + 1)) tail hS.packet
      (by rw [hleft]; simp; omega) hseen' (hf m hm') (ih (by omega))
    have hga : (List.ofFn a).getD m 0 = a ⟨m, hm'⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hm')]; simp only [List.getElem_ofFn]
    have hgs : (List.ofFn s).getD m 0 = s ⟨m, hm'⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hm')]; simp only [List.getElem_ofFn]
    simpa only [crtControlTraversalRegs, hga, hgs,
      crtControl_ofFn_take_sum a m hm'.le] using hstep

/-- The actual recursive arithmetic states generate each original-axis field. -/
theorem crtControlTraversal_field {d A : ℕ} (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (st : TblSt 10 A)
    (h0 : st.val 0 = 0) (h1 : st.val 1 = i.val)
    (h3 : st.val 3 = 2 ^ a i) (h4 : st.val 4 = 2 ^ a 0)
    (h6 : st.val 6 = 1) (h9 : st.val 9 = 2 ^ crtPre a i.val)
    (m : ℕ) (hm : m < d + 1) (hmi : m ≠ i.val) :
    crtControlGeneratedField (crtControlPreparedState
      (crtControlTraversalState st (List.ofFn a) (List.ofFn s) m)
      (s ⟨m, hm⟩) (crtPre a m)) = crtControlAxisField a s i ⟨m, hm⟩ := by
  apply crtControlPreparedField_eq_axisField a s i ⟨m, hm⟩
    (fun h => hmi (congrArg Fin.val h))
  · simp only [crtControlTraversalState_index, h0, Nat.zero_add]
  · rw [crtControlTraversalState_fixed st _ _ m 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h1]
  · rw [crtControlTraversalState_fixed st _ _ m 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h3]
  · rw [crtControlTraversalState_fixed st _ _ m 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h4]
  · exact crtControlTraversalState_weight_prefix st a s h6 ⟨m, hm⟩
  · rw [crtControlTraversalState_fixed st _ _ m 9 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h9]

/-- The invariant at traversal completion is the exact exposed-layout tape. -/
theorem CrtControlLayoutInvariant_full {d T A : ℕ} (W : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (zero dst past : Fin T) (tail : List (Fin (A + 4)))
    (R : Regs T A) (h : CrtControlLayoutInvariant W a s i zero dst past tail (d + 1) R) :
    R dst = crtControlTape W (crtControlFields a s i.val (crtExposePrefix i)) ++ tail ∧
      R zero = [] ∧ R past = [tick] := by
  obtain ⟨hd, hz, hp⟩ := h
  rw [crtControlGeneratedFields_full] at hd
  exact ⟨hd, by simpa [crtControlParkedZero, show ¬d + 1 ≤ i.val by omega] using hz,
    by simpa [crtControlPast, i.isLt] using hp⟩

/-- Exact final tape of the concrete register trajectory from its initialized bank.
No per-axis packet semantics or execution contract is assumed. -/
theorem crtControlTraversal_exactTape {d T A : ℕ} {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp].Nodup)
    (hd : ∀ j, ∀ r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp], rg j ≠ r)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1)) (tail : List (Fin (A + 4)))
    (hinit : CrtControlTraversalInvariant rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left packet pad tmp W wl nl st (List.ofFn a) (List.ofFn s) i.val 0 R)
    (hdst : R dst = tail) (hz : R zero = []) (hpast : R past = [])
    (h0 : st.val 0 = 0) (h1 : st.val 1 = i.val)
    (h3 : st.val 3 = 2 ^ a i) (h4 : st.val 4 = 2 ^ a 0)
    (h6 : st.val 6 = 1) (h9 : st.val 9 = 2 ^ crtPre a i.val) :
    let S := crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl st R (List.ofFn a) (List.ofFn s) (d + 1)
    S dst = crtControlTape W (crtControlFields a s i.val (crtExposePrefix i)) ++ tail ∧
      S zero = [] ∧ S past = [tick] := by
  apply CrtControlLayoutInvariant_full W a s i zero dst past tail
    (crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl st R (List.ofFn a) (List.ofFn s) (d + 1))
  apply crtControlTraversal_layout hrg widths moduli savedWidths savedModuli axisWidth axisModulus
    lower left past packet zero dst pad tmp hreg hd W wl nl st R a s i tail hinit
    (CrtControlLayoutInvariant_zero W a s i zero dst past tail R hdst hz hpast)
    (crtControlTraversal_field a s i st h0 h1 h3 h4 h6 h9) (d + 1) le_rfl

end IntegerMultBounds.MathlibTM2.Fast
