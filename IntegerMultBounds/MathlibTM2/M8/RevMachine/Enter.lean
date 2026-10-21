module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Headers
public import IntegerMultBounds.Machine.RecursiveChildCallSetup
public import IntegerMultBounds.Machine.RecursiveChildCallReturn
public import IntegerMultBounds.Machine.ExactFrame

/-!
# Entering and leaving a sub-view call

`RecursiveChildCallSetup` saves the parent's six headers and the return code, then builds the
headers of the cross child `child q roles b v i j` from the literal indices `i, j`. A call of the
reversed family enters `sub q w n s c v` instead, whose offsets are runtime values. Here the
call bank carries four extra counter tapes `w, s, c, e` (`viewBank`). `enterView` saves the
headers and the return code exactly as before, copies the counters next to the headers, runs
`Headers.program` and erases the copies (`enters`): the bank then holds the sub-view's headers
and the saved stacks, and the counters are unchanged. The cost is linear in the parent volume
plus the return code (`enters_volume`).

Leaving is the existing `RecursiveChildCallReturn.program`, which restores any saved headers;
its cost is linear in the parent volume for sub-view headers too (`restore_cost_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Enter

noncomputable section
open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.Machine.SharedPlacementAlphabet (setTape)
open IntegerMultBounds.Machine.CounterDimensions (descriptorHead descriptorTape)
open IntegerMultBounds.Machine.RecursiveChildCallSetup (descriptorStack fields pcStack savedStacks words)

variable {q k : ℕ} (hq : 2 ≤ q)

/-- The four counters `w, s, c, e`, each at head one. -/
def counters (ws ss cs es : List Bool) : Tapes 4 q :=
  ⟨fun _ => 1, ![RadixZeroFill.encodedBinary ws, RadixZeroFill.encodedBinary ss,
    RadixZeroFill.encodedBinary cs, RadixZeroFill.encodedBinary es]⟩

/-- The call bank with its counters. -/
def viewBank (hs : Fin 6 → List Bool) (st : Tapes 2 q) (cnt : Tapes 4 q) : Tapes (40+4) q :=
  (RecursiveChildCallSetup.bank hs st).append cnt

/-- The headers only, as an optional descriptor bank. -/
def base (hs : Fin 6 → List Bool) : Fin 22 → Option (List Bool) :=
  ![none, none, none, some (hs 0), some (hs 1), some (hs 2), some (hs 3), some (hs 4), some (hs 5),
    none, none, none, none, none, none, none, none, none, none, none, none, none]

/-- Everything after the first `22` tapes. -/
def rest (st : Tapes 2 q) (cnt : Tapes 4 q) : Tapes ((16+2)+4) q :=
  ((SharedBank.empty 16 q).append st).append cnt

theorem view_split (hs : Fin 6 → List Bool) (st : Tapes 2 q) (cnt : Tapes 4 q) :
    viewBank hs st cnt = (Headers.bank (base hs)).append (rest st cnt) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-! ### Copying the counters in and out -/

theorem append_right_tape {l r : ℕ} (X : Tapes l q) (Y : Tapes r q) (i : Fin r) :
    (X.append Y).tape (Fin.natAdd l i) = Y.tape i := by simp [Tapes.append]

theorem append_right_head {l r : ℕ} (X : Tapes l q) (Y : Tapes r q) (i : Fin r) :
    (X.append Y).head (Fin.natAdd l i) = Y.head i := by simp [Tapes.append]

theorem copy_in {d : Fin 22 → Option (List Bool)} {R : Tapes 22 q} (j : Fin 22) (r : Fin 22)
    (xs : List Bool) (hd : d j = none) (hr : R.tape r = RadixZeroFill.encodedBinary xs)
    (hrh : R.head r = 1) (hne : Fin.natAdd 22 r ≠ Fin.castAdd 22 j) :
    HoareTime (BinaryDescriptorInstall.program q (Fin.natAdd 22 r) (Fin.castAdd 22 j) hne)
      (fun v => v = (Headers.bank d).append R)
      (fun v => v = (Headers.bank (Function.update d j (some xs))).append R) (2*xs.length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (Fin.natAdd 22 r) (Fin.castAdd 22 j) hne
    ((Headers.bank (q := q) d).append R) xs
    ((append_right_tape _ _ r).trans hr) ((append_right_head _ _ r).trans hrh)
    (by simp [Tapes.append, Headers.bank, hd, descriptorTape])
    (by simp [Tapes.append, Headers.bank, hd, descriptorHead])
  rw [SharedPlacementAlphabet.setTape_append_left, ← show descriptorTape q (some xs) =
    RadixZeroFill.encodedBinary xs from rfl, ← show descriptorHead (some xs) = 1 from rfl,
    ← Headers.bank_update] at h
  exact h

theorem erase_out {d : Fin 22 → Option (List Bool)} {R : Tapes 22 q} (j : Fin 22)
    (xs : List Bool) (hd : d j = some xs) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (a := q) (Fin.castAdd 22 j))
      (fun v => v = (Headers.bank d).append R)
      (fun v => v = (Headers.bank (Function.update d j none)).append R) (2*xs.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (Fin.castAdd 22 j)
    ((Headers.bank (q := q) d).append R) xs
    (by simp [Tapes.append, Headers.bank, hd, descriptorTape,
      BinaryDescriptorStackRoundtrip.descriptor_encoded])
    (by simp [Tapes.append, Headers.bank, hd, descriptorHead])
  rw [SharedPlacementAlphabet.setTape_append_left, ← show descriptorTape q none = (fun _ => blank) from rfl,
    ← show descriptorHead none = 0 from rfl, ← Headers.bank_update] at h
  exact h

/-! ### The entry program -/

def copyAt (r j : ℕ) (hr : r < 22) (hj : j < 22) : Program (22+22) 5 q :=
  BinaryDescriptorInstall.program q (Fin.natAdd 22 ⟨r, hr⟩) (Fin.castAdd 22 ⟨j, hj⟩)
    (fun h => by have := congrArg Fin.val h; simp at this; omega)

def eraseAt (j : ℕ) (hj : j < 22) : Program (22+22) 4 q :=
  BinaryDescriptorCleanupList.oneProgram (Fin.castAdd 22 ⟨j, hj⟩)

/-- Save, copy the counters in, build the child headers, erase the copies. -/
def enterView (code : FiniteReturnStack.Code k) :=
  seq (seq (seq (extend (RecursiveFrameControl.callProgram (a := q) descriptorStack fields pcStack code) 4)
    (seq (seq (seq (copyAt (q := q) 18 9 (by decide) (by decide)) (copyAt (q := q) 19 10 (by decide) (by decide)))
      (copyAt (q := q) 20 11 (by decide) (by decide))) (copyAt (q := q) 21 12 (by decide) (by decide))))
    (extend (Headers.program hq) 22))
    (seq (seq (seq (eraseAt (q := q) 9 (by decide)) (eraseAt (q := q) 10 (by decide)))
      (eraseAt (q := q) 11 (by decide))) (eraseAt (q := q) 12 (by decide)))

variable {v : Descriptor} {hs : Fin 6 → List Bool} {ws ss cs es : List Bool} {w s c e : ℕ}

theorem save_step (code : FiniteReturnStack.Code k) (st : Tapes 2 q) (cnt : Tapes 4 q) :
    HoareTime (extend (RecursiveFrameControl.callProgram (a := q) descriptorStack fields pcStack code) 4)
      (fun x => x = viewBank hs st cnt)
      (fun x => x = (Headers.bank (base hs)).append (rest (savedStacks hs st code) cnt))
      (BinaryDescriptorFrames.cost fields (words hs) + 1 + k) := by
  have h1 := hoare_extend_eq (RecursiveChildCallSetup.save_hoare hs st code) cnt
  rw [← view_split]
  exact h1

theorem rest_counter (st : Tapes 2 q) (i : Fin 4) :
    (rest st (counters ws ss cs es)).tape (Fin.natAdd 18 i) = (counters (q := q) ws ss cs es).tape i ∧
      (rest st (counters (q := q) ws ss cs es)).head (Fin.natAdd 18 i) = 1 := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

theorem copies_step (R : Tapes 22 q)
    (hR : ∀ i : Fin 4, R.tape (Fin.natAdd 18 i) = (counters (q := q) ws ss cs es).tape i ∧
      R.head (Fin.natAdd 18 i) = 1) :
    HoareTime (seq (seq (seq (copyAt (q := q) 18 9 (by decide) (by decide)) (copyAt (q := q) 19 10 (by decide) (by decide)))
      (copyAt (q := q) 20 11 (by decide) (by decide))) (copyAt (q := q) 21 12 (by decide) (by decide)))
      (fun x => x = (Headers.bank (base hs)).append R)
      (fun x => x = (Headers.bank (Headers.inputs hs ws ss cs es)).append R)
      ((2*ws.length+5) + (2*ss.length+5) + (2*cs.length+5) + (2*es.length+5) + 3) := by
  have c1 := copy_in (q := q) (d := base hs) (R := R) 9 18 ws rfl (hR 0).1 (hR 0).2
    (fun h => by have := congrArg Fin.val h; simp at this)
  have c2 := copy_in (q := q) (d := Function.update (base hs) 9 (some ws)) (R := R) 10 19 ss
    rfl (hR 1).1 (hR 1).2 (fun h => by have := congrArg Fin.val h; simp at this)
  have c3 := copy_in (q := q) (d := Function.update (Function.update (base hs) 9 (some ws)) 10 (some ss))
    (R := R) 11 20 cs rfl (hR 2).1 (hR 2).2 (fun h => by have := congrArg Fin.val h; simp at this)
  have c4 := copy_in (q := q) (d := Function.update (Function.update (Function.update (base hs) 9 (some ws))
    10 (some ss)) 11 (some cs)) (R := R) 12 21 es rfl (hR 3).1 (hR 3).2
    (fun h => by have := congrArg Fin.val h; simp at this)
  have hin : Function.update (Function.update (Function.update (Function.update (base hs) 9 (some ws))
      10 (some ss)) 11 (some cs)) 12 (some es) = Headers.inputs hs ws ss cs es := by
    funext i; fin_cases i <;> rfl
  rw [hin] at c4
  exact (((c1.seq c2).seq c3).seq c4).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem erases_step (ch : Fin 6 → List Bool) (R : Tapes 22 q) :
    HoareTime (seq (seq (seq (eraseAt (q := q) 9 (by decide)) (eraseAt (q := q) 10 (by decide)))
      (eraseAt (q := q) 11 (by decide))) (eraseAt (q := q) 12 (by decide)))
      (fun x => x = (Headers.bank (Headers.inputs ch ws ss cs es)).append R)
      (fun x => x = (Headers.bank (base ch)).append R)
      ((2*ws.length+4) + (2*ss.length+4) + (2*cs.length+4) + (2*es.length+4) + 3) := by
  have e1 := erase_out (q := q) (d := Headers.inputs ch ws ss cs es) (R := R) 9 ws rfl
  have e2 := erase_out (q := q) (d := Function.update (Headers.inputs ch ws ss cs es) 9 none) (R := R) 10 ss rfl
  have e3 := erase_out (q := q) (d := Function.update (Function.update (Headers.inputs ch ws ss cs es) 9 none)
    10 none) (R := R) 11 cs rfl
  have e4 := erase_out (q := q) (d := Function.update (Function.update (Function.update
    (Headers.inputs ch ws ss cs es) 9 none) 10 none) 11 none) (R := R) 12 es rfl
  have hout : Function.update (Function.update (Function.update (Function.update
      (Headers.inputs ch ws ss cs es) 9 none) 10 none) 11 none) 12 none = base ch := by
    funext i; fin_cases i <;> rfl
  rw [hout] at e4
  exact (((e1.seq e2).seq e3).seq e4).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- **Entering a sub-view call.** -/
theorem enters (code : FiniteReturnStack.Code k) (st : Tapes 2 q)
    (hv : RecursiveDimensionBank.Headers v hs)
    (hpos : v.Positive) (hw0 : 0 < w) {n : ℕ} (hwidth : v.width = n * w) (hsc : s + c ≤ n)
    (he : e = n - s - c)
    (hwv : Counter.value ws = w) (hsv : Counter.value ss = s) (hcv : Counter.value cs = c)
    (hev : Counter.value es = e)
    (cwv : GrowingCounterData.Canonical ws) (csv : GrowingCounterData.Canonical ss)
    (ccv : GrowingCounterData.Canonical cs) (cev : GrowingCounterData.Canonical es) :
    HoareTime (enterView hq code) (fun x => x = viewBank hs st (counters ws ss cs es))
      (fun x => x = viewBank (Headers.childHeaders (q := q) v hs w s c e) (savedStacks hs st code)
        (counters ws ss cs es))
      (BinaryDescriptorFrames.cost fields (words hs) + 1 + k + 1 +
        ((2*ws.length+5) + (2*ss.length+5) + (2*cs.length+5) + (2*es.length+5) + 3) + 1 +
        1500 * volume q v + 1 +
        ((2*ws.length+4) + (2*ss.length+4) + (2*cs.length+4) + (2*es.length+4) + 3)) := by
  have h1 := save_step (hs := hs) code st (counters (q := q) ws ss cs es)
  have h2 := copies_step (hs := hs) (ws := ws) (ss := ss) (cs := cs) (es := es)
    (rest (savedStacks hs st code) (counters (q := q) ws ss cs es)) (rest_counter _)
  have h3 := hoare_extend_eq (Headers.prepares hq hv hpos hw0 hwidth hsc he hwv hsv hcv hev cwv csv ccv cev)
    (rest (savedStacks hs st code) (counters (q := q) ws ss cs es))
  have h4 := erases_step (ws := ws) (ss := ss) (cs := cs) (es := es)
    (Headers.childHeaders (q := q) v hs w s c e) (rest (savedStacks hs st code) (counters (q := q) ws ss cs es))
  rw [← view_split] at h4
  exact ((h1.seq h2).seq h3).seq h4

theorem sub_positive {n : ℕ} (hpos : v.Positive) (hq0 : 0 < q) :
    (RevMachine.sub q w n s c v).Positive := by
  obtain ⟨hA, hR, hB, hC, hE⟩ := hpos
  exact ⟨hA, hR, Nat.mul_pos hB (pow_pos hq0 _),
    Nat.mul_pos (Nat.mul_pos (pow_pos hq0 _) hC) (pow_pos hq0 _), Nat.mul_pos (pow_pos hq0 _) hE⟩

/-- **Entering in linear time.** With every counter at most the parent volume, entry costs at
most `1700` times the parent volume plus the return code. -/
theorem enters_volume (code : FiniteReturnStack.Code k) (st : Tapes 2 q)
    (hv : RecursiveDimensionBank.Headers v hs)
    (hpos : v.Positive) (hw0 : 0 < w) {n : ℕ} (hwidth : v.width = n * w) (hsc : s + c ≤ n)
    (he : e = n - s - c)
    (hwv : Counter.value ws = w) (hsv : Counter.value ss = s) (hcv : Counter.value cs = c)
    (hev : Counter.value es = e)
    (cwv : GrowingCounterData.Canonical ws) (csv : GrowingCounterData.Canonical ss)
    (ccv : GrowingCounterData.Canonical cs) (cev : GrowingCounterData.Canonical es)
    (hcount : w ≤ volume q v ∧ s ≤ volume q v ∧ c ≤ volume q v ∧ e ≤ volume q v) :
    HoareTime (enterView hq code) (fun x => x = viewBank hs st (counters ws ss cs es))
      (fun x => x = viewBank (Headers.childHeaders (q := q) v hs w s c e) (savedStacks hs st code)
        (counters ws ss cs es))
      (1700 * volume q v + k) := by
  refine (enters hq code st hv hpos hw0 hwidth hsc he hwv hsv hcv hev cwv csv ccv cev).consequence
    (fun _ h => h) (fun _ h => h) ?_
  set V := volume q v
  have hV := RecursiveAffinePrepare.volume_positive hq v hpos
  have hlen (z : Fin 6) : (hs z).length ≤ 2 * V := by
    have h1 : (hs z).length ≤ Nat.log2 V + 1 := RecursiveAffinePrepare.header_log hq v hpos hs hv z
    have h2 := Nat.log2_le_self V
    omega
  have hframe := BinaryDescriptorFrames.six_field_cost fields (by simp [fields]) (words hs) (2 * V) (by
    intro op hop
    obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hop
    rw [RecursiveChildCallSetup.words_header]
    exact hlen z)
  have lw := Headers.length_le ws cwv
  have ls := Headers.length_le ss csv
  have lc := Headers.length_le cs ccv
  have le := Headers.length_le es cev
  rw [hwv] at lw; rw [hsv] at ls; rw [hcv] at lc; rw [hev] at le
  obtain ⟨h1, h2, h3, h4⟩ := hcount
  omega

include hq in
/-- **Leaving a sub-view call** restores the parent headers, at most `127` times the parent
volume. -/
theorem restore_cost_le (hpos : v.Positive) {n : ℕ} (hwidth : v.width = n * w) (hsc : s + c ≤ n)
    (he : e = n - s - c) (hv : RecursiveDimensionBank.Headers v hs) :
    RecursiveChildCallReturn.cost hs (Headers.childHeaders (q := q) v hs w s c e) ≤ 127 * volume q v := by
  have hq' : 0 < q := by omega
  have hc := Headers.child_headers (q := q) (w := w) hv he
  have hvol : volume q (RevMachine.sub q w n s c v) = volume q v :=
    RevMachine.sub_volume q w n s c v hwidth hsc
  have hV := RecursiveAffinePrepare.volume_positive hq v hpos
  have hold (z : Fin 6) : (hs z).length ≤ 2 * volume q v := by
    have h := RecursiveAffinePrepare.header_log hq v hpos hs hv z
    have hl := Nat.log2_le_self (volume q v)
    omega
  have hnew (z : Fin 6) : (Headers.childHeaders (q := q) v hs w s c e z).length ≤ 2 * volume q v := by
    have h := RecursiveAffinePrepare.header_log hq _ (sub_positive hpos hq') _ hc z
    rw [hvol] at h
    have hl := Nat.log2_le_self (volume q v)
    omega
  have hpop := BinaryDescriptorFrames.six_field_cost fields (by simp [fields]) (words hs)
    (2 * volume q v) (by
      intro op hop
      obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact hold z)
  have hclear := BinaryDescriptorCleanupList.cost_le (BinaryDescriptorFrameRestore.slots fields)
    (words (Headers.childHeaders (q := q) v hs w s c e)) (2 * volume q v) (by
      intro z hz
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact hnew i)
  have hlen : (BinaryDescriptorFrameRestore.slots fields).length = 6 := by
    simp [BinaryDescriptorFrameRestore.slots, fields]
  rw [hlen] at hclear
  unfold RecursiveChildCallReturn.cost
  omega

end

end IntegerMultBounds.MathlibTM2.M8.RevMachine.Enter
