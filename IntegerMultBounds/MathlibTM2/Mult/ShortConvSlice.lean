module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvExec
public import IntegerMultBounds.MathlibTM2.Fast.Input

/-! # Extract coefficient intervals without changing the product stream

Counted transfers keep their counter words intact. `copySlice` saves the skipped prefix,
copies the selected interval, and restores both prefixes. Only the destination changes;
all left stacks, counters, the source, and the three work tapes are restored.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- One symbol of a counted transfer. -/
def transferAct (src dst : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.push (.rt dst) (fun v => v.sym.getD blank) k)

/-- Register effect of moving one symbol. -/
def transferFx (src dst : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update (Function.update R src (R src).tail) dst
    ((R src).head?.getD blank :: R dst)

lemma transferAct_fx (src dst : Fin T) (h : src ≠ dst) :
    RegFx (transferAct (Q := Q) (A := A) (U := U) src dst) (transferFx src dst) := by
  intro x k v S _
  refine ⟨{ v with sym := (S.R src).head? }, rfl, ?_⟩
  simp [transferAct, transferFx, Action.run, update_rt, h.symm]

lemma transferFx_frame {src dst r : Fin T} (hs : r ≠ src) (hd : r ≠ dst) :
    Frame r (transferFx (A := A) src dst) := by
  intro x R l
  simp only [transferFx, Function.update_of_ne hs.symm, Function.update_of_ne hd.symm]
  rw [Function.update_comm hs, Function.update_comm hd]

/-- Fold the transfer structurally over the actual prefix, without any finite-index recursion. -/
lemma transferFx_fold (src dst : Fin T) (h : src ≠ dst)
    (cs xs rest : List (Fin (A + 4))) (hlen : cs.length = xs.length) (R : Regs T A)
    (hsrc : R src = xs ++ rest) :
    cs.foldl (fun R x => transferFx src dst x R) R =
      Function.update (Function.update R src rest) dst (xs.reverse ++ R dst) := by
  induction cs generalizing xs R with
  | nil =>
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst xs
      simp only [List.nil_append] at hsrc
      funext r
      simp only [List.foldl_nil, List.reverse_nil, List.nil_append, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | cons c cs ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          rw [List.foldl_cons, ih xs hlen]
          · funext r
            simp only [transferFx, Function.update_apply]
            split_ifs <;> subst_vars <;> simp_all [List.reverse_cons, List.append_assoc]
          · simp [transferFx, hsrc, h]

/-- Move a counted prefix onto `dst`, reversed, restoring the counter and scratch. -/
def transfer (count src dst tmp : Fin T) : Pr P T Q A U :=
  scanR count tmp (transferAct src dst)

theorem transfer_exec {count src dst tmp : Fin T} (hreg : [count, src, dst, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs rest : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ rest) (hlen : (S.R count).length = xs.length)
    (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (transfer count src dst tmp) (mk v S) (4 * xs.length + 4)
        (mk v' { S with R := (Function.update (Function.update S.R src rest) dst
          (xs.reverse ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v', hu, he⟩ := scanR_exec' body ‹count ≠ tmp› (transferAct_fx src dst ‹src ≠ dst›)
    (transferFx_frame ‹count ≠ src› ‹count ≠ dst›)
    (transferFx_frame ‹src ≠ tmp›.symm ‹dst ≠ tmp›.symm) v S htmp
  rw [transferFx_fold src dst ‹src ≠ dst› (S.R count) xs rest hlen S.R hsrc, hlen] at he
  exact ⟨v', hu, he⟩

/-- Copy a counted prefix in its original order and restore the source through `saved`. -/
def copyPrefix (count src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer count src saved tmp)
    (.seq (copyR saved dst tmp id) (moveR saved src id))

theorem copyPrefix_exec {count src dst saved tmp : Fin T}
    (hreg : [count, src, dst, saved, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs rest : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ rest) (hlen : (S.R count).length = xs.length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyPrefix count src dst saved tmp) (mk v S) (10 * xs.length + 10)
        (mk v' { S with R := Function.update S.R dst (xs ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
    (show [count, src, saved, tmp].Nodup by simp_all) v S xs rest hsrc hlen htmp
  set S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src rest) saved
    (xs.reverse ++ S.R saved)) }
  obtain ⟨v₂, hu₂, he₂⟩ := copyR_exec body saved dst tmp ‹dst ≠ saved›.symm ‹saved ≠ tmp›
    ‹dst ≠ tmp› id v₁ S₁ (by simp [S₁, ‹src ≠ tmp›.symm, ‹saved ≠ tmp›.symm, htmp])
  set S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R dst
    (((S₁.R saved).map id).reverse ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id v₂ S₂
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂, S₁, ‹dst ≠ saved›.symm, hsaved]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext r
    simp only [S₂, S₁, movedR, Function.update_apply, List.map_id, hsaved,
      List.append_nil]
    split_ifs <;> subst_vars <;> simp_all

/-- Copy a slice, preserving its source and all counters and scratch. -/
def copySlice (skip count src dst savedSkip saved tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer skip src savedSkip tmp)
    (.seq (copyPrefix count src dst saved tmp) (moveR savedSkip src id))

theorem copySlice_exec {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip, count, src, dst, savedSkip, saved, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (pre xs rest : List (Fin (A + 4)))
    (hsrc : S.R src = pre ++ xs ++ rest)
    (hskip : (S.R skip).length = pre.length) (hlen : (S.R count).length = xs.length)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6 * pre.length + 10 * xs.length + 16)
        (mk v' { S with R := Function.update S.R dst (xs ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
    (show [skip, src, savedSkip, tmp].Nodup by simp_all) v S pre (xs ++ rest)
    (by simpa [List.append_assoc] using hsrc) hskip htmp
  set S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src (xs ++ rest))
    savedSkip (pre.reverse ++ S.R savedSkip)) }
  obtain ⟨v₂, hu₂, he₂⟩ := copyPrefix_exec (body := body)
    (show [count, src, dst, saved, tmp].Nodup by simp_all) v₁ S₁ xs rest
    (by simp [S₁, ‹src ≠ savedSkip›])
    (by simpa [S₁, ‹count ≠ src›, ‹count ≠ savedSkip›] using hlen)
    (by simp [S₁, ‹src ≠ saved›.symm, ‹savedSkip ≠ saved›.symm, hsaved])
    (by simp [S₁, ‹src ≠ tmp›.symm, ‹savedSkip ≠ tmp›.symm, htmp])
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (xs ++ S₁.R dst) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body savedSkip src ‹src ≠ savedSkip›.symm id v₂ S₂
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂, S₁, ‹dst ≠ savedSkip›.symm, hsavedSkip]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext r
    simp only [S₂, S₁, movedR, Function.update_apply, List.map_id, hsavedSkip,
      List.append_nil]
    split_ifs <;> subst_vars <;> simp_all [List.append_assoc]

/-- Extract a coefficient interval with arbitrary trailing spectator symbols. -/
theorem copySlice_coeffs_exec {skip count src dst savedSkip saved tmp : Fin T}
    (hreg : [skip, count, src, dst, savedSkip, saved, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (w : ℕ) (pre xs rest : List GaussianInt)
    (tail : List (Fin (A + 4)))
    (hsrc : S.R src = cstream A w (pre ++ xs ++ rest) ++ tail)
    (hskip : (S.R skip).length = pre.length * w)
    (hlen : (S.R count).length = xs.length * w)
    (hsavedSkip : S.R savedSkip = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v S)
        (6 * (pre.length * w) + 10 * (xs.length * w) + 16)
        (mk v' { S with R := Function.update S.R dst (cstream A w xs ++ S.R dst) }) := by
  simpa only [length_cstream] using copySlice_exec (body := body) hreg v S
    (cstream A w pre) (cstream A w xs) (cstream A w rest ++ tail)
    (by simpa [cstream_append, List.append_assoc] using hsrc)
    (by simpa using hskip) (by simpa using hlen) hsavedSkip hsaved htmp

/-- The three consecutive pieces used by the extraction program reassemble the full record. -/
theorem slice_split {β : Type*} (zs : List β) (start len : ℕ) :
    zs.take start ++ (zs.drop start).take len ++ (zs.drop start).drop len = zs := by
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- The extracted interval's coefficients retain the original ring-output rounding bound. -/
theorem slice_coeff_err (p l : ℕ) (x y : List GaussianInt)
    (hxy : x.length + y.length ≤ 2 ^ l + 1) (start len i : ℕ)
    (hsize : start + len ≤ 2 ^ l) (hi : i < len) :
    let zs := ((List.ofFn (coeff p l x y)).drop start).take len
    ‖((2 ^ l : ℕ) : ℂ) * value p (zs[i]?.getD 0) -
      ∑ j ∈ Finset.range (start + i + 1),
        value p (block x j) * value p (block y (start + i - j))‖ ≤
          2 * (2 ^ l : ℕ) / (2 : ℝ) ^ p := by
  have hidx : start + i < 2 ^ l := by omega
  simpa [List.getElem?_take, hi, List.getElem?_drop, hidx, Nat.add_comm] using
    coeff_err p l x y hxy ⟨start + i, hidx⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
