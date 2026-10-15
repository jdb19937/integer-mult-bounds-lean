module

public import IntegerMultBounds.MathlibTM2.Node.CompactBad
public import IntegerMultBounds.MathlibTM2.Node.CompactKeyBridge
public import IntegerMultBounds.MathlibTM2.Node.CompactRepair

/-!
# The exceptional-set indicator of the compact slot XOR, per record

`badPrep` is the preparation program of the compact repair pass: before every record it reads the
field registers of the index (the temporary fields `T`, `U` and the target slot `Y`), copies them
into scratch registers padded to the slot width, runs the two code automata of
`Node/CompactBad.lean` against the mask constants, and writes the indicator of the exceptional
set (one symbol) into the computed register `comp`, restoring everything else. Its contract is
the `Host.PrepSpec` of the prepared repair machine (`badPrep_spec`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor
  IntegerMultBounds.MathlibTM2.Layer.CompactXor

section Pieces

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Duplicate register `a` onto `b` through the empty `t`, `t₂`. -/
def dupR (a b t t₂ : Fin T) : Pr P T Q A U :=
  .seq (scanR a t (pushN t₂ (fun v => v.sym.getD blank) 1)) (moveR t₂ b id)

theorem dupR_exec {a b t t₂ : Fin T} (hreg : [a, b, t, t₂].Nodup) (v : HS T Q A U)
    (S : Stacks T A) (ht : S.R t = []) (ht₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (dupR a b t t₂) (mk v S) (6 * (S.R a).length + 6)
        (mk v' { S with R := Function.update S.R b (S.R a ++ S.R b) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hab, hat, hat₂⟩, ⟨hbt, hbt₂⟩, htt₂⟩ := hreg
  obtain ⟨v₁, hu₁, he₁⟩ := scanR_exec' body hat
    (regFx_pushN t₂ 1 (fun v => v.sym.getD blank) id (fun v x hx => by simp [hx]))
    (frame_pushFx hat₂ 1 id) (frame_pushFx htt₂ 1 id) v S ht
  rw [foldl_pushFx] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t₂ b hbt₂.symm id v₁
    { S with
      R := Function.update S.R t₂
        (((S.R a).reverse.flatMap fun x => List.replicate 1 (id x)) ++ S.R t₂) }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [ht₂]; ring
  · congr 2
    funext k
    simp only [movedR, Function.update_apply, ht₂, List.append_nil, List.map_id, id]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [flatMap_replicate_one]

/-- Copy the field register `f` onto the empty `sF`, padded above by `|padR|` zeros. -/
def padCopy (padR f sF t₁ t₂ t₃ t₄ : Fin T) : Pr P T Q A U :=
  .seq (zeroBits padR sF t₁)
    (.seq (moveR f t₁ id)
      (.seq (dupR t₁ t₂ t₃ t₄)
        (.seq (moveR t₁ f id) (moveR t₂ sF id))))

theorem padCopy_exec {padR f sF t₁ t₂ t₃ t₄ : Fin T}
    (hreg : [padR, f, sF, t₁, t₂, t₃, t₄].Nodup) {m x pad : ℕ} (hx : x < 2 ^ m)
    (v : HS T Q A U) (S : Stacks T A) (hf : S.R f = binSyms m x) (hsF : S.R sF = [])
    (hpad : (S.R padR).length = pad) (h1 : S.R t₁ = []) (h2 : S.R t₂ = []) (h3 : S.R t₃ = [])
    (h4 : S.R t₄ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (padCopy padR f sF t₁ t₂ t₃ t₄) (mk v S) (12 * m + 4 * pad + 16)
        (mk v' { S with R := Function.update S.R sF (binSyms (m + pad) x) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hpf, hps, hp1, hp2, hp3, hp4⟩, ⟨hfs, hf1, hf2, hf3, hf4⟩, ⟨hs1, hs2, hs3, hs4⟩,
    ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hreg'
  have hml : (S.R f).length = m := by rw [hf, length_binSyms]
  -- zeros
  obtain ⟨v₁, hu₁, he₁⟩ := zeroBits_exec body hps hp1 hs1 v S h1
  rw [hpad, hsF, List.append_nil] at he₁
  set R₁ := Function.update S.R sF (binSyms pad 0 : List (Fin (A + 4))) with hR₁
  -- move the field
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body f t₁ hf1 id v₁ { S with R := R₁ }
  have hR₁f : R₁ f = binSyms m x := by rw [hR₁, Function.update_of_ne hfs, hf]
  set R₂ := movedR R₁ f t₁ id (R₁ f) with hR₂
  have hR₂f : ∀ k, k ≠ f → k ≠ t₁ → R₂ k = R₁ k := fun k hk1 hk2 => by
    simp [hR₂, movedR, hk1, hk2]
  have hR₁t₁ : R₁ t₁ = [] := by rw [hR₁, Function.update_of_ne hs1.symm, h1]
  have hR₂t₁ : R₂ t₁ = (binSyms m x : List (Fin (A + 4))).reverse := by
    simp [hR₂, movedR, hR₁f, hR₁t₁]
  have hR₂f' : R₂ f = [] := by simp [hR₂, movedR, hf1]
  -- duplicate
  obtain ⟨v₃, hu₃, he₃⟩ := dupR_exec body (a := t₁) (b := t₂) (t := t₃) (t₂ := t₄)
    (by simp [h12, h13, h14, h23, h24, h34]) v₂ { S with R := R₂ }
    (by show R₂ t₃ = []; rw [hR₂f _ hf3.symm h13.symm, hR₁, Function.update_of_ne hs3.symm, h3])
    (by show R₂ t₄ = []; rw [hR₂f _ hf4.symm h14.symm, hR₁, Function.update_of_ne hs4.symm, h4])
  set R₃ := Function.update R₂ t₂ (R₂ t₁ ++ R₂ t₂) with hR₃
  have hR₂t₂ : R₂ t₂ = [] := by
    rw [hR₂f _ hf2.symm h12.symm, hR₁, Function.update_of_ne hs2.symm, h2]
  have hR₃t₂ : R₃ t₂ = (binSyms m x : List (Fin (A + 4))).reverse := by
    rw [hR₃, Function.update_self, hR₂t₁, hR₂t₂, List.append_nil]
  have hR₃f : ∀ k, k ≠ t₂ → R₃ k = R₂ k := fun k hk => by rw [hR₃, Function.update_of_ne hk]
  -- restore the field
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body t₁ f hf1.symm id v₃ { S with R := R₃ }
  set R₄ := movedR R₃ t₁ f id (R₃ t₁) with hR₄
  have hR₄f : ∀ k, k ≠ t₁ → k ≠ f → R₄ k = R₃ k := fun k hk1 hk2 => by
    simp [hR₄, movedR, hk1, hk2]
  have hR₄ff : R₄ f = binSyms m x := by
    simp [hR₄, movedR, hR₃f _ h12, hR₂t₁, hR₃f _ hf2, hR₂f']
  have hR₄t₁ : R₄ t₁ = [] := by simp [hR₄, movedR, hf1.symm]
  -- deliver the copy
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body t₂ sF hs2.symm id v₄ { S with R := R₄ }
  have hR₄t₂ : R₄ t₂ = (binSyms m x : List (Fin (A + 4))).reverse := by
    rw [hR₄f _ h12.symm hf2.symm, hR₃t₂]
  have hR₄sF : R₄ sF = binSyms pad 0 := by
    rw [hR₄f _ hs1 hfs.symm, hR₃f _ hs2, hR₂f _ hfs.symm hs1, hR₁, Function.update_self]
  refine ⟨v₅, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂
    (Exec.seq he₃ (Exec.seq he₄ he₅)))) ?_ ?_⟩
  · simp only [hml, hR₁f, hR₂t₁, hR₃t₂, hR₄t₂, List.length_reverse, length_binSyms,
      hR₃f _ h12]
    ring
  · congr 2
    funext k
    simp only [movedR, List.map_id, Function.update_apply]
    by_cases hk1 : k = sF
    · subst hk1
      simp only [↓reduceIte, hR₄t₂, hR₄sF, List.reverse_reverse]
      rw [binSyms_split, Nat.div_eq_of_lt hx]
    rw [if_neg hk1, if_neg hk1]
    by_cases hk2 : k = t₂
    · subst hk2; simp [h2]
    rw [if_neg hk2]
    by_cases hk3 : k = t₁
    · subst hk3; rw [hR₄t₁, h1]
    by_cases hk4 : k = f
    · subst hk4; rw [hR₄ff, hf]
    rw [hR₄f _ hk3 hk4, hR₃f _ hk2, hR₂f _ hk4 hk3, hR₁, Function.update_of_ne hk1]


/-- Push the output bit of the code automaton `C` (state in scan slot `st`) onto `acc`. -/
def pushCode (C : CAuto A nr 2) (st acc : Fin T) : Act T Q A U :=
  .push (.rt acc) (fun v => bitSymbol (decide (C.out (v.scan st) = 1))) .done

lemma pushCode_run {nr : ℕ} (C : CAuto A nr 2) (st acc : Fin T) (v : HS T Q A U)
    (S : Stacks T A) :
    (pushCode C st acc).run (mk v S) =
      mk v { S with
        R := Function.update S.R acc (bitSymbol (decide (C.out (v.scan st) = 1)) :: S.R acc) } := by
  simp [pushCode, Action.run, update_rt]
  rfl

/-- Pop `k` symbols of `acc`, OR-ing their bits into the flag, then push the flag onto `comp`. -/
def orPops (acc comp : Fin T) : ℕ → Act T Q A U
  | 0 => .push (.rt comp) (fun v => bitSymbol v.flag) .done
  | k + 1 => .pop (.rt acc) (fun v o => { v with flag := v.flag || symBit (o.getD blank) })
      (orPops acc comp k)

/-- The OR of the bits of `acc` onto `comp`. -/
def orAcc (acc comp : Fin T) (k : ℕ) : Act T Q A U :=
  .load (fun v => { v with flag := false }) (orPops acc comp k)

lemma orPops_run {acc comp : Fin T} (hac : acc ≠ comp) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), S.R acc = l →
      (orPops acc comp l.length).run (mk v S) =
        mk { v with flag := v.flag || l.any symBit }
          { S with
            R := Function.update (Function.update S.R acc []) comp
                  (bitSymbol (v.flag || l.any symBit) :: S.R comp) }
  | [], v, S, h => by
      simp only [List.length_nil, orPops, Action.run, List.any_nil, Bool.or_false, mk_var, mk_stk,
        get_rt, update_rt, store_mk]
      rw [← h, Function.update_eq_self]
      try rfl
  | x :: rest, v, S, h => by
      simp only [List.length_cons, orPops, Action.run, mk_var, mk_stk, get_rt, h, List.head?_cons,
        Option.getD_some, List.tail_cons, update_rt, store_mk]
      rw [orPops_run hac rest _ { S with R := Function.update S.R acc rest }
        (by simp)]
      simp only [List.any_cons, Function.update_idem, Function.update_of_ne hac.symm,
        Bool.or_assoc]

lemma orAcc_run {acc comp : Fin T} (hac : acc ≠ comp) (l : List (Fin (A + 4))) (v : HS T Q A U)
    (S : Stacks T A) (h : S.R acc = l) :
    (orAcc acc comp l.length).run (mk v S) =
      mk { v with flag := l.any symBit }
        { S with
          R := Function.update (Function.update S.R acc []) comp
                (bitSymbol (l.any symBit) :: S.R comp) } := by
  simp only [orAcc, Action.run, mk_var, mk_stk, store_mk]
  rw [orPops_run hac l { v with flag := false } S h]
  simp

/-- The code automaton reading one computed bit. -/
def cxBitAuto (A : ℕ) : CAuto A 1 2 where
  init := bitSymbol false
  step := fun _ col => bitSymbol (col 0)
  out := fun s => if symBit s then 1 else 0

lemma cxBitAuto_eval (A : ℕ) (b : Bool) : (cxBitAuto A).eval 1 ![b2n b] = if b then 1 else 0 := by
  simp [CAuto.eval, CAuto.run, cxBitAuto, b2n]
  cases b <;> simp

end Pieces

/-! ### The indicator of the exceptional set -/

section Indicator

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- The exceptional set in digit terms: a used digit of `T` (and of `U` when `useU`) is
`2^G - 1`, or a used guard of `Y` leaves the range. -/
def CBad (useU : Bool) (U T Y : Fin nf) (K ρ G n : ℕ) (i : ℕ) : Prop :=
  (∃ c < n, dig len T i / 2 ^ (c * G) % 2 ^ G = 2 ^ G - 1) ∨
    (useU = true ∧ ∃ c < n, dig len U i / 2 ^ (c * G) % 2 ^ G = 2 ^ G - 1) ∨
    ∃ c < n, ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len Y i) c

instance (useU : Bool) (U T Y : Fin nf) (K ρ G n i : ℕ) :
    Decidable (CBad len useU U T Y K ρ G n i) := by unfold CBad; infer_instance

/-- The indicator as a number. -/
def cbadN (useU : Bool) (U T Y : Fin nf) (K ρ G n : ℕ) (i : ℕ) : ℕ :=
  if CBad len useU U T Y K ρ G n i then 1 else 0

lemma cbadN_eq_b2n (useU : Bool) (U T Y : Fin nf) (K ρ G n i : ℕ) :
    cbadN len useU U T Y K ρ G n i = b2n (decide (CBad len useU U T Y K ρ G n i)) := by
  unfold cbadN b2n; split_ifs <;> simp_all

/-- The earlier-source exceptional set is `CBad` without `U`. -/
lemma cbad_false_iff_badE {T Y : Fin nf} {K ρ G n R S : ℕ} (U : Fin nf)
    (a : Fin (R * 2 ^ S)) :
    CBad len false U T Y K ρ G n a ↔ BadE len T Y K ρ G n a := by
  rw [badE_iff]
  unfold CBad
  simp only [Bool.false_eq_true, false_and, false_or]
  have hd : ∀ c, dig len T a / 2 ^ (c * G) % 2 ^ G = 2 ^ G - 1 ↔
      2 ^ G < digAt len G T c a + 2 := by
    intro c
    unfold digAt
    have := Nat.mod_lt (dig len T a / 2 ^ (c * G)) (show 0 < 2 ^ G by positivity)
    have h1 : 1 ≤ 2 ^ G := Nat.one_le_two_pow
    omega
  simp only [hd]

/-- The later-source exceptional set is `CBad` with `U`. -/
lemma cbad_true_iff_badL {U T Y : Fin nf} {K ρ G n R S : ℕ} (a : Fin (R * 2 ^ S)) :
    CBad len true U T Y K ρ G n a ↔ BadL len U T Y K ρ G n a := by
  unfold BadL GoodL
  rw [not_and_or, ← BadE, badE_iff]
  unfold CBad DigOK
  simp only [true_and]
  have hd : ∀ (D : Fin nf) c, dig len D a / 2 ^ (c * G) % 2 ^ G = 2 ^ G - 1 ↔
      2 ^ G < digAt len G D c a + 2 := by
    intro D c
    unfold digAt
    have := Nat.mod_lt (dig len D a / 2 ^ (c * G)) (show 0 < 2 ^ G by positivity)
    have h1 : 1 ≤ 2 ^ G := Nat.one_le_two_pow
    omega
  simp only [hd]
  push_neg
  simp only [Nat.lt_iff_add_one_le]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (by obtain ⟨c, hc, h⟩ := h; exact ⟨c, hc, by omega⟩)
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (by obtain ⟨c, hc, h⟩ := h; exact ⟨c, hc, by omega⟩))

end Indicator


/-! ### The preparation program -/

section Program

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U) {nf : ℕ}

/-- The registers of the preparation besides the field registers: the computed indicator, the
two masks and the padding count, three padded copies, four move scratches, the accumulator and
the two code-pass scratches. -/
inductive BReg where
  | comp | mD | mG | padR | sT | sU | sY | t₁ | t₂ | t₃ | t₄ | acc | ct | cu
  deriving DecidableEq

/-- A code pass followed by pushing its output bit onto `acc`. -/
def codePush {nr : ℕ} [NeZero nr] (rs tmps : Fin nr → Fin T) (st : Fin T) (C : CAuto A nr 2)
    (acc : Fin T) : Pr P T Q A U :=
  .seq (codePass rs tmps st C) (.act (pushCode C st acc))

/-- The exceptional-set indicator: copy `T` (and `U`) padded and `Y`, run the digit automaton on
the copies against the alternating mask and the guard automaton on `Y` against the high-guard
mask, OR the outputs into `comp`, clear the copies. -/
def badPrep (useU : Bool) (cf : Fin nf → Fin T) (fT fU fY : Fin nf) (ι : BReg → Fin T)
    (st : Fin T) : Pr P T Q A U :=
  .seq (uclear (ι .comp))
    (.seq (padCopy (ι .padR) (cf fT) (ι .sT) (ι .t₁) (ι .t₂) (ι .t₃) (ι .t₄))
      (.seq (if useU then padCopy (ι .padR) (cf fU) (ι .sU) (ι .t₁) (ι .t₂) (ι .t₃) (ι .t₄)
          else .act .done)
        (.seq (padCopy (ι .cu) (cf fY) (ι .sY) (ι .t₁) (ι .t₂) (ι .t₃) (ι .t₄))
          (.seq (codePush ![ι .sT, ι .mD] ![ι .ct, ι .cu] st (onesAuto A) (ι .acc))
            (.seq (if useU then codePush ![ι .sU, ι .mD] ![ι .ct, ι .cu] st (onesAuto A) (ι .acc)
                else .act .done)
              (.seq (codePush ![ι .sY, ι .mG] ![ι .ct, ι .cu] st (guardAuto A) (ι .acc))
                (.seq (.act (orAcc (ι .acc) (ι .comp) (if useU then 3 else 2)))
                  (.seq (uclear (ι .sT)) (.seq (uclear (ι .sU)) (uclear (ι .sY)))))))))))

/-- The step bound of the preparation. -/
def badPrepCost (L' nG c : ℕ) : ℕ := 2 * c + 44 * L' + 16 * nG + 80

/-- A conditional sub-program. -/
lemma exec_ite (b : Bool) (p : Pr P T Q A U) (v : HS T Q A U) (S : Stacks T A)
    (R' : Regs T A) (c : ℕ)
    (hp : b = true → ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c ∧
      Exec body p (mk v S) m (mk v' { S with R := R' })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c + 1 ∧
      Exec body (if b then p else .act .done) (mk v S) m
        (mk v' { S with R := if b then R' else S.R }) := by
  cases b
  · refine ⟨v, 1, rfl, by omega, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := Exec.act (body := body) (Action.done : Act T Q A U) (mk v S)
    rw [run_done] at this
    exact Exec.cast this rfl (by cases S; rfl)
  · obtain ⟨v', m, hu, hm, he⟩ := hp rfl
    exact ⟨v', m, hu, by omega, by simpa using he⟩

lemma ite_eq_one_iff (p : Prop) [Decidable p] :
    ((if p then (1 : Fin 2) else 0) = 1 ↔ p) := by
  split_ifs with h <;> simp [h]

lemma binSyms_one_b2n (b : Bool) : (binSyms 1 (b2n b) : List (Fin (A + 4))) = [bitSymbol b] := by
  cases b <;> rfl

/-- A code pass followed by pushing its output. -/
lemma codePush_exec {nr : ℕ} [NeZero nr] {rs tmps : Fin nr → Fin T} {st acc : Fin T}
    (h : CodeLayout rs tmps st) (C : CAuto A nr 2) (L : ℕ) (vals : Fin nr → ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hrs : ∀ r, S.R (rs r) = binSyms L (vals r))
    (htmps : ∀ r, S.R (tmps r) = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (codePush rs tmps st C acc) (mk v S) (6 * L + 5)
        (mk v' { S with
          R := Function.update S.R acc (bitSymbol (decide (C.eval L vals = 1)) :: S.R acc) }) := by
  obtain ⟨v₁, hu₁, hs₁, he₁⟩ := codePass_exec body h C L vals v S hrs htmps
  have he₂ := Exec.act (body := body) (pushCode C st acc) (mk v₁ S)
  rw [pushCode_run, hs₁] at he₂
  exact ⟨v₁, hu₁, Exec.cast (Exec.seq he₁ he₂) (by ring) rfl⟩


set_option maxHeartbeats 1000000 in
/-- **The preparation.** From the field registers at index `i` it writes the indicator
`cbadN … i` (one symbol) into `comp` and restores every other register. -/
theorem badPrep_exec (hA : 12 ≤ A) (useU : Bool) {cf : Fin nf → Fin T} {fT fU fY : Fin nf}
    {ι : BReg → Fin T} (hι : Function.Injective ι) {st : Fin T}
    (hcf : ∀ x f, ι x ≠ cf f) (hst : ∀ x, ι x ≠ st) (hcfst : ∀ f, cf f ≠ st)
    (hTY : cf fT ≠ cf fY) (hUY : useU = true → cf fU ≠ cf fY)
    (hTU : useU = true → cf fT ≠ cf fU) (len : Fin nf → ℕ) {K ρ G n : ℕ} (hG : 1 ≤ G)
    (hK : G + 3 ≤ K) (hρ : ρ < K) (hLT : len fT = n * G) (hLU : useU = true → len fU = n * G)
    (hLY : len fY = (n + 1) * K) (i : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hT : S.R (cf fT) = binSyms (len fT) (digit len fT i))
    (hU : useU = true → S.R (cf fU) = binSyms (len fU) (digit len fU i))
    (hY : S.R (cf fY) = binSyms (len fY) (digit len fY i))
    (hpad : (S.R (ι .padR)).length = (n + 1) * K - n * G)
    (hmD : S.R (ι .mD) = binSyms ((n + 1) * K) (altMask G ((n + 1) * K)))
    (hmG : S.R (ι .mG) = binSyms ((n + 1) * K) (highMask K ρ G n ((n + 1) * K)))
    (hsT : S.R (ι .sT) = []) (hsU : S.R (ι .sU) = []) (hsY : S.R (ι .sY) = [])
    (ht₁ : S.R (ι .t₁) = []) (ht₂ : S.R (ι .t₂) = []) (ht₃ : S.R (ι .t₃) = [])
    (ht₄ : S.R (ι .t₄) = []) (hacc : S.R (ι .acc) = []) (hct : S.R (ι .ct) = [])
    (hcu : S.R (ι .cu) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ badPrepCost ((n + 1) * K) (n * G) (S.R (ι .comp)).length ∧
      Exec body (badPrep useU cf fT fU fY ι st) (mk v S) m
        (mk v' { S with
          R := Function.update S.R (ι .comp) (binSyms 1 (cbadN len useU fU fT fY K ρ G n i)) }) := by
  have hcf' : ∀ x f, cf f ≠ ι x := fun x f => (hcf x f).symm
  have hne : ∀ {x y : BReg}, x ≠ y → ι x ≠ ι y := fun h => hι.ne h
  set L' := (n + 1) * K with hL'
  have hnGL : n * G ≤ L' := by
    rw [hL', Nat.succ_mul]
    exact le_trans (Nat.mul_le_mul_left n (by omega)) (Nat.le_add_right _ _)
  have hL1 : 1 ≤ L' := by rw [hL']; nlinarith
  have hρn : ρ + n * K ≤ L' := by rw [hL', Nat.succ_mul]; omega
  set xT := digit len fT i with hxT
  set xU := digit len fU i with hxU
  set xY := digit len fY i with hxY
  have hxTl : xT < 2 ^ (n * G) := by rw [hxT, ← hLT]; exact Nat.mod_lt _ (by positivity)
  have hxUl : useU = true → xU < 2 ^ (n * G) := fun h => by
    rw [hxU, ← hLU h]; exact Nat.mod_lt _ (by positivity)
  have hxYl : xY < 2 ^ L' := by rw [hxY, ← hLY]; exact Nat.mod_lt _ (by positivity)
  set pad := L' - n * G with hpaddef
  have hpad' : n * G + pad = L' := by omega
  -- step 1: clear the indicator
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body (ι .comp) v S
  set R₁ := Function.update S.R (ι .comp) [] with hR₁
  have hR₁f : ∀ k, k ≠ ι .comp → R₁ k = S.R k := fun k hk => by
    rw [hR₁, Function.update_of_ne hk]
  -- step 2: copy `T`
  obtain ⟨v₂, hu₂, he₂⟩ := padCopy_exec body (padR := ι .padR) (f := cf fT) (sF := ι .sT)
    (t₁ := ι .t₁) (t₂ := ι .t₂) (t₃ := ι .t₃) (t₄ := ι .t₄)
    (by simp [hι.eq_iff, hcf, hcf']) (hLT ▸ hxTl) v₁ { S with R := R₁ }
    (by show R₁ (cf fT) = _; rw [hR₁f _ (hcf' _ _), hT])
    (by show R₁ (ι .sT) = []; rw [hR₁f _ (hne (by decide)), hsT])
    (by show (R₁ (ι .padR)).length = pad; rw [hR₁f _ (hne (by decide)), hpad])
    (by show R₁ (ι .t₁) = []; rw [hR₁f _ (hne (by decide)), ht₁])
    (by show R₁ (ι .t₂) = []; rw [hR₁f _ (hne (by decide)), ht₂])
    (by show R₁ (ι .t₃) = []; rw [hR₁f _ (hne (by decide)), ht₃])
    (by show R₁ (ι .t₄) = []; rw [hR₁f _ (hne (by decide)), ht₄])
  rw [hLT, hpad'] at he₂
  set R₂ := Function.update R₁ (ι .sT) (binSyms L' xT : List (Fin (A + 4))) with hR₂
  have hR₂f : ∀ k, k ≠ ι .sT → R₂ k = R₁ k := fun k hk => by
    rw [hR₂, Function.update_of_ne hk]
  -- step 3: copy `U`
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := exec_ite body useU _ v₂ { S with R := R₂ }
    (Function.update R₂ (ι .sU) (binSyms L' xU : List (Fin (A + 4)))) (12 * (n * G) + 4 * pad + 16)
    (fun hu => by
      obtain ⟨v', hu', he'⟩ := padCopy_exec body (padR := ι .padR) (f := cf fU) (sF := ι .sU)
        (t₁ := ι .t₁) (t₂ := ι .t₂) (t₃ := ι .t₃) (t₄ := ι .t₄)
        (by simp [hι.eq_iff, hcf, hcf']) (hLU hu ▸ hxUl hu) v₂ { S with R := R₂ }
        (by show R₂ (cf fU) = _; rw [hR₂f _ (hcf' _ _), hR₁f _ (hcf' _ _), hU hu])
        (by show R₂ (ι .sU) = []; rw [hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), hsU])
        (by show (R₂ (ι .padR)).length = pad
            rw [hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), hpad])
        (by show R₂ (ι .t₁) = []; rw [hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), ht₁])
        (by show R₂ (ι .t₂) = []; rw [hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), ht₂])
        (by show R₂ (ι .t₃) = []; rw [hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), ht₃])
        (by show R₂ (ι .t₄) = []; rw [hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), ht₄])
      rw [hLU hu, hpad'] at he'
      exact ⟨v', _, hu', le_rfl, he'⟩)
  set R₃ : Regs T A := if useU then
    Function.update R₂ (ι .sU) (binSyms L' xU : List (Fin (A + 4))) else R₂ with hR₃
  have hR₃f : ∀ k, k ≠ ι .sU → R₃ k = R₂ k := fun k hk => by
    rw [hR₃]; split_ifs
    · rw [Function.update_of_ne hk]
    · rfl
  have hR₃sU : R₃ (ι .sU) = if useU then (binSyms L' xU : List (Fin (A + 4))) else [] := by
    rw [hR₃]; split_ifs
    · rw [Function.update_self]
    · rw [hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), hsU]
  -- step 4: copy `Y`
  have hR₃cu : R₃ (ι .cu) = [] := by
    rw [hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), hcu]
  obtain ⟨v₄, hu₄, he₄⟩ := padCopy_exec body (padR := ι .cu) (f := cf fY) (sF := ι .sY)
    (t₁ := ι .t₁) (t₂ := ι .t₂) (t₃ := ι .t₃) (t₄ := ι .t₄)
    (by simp [hι.eq_iff, hcf, hcf']) (hLY ▸ hxYl) v₃ { S with R := R₃ }
    (by show R₃ (cf fY) = _
        rw [hR₃f _ (hcf' _ _), hR₂f _ (hcf' _ _), hR₁f _ (hcf' _ _), hY])
    (by show R₃ (ι .sY) = []
        rw [hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), hsY])
    (by show (R₃ (ι .cu)).length = 0; rw [hR₃cu]; rfl)
    (by show R₃ (ι .t₁) = []
        rw [hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), ht₁])
    (by show R₃ (ι .t₂) = []
        rw [hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), ht₂])
    (by show R₃ (ι .t₃) = []
        rw [hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), ht₃])
    (by show R₃ (ι .t₄) = []
        rw [hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)), hR₁f _ (hne (by decide)), ht₄])
  rw [hLY, Nat.add_zero] at he₄
  set R₄ := Function.update R₃ (ι .sY) (binSyms L' xY : List (Fin (A + 4))) with hR₄
  have hR₄f : ∀ k, k ≠ ι .sY → R₄ k = R₃ k := fun k hk => by
    rw [hR₄, Function.update_of_ne hk]
  -- the code layout of the three code passes
  have hlay : ∀ a b : BReg, a ≠ b → a ≠ .ct → a ≠ .cu → b ≠ .ct → b ≠ .cu →
      CodeLayout ![ι a, ι b] ![ι .ct, ι .cu] st := fun a b hab ha1 ha2 hb1 hb2 =>
    ⟨fun r r' h => by fin_cases r <;> fin_cases r' <;> simp_all [hι.eq_iff],
      fun r r' h => by fin_cases r <;> fin_cases r' <;> simp_all [hι.eq_iff],
      fun r r' => by fin_cases r <;> fin_cases r' <;> simp [hι.eq_iff, ha1, ha2, hb1, hb2],
      fun r => by fin_cases r <;> simp [hst],
      fun r => by fin_cases r <;> simp [hst]⟩
  have hR₄mD : R₄ (ι .mD) = binSyms L' (altMask G L') := by
    rw [hR₄f _ (hne (by decide)), hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)),
      hR₁f _ (hne (by decide)), hmD]
  have hR₄mG : R₄ (ι .mG) = binSyms L' (highMask K ρ G n L') := by
    rw [hR₄f _ (hne (by decide)), hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)),
      hR₁f _ (hne (by decide)), hmG]
  have hR₄ct : R₄ (ι .ct) = [] := by
    rw [hR₄f _ (hne (by decide)), hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)),
      hR₁f _ (hne (by decide)), hct]
  have hR₄cu : R₄ (ι .cu) = [] := by rw [hR₄f _ (hne (by decide)), hR₃cu]
  have hR₄sT : R₄ (ι .sT) = binSyms L' xT := by
    rw [hR₄f _ (hne (by decide)), hR₃f _ (hne (by decide)), hR₂, Function.update_self]
  have hR₄sU : R₄ (ι .sU) = if useU then (binSyms L' xU : List (Fin (A + 4))) else [] := by
    rw [hR₄f _ (hne (by decide)), hR₃sU]
  have hR₄sY : R₄ (ι .sY) = binSyms L' xY := by rw [hR₄, Function.update_self]
  have hR₄acc : R₄ (ι .acc) = [] := by
    rw [hR₄f _ (hne (by decide)), hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)),
      hR₁f _ (hne (by decide)), hacc]
  -- step 5: the digit automaton on `T`
  set d₁ := decide ((onesAuto A).eval L' ![xT, altMask G L'] = 1) with hd₁
  obtain ⟨v₅, hu₅, he₅⟩ := codePush_exec body (acc := ι .acc)
    (hlay .sT .mD (by decide) (by decide) (by decide) (by decide) (by decide)) (onesAuto A) L'
    ![xT, altMask G L'] v₄ { S with R := R₄ }
    (fun r => by fin_cases r <;> simp [hR₄sT, hR₄mD])
    (fun r => by fin_cases r <;> simp [hR₄ct, hR₄cu])
  set R₅ := Function.update R₄ (ι .acc) (bitSymbol d₁ :: R₄ (ι .acc)) with hR₅
  have hR₅f : ∀ k, k ≠ ι .acc → R₅ k = R₄ k := fun k hk => by
    rw [hR₅, Function.update_of_ne hk]
  -- step 6: the digit automaton on `U`
  set d₂ := decide ((onesAuto A).eval L' ![xU, altMask G L'] = 1) with hd₂
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := exec_ite body useU _ v₅ { S with R := R₅ }
    (Function.update R₅ (ι .acc) (bitSymbol d₂ :: R₅ (ι .acc))) (6 * L' + 5)
    (fun hu => by
      obtain ⟨v', hu', he'⟩ := codePush_exec body (acc := ι .acc)
        (hlay .sU .mD (by decide) (by decide) (by decide) (by decide) (by decide)) (onesAuto A) L'
        ![xU, altMask G L'] v₅ { S with R := R₅ }
        (fun r => by
          fin_cases r
          · show R₅ (ι .sU) = _; rw [hR₅f _ (hne (by decide)), hR₄sU, if_pos hu]; rfl
          · show R₅ (ι .mD) = _; rw [hR₅f _ (hne (by decide)), hR₄mD]; rfl)
        (fun r => by
          fin_cases r
          · show R₅ (ι .ct) = _; rw [hR₅f _ (hne (by decide)), hR₄ct]
          · show R₅ (ι .cu) = _; rw [hR₅f _ (hne (by decide)), hR₄cu])
      exact ⟨v', _, hu', le_rfl, he'⟩)
  set R₆ : Regs T A := if useU then
    Function.update R₅ (ι .acc) (bitSymbol d₂ :: R₅ (ι .acc)) else R₅ with hR₆
  have hR₆f : ∀ k, k ≠ ι .acc → R₆ k = R₅ k := fun k hk => by
    rw [hR₆]; split_ifs
    · rw [Function.update_of_ne hk]
    · rfl
  have hR₆acc : R₆ (ι .acc) =
      if useU then [bitSymbol d₂, bitSymbol d₁] else [bitSymbol d₁] := by
    rw [hR₆]; split_ifs
    · rw [Function.update_self, hR₅, Function.update_self, hR₄acc]
    · rw [hR₅, Function.update_self, hR₄acc]
  -- step 7: the guard automaton on `Y`
  set d₃ := decide ((guardAuto A).eval L' ![xY, highMask K ρ G n L'] = 1) with hd₃
  obtain ⟨v₇, hu₇, he₇⟩ := codePush_exec body (acc := ι .acc)
    (hlay .sY .mG (by decide) (by decide) (by decide) (by decide) (by decide)) (guardAuto A) L'
    ![xY, highMask K ρ G n L'] v₆ { S with R := R₆ }
    (fun r => by
      fin_cases r
      · show R₆ (ι .sY) = _
        rw [hR₆f _ (hne (by decide)), hR₅f _ (hne (by decide)), hR₄sY]; rfl
      · show R₆ (ι .mG) = _
        rw [hR₆f _ (hne (by decide)), hR₅f _ (hne (by decide)), hR₄mG]; rfl)
    (fun r => by
      fin_cases r
      · show R₆ (ι .ct) = _; rw [hR₆f _ (hne (by decide)), hR₅f _ (hne (by decide)), hR₄ct]
      · show R₆ (ι .cu) = _; rw [hR₆f _ (hne (by decide)), hR₅f _ (hne (by decide)), hR₄cu])
  set R₇ := Function.update R₆ (ι .acc) (bitSymbol d₃ :: R₆ (ι .acc)) with hR₇
  have hR₇f : ∀ k, k ≠ ι .acc → R₇ k = R₆ k := fun k hk => by
    rw [hR₇, Function.update_of_ne hk]
  have hR₇acc : R₇ (ι .acc) = bitSymbol d₃ ::
      (if useU then [bitSymbol d₂, bitSymbol d₁] else [bitSymbol d₁]) := by
    rw [hR₇, Function.update_self, hR₆acc]
  -- step 8: the OR onto `comp`
  set lacc : List (Fin (A + 4)) := bitSymbol d₃ ::
    (if useU then [bitSymbol d₂, bitSymbol d₁] else [bitSymbol d₁]) with hlacc
  have hlen : lacc.length = if useU then 3 else 2 := by rw [hlacc]; cases useU <;> rfl
  have he₈ := Exec.act (body := body) (orAcc (ι .acc) (ι .comp) lacc.length)
    (mk v₇ { S with R := R₇ })
  rw [orAcc_run (hne (by decide)) lacc v₇ _ hR₇acc, hlen] at he₈
  set bad := lacc.any symBit with hbad
  have hR₇comp : R₇ (ι .comp) = [] := by
    rw [hR₇f _ (hne (by decide)), hR₆f _ (hne (by decide)), hR₅f _ (hne (by decide)),
      hR₄f _ (hne (by decide)), hR₃f _ (hne (by decide)), hR₂f _ (hne (by decide)), hR₁,
      Function.update_self]
  set R₈ := Function.update (Function.update R₇ (ι .acc) []) (ι .comp)
    (bitSymbol bad :: R₇ (ι .comp)) with hR₈
  have hR₈f : ∀ k, k ≠ ι .acc → k ≠ ι .comp → R₈ k = R₇ k := fun k h1 h2 => by
    rw [hR₈, Function.update_of_ne h2, Function.update_of_ne h1]
  -- steps 9–11: clear the copies
  obtain ⟨v₉, hu₉, he₉⟩ := uclear_exec body (ι .sT) { v₇ with flag := bad } { S with R := R₈ }
  set R₉ := Function.update R₈ (ι .sT) [] with hR₉
  obtain ⟨v₁₀, hu₁₀, he₁₀⟩ := uclear_exec body (ι .sU) v₉ { S with R := R₉ }
  set R₁₀ := Function.update R₉ (ι .sU) [] with hR₁₀
  obtain ⟨v₁₁, hu₁₁, he₁₁⟩ := uclear_exec body (ι .sY) v₁₀ { S with R := R₁₀ }
  set R₁₁ := Function.update R₁₀ (ι .sY) [] with hR₁₁
  -- the indicator
  have hbadN : (binSyms 1 (cbadN len useU fU fT fY K ρ G n i) : List (Fin (A + 4))) =
      [bitSymbol bad] := by
    rw [cbadN_eq_b2n, binSyms_one_b2n]
    congr 1
    rw [hbad, hlacc]
    have hd₁' : d₁ = decide (∃ c < n, dig len fT i / 2 ^ (c * G) % 2 ^ G = 2 ^ G - 1) := by
      rw [hd₁, onesAuto_eval_digits hA hG xT (altMask G L') L' n
        (fun t ht => testBit_altMask G L' t ht) hnGL hL1 hxTl]
      exact decide_eq_decide.mpr (ite_eq_one_iff _)
    have hd₃' : d₃ = decide (∃ c < n, ¬ GuardOK K ρ (2 ^ (G + 1)) (dig len fY i) c) := by
      rw [hd₃, guardAuto_eval hA hK xY (highMask K ρ G n L') L'
        (fun t ht => testBit_highMask K ρ G n L' t ht) hρn]
      apply decide_eq_decide.mpr
      rw [ite_eq_one_iff]
      have hcL : ∀ c < n, ρ + c * K + K ≤ L' := fun c hc => by
        have := Nat.mul_le_mul_right K (show c + 1 ≤ n by omega)
        rw [Nat.add_mul, one_mul] at this
        omega
      constructor
      · rintro ⟨c, hc, h⟩
        exact ⟨c, hc, (highAll_iff_not_guardOK hK xY c L' (hcL c hc)).1 h⟩
      · rintro ⟨c, hc, h⟩
        exact ⟨c, hc, (highAll_iff_not_guardOK hK xY c L' (hcL c hc)).2 h⟩
    cases useU
    · simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons, List.any_nil, symBit_bitSymbol,
        Bool.or_false]
      rw [hd₁', hd₃']
      unfold CBad
      simp only [Bool.false_eq_true, false_and, false_or]
      congr 1
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.comm
    · have hd₂' : d₂ = decide (∃ c < n, dig len fU i / 2 ^ (c * G) % 2 ^ G = 2 ^ G - 1) := by
        rw [hd₂, onesAuto_eval_digits hA hG xU (altMask G L') L' n
          (fun t ht => testBit_altMask G L' t ht) hnGL hL1 (hxUl rfl)]
        exact decide_eq_decide.mpr (ite_eq_one_iff _)
      simp only [↓reduceIte, List.any_cons, List.any_nil, symBit_bitSymbol, Bool.or_false]
      rw [hd₁', hd₂', hd₃']
      unfold CBad
      simp only [true_and]
      congr 1
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨fun h => h.elim (fun h => Or.inr (Or.inr h))
          (fun h => h.elim (fun h => Or.inr (Or.inl h)) Or.inl),
        fun h => h.elim (fun h => Or.inr (Or.inr h))
          (fun h => h.elim (fun h => Or.inr (Or.inl h)) Or.inl)⟩
  -- assembly
  refine ⟨v₁₁, _, by simp only [hu₁₁, hu₁₀, hu₉, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ (Exec.seq he₇ (Exec.seq he₈ (Exec.seq he₉ (Exec.seq he₁₀ he₁₁)))))))))) rfl
      ?_⟩
  · -- the cost
    have h8 : (R₈ (ι .sT)).length = L' := by
      rw [hR₈f _ (hne (by decide)) (hne (by decide)), hR₇f _ (hne (by decide)),
        hR₆f _ (hne (by decide)), hR₅f _ (hne (by decide)), hR₄sT, length_binSyms]
    have h9 : (R₉ (ι .sU)).length ≤ L' := by
      rw [hR₉, Function.update_of_ne (hne (by decide)), hR₈f _ (hne (by decide)) (hne (by decide)),
        hR₇f _ (hne (by decide)), hR₆f _ (hne (by decide)), hR₅f _ (hne (by decide)), hR₄sU]
      split_ifs <;> simp [length_binSyms]
    have h10 : (R₁₀ (ι .sY)).length = L' := by
      rw [hR₁₀, Function.update_of_ne (hne (by decide)), hR₉,
        Function.update_of_ne (hne (by decide)), hR₈f _ (hne (by decide)) (hne (by decide)),
        hR₇f _ (hne (by decide)), hR₆f _ (hne (by decide)), hR₅f _ (hne (by decide)), hR₄sY,
        length_binSyms]
    simp only [h8, h10]
    unfold badPrepCost
    have hpadL : pad ≤ L' := by omega
    omega
  · -- the registers
    congr 2
    funext k
    by_cases hk1 : k = ι .comp
    · subst hk1
      rw [hbadN, Function.update_self, hR₁₁, Function.update_of_ne (hne (by decide)), hR₁₀,
        Function.update_of_ne (hne (by decide)), hR₉, Function.update_of_ne (hne (by decide)),
        hR₈, Function.update_self, hR₇comp]
    rw [Function.update_of_ne hk1]
    by_cases hk2 : k = ι .sY
    · subst hk2; rw [hR₁₁, Function.update_self, hsY]
    rw [hR₁₁, Function.update_of_ne hk2]
    by_cases hk3 : k = ι .sU
    · subst hk3; rw [hR₁₀, Function.update_self, hsU]
    rw [hR₁₀, Function.update_of_ne hk3]
    by_cases hk4 : k = ι .sT
    · subst hk4; rw [hR₉, Function.update_self, hsT]
    rw [hR₉, Function.update_of_ne hk4]
    by_cases hk5 : k = ι .acc
    · subst hk5
      rw [hR₈, Function.update_of_ne hk1, Function.update_self, hacc]
    rw [hR₈f _ hk5 hk1, hR₇f _ hk5, hR₆f _ hk5, hR₅f _ hk5, hR₄f _ hk2, hR₃f _ hk3, hR₂f _ hk4,
      hR₁f _ hk1]


/-- The scratch registers of the preparation. -/
def scrB (ι : BReg → Fin T) : Fin 9 → Fin T :=
  ![ι .sT, ι .sU, ι .sY, ι .t₂, ι .t₃, ι .t₄, ι .acc, ι .ct, ι .cu]

/-- The parameter registers of the preparation. -/
def prmB (ι : BReg → Fin T) : Fin 3 → Fin T := ![ι .mD, ι .mG, ι .padR]

/-- The parameter constants. -/
def prmB₀ (K ρ G n : ℕ) : Fin 3 → List (Fin (A + 4)) :=
  ![binSyms ((n + 1) * K) (altMask G ((n + 1) * K)),
    binSyms ((n + 1) * K) (highMask K ρ G n ((n + 1) * K)),
    List.replicate ((n + 1) * K - n * G) tick]

/-- **The preparation contract** of the prepared repair machine: one computed register `comp`
of length `1` holding the indicator of `CBad`. -/
theorem badPrep_spec (hA : 12 ≤ A) (useU : Bool) {cf : Fin nf → Fin T} {fT fU fY : Fin nf}
    {ι : BReg → Fin T} (hι : Function.Injective ι) {st : Fin T}
    (hcf : ∀ x f, ι x ≠ cf f) (hst : ∀ x, ι x ≠ st) (hcfst : ∀ f, cf f ≠ st)
    (hTY : cf fT ≠ cf fY) (hUY : useU = true → cf fU ≠ cf fY)
    (hTU : useU = true → cf fT ≠ cf fU) (len : Fin nf → ℕ) {K ρ G n : ℕ} (hG : 1 ≤ G)
    (hK : G + 3 ≤ K) (hρ : ρ < K) (hLT : len fT = n * G) (hLU : useU = true → len fU = n * G)
    (hLY : len fY = (n + 1) * K) :
    PrepSpec body (badPrep useU cf fT fU fY ι st) cf len 1 ![ι .comp] ![ι .t₁]
      ![.inr (cbadN len useU fU fT fY K ρ G n)] (scrB ι) (prmB ι) (prmB₀ K ρ G n)
      (badPrepCost ((n + 1) * K) (n * G) 1) where
  run := by
    intro i v S hI
    obtain ⟨hfld, hcomp, htmps, hscr, hprm⟩ := hI
    have hc1 : (S.R (ι .comp)).length = 1 := hcomp 0 _ rfl
    obtain ⟨v', m, hu, hm, he⟩ := badPrep_exec body hA useU hι hcf hst hcfst hTY hUY hTU len hG hK
      hρ hLT hLU hLY i v S (hfld fT) (fun _ => hfld fU) (hfld fY)
      (by have := hprm 2; simp [prmB, prmB₀] at this; rw [this]; simp)
      (by have := hprm 0; simpa [prmB, prmB₀] using this)
      (by have := hprm 1; simpa [prmB, prmB₀] using this)
      (hscr 0) (hscr 1) (hscr 2) (htmps 0) (hscr 3) (hscr 4) (hscr 5) (hscr 6) (hscr 7) (hscr 8)
    rw [hc1] at hm
    refine ⟨v', _, m, hu, hm, he, ?_, ?_⟩
    · intro r g hr
      fin_cases r
      simp only [Matrix.cons_val_zero, Matrix.cons_val_fin_one, Sum.inr.injEq] at hr
      subst hr
      simp
    · intro k hk
      exact Function.update_of_ne (hk 0 _ rfl) _ _

end Program


/-! ### The compact repair pass -/

section RepairPass

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U) {nf : ℕ}

/-- The code of the prepared repair is the indicator of `CBad`. -/
lemma idxCodeP_cxBitAuto (len : Fin nf → ℕ) (useU : Bool) (fU fT fY : Fin nf) (K ρ G n : ℕ)
    (j : ℕ) :
    idxCodeP (cxBitAuto A) 1 len ![.inr (cbadN len useU fU fT fY K ρ G n)] j =
      if CBad len useU fU fT fY K ρ G n j then 1 else 0 := by
  unfold idxCodeP
  have hv : (regValP len ![.inr (cbadN len useU fU fT fY K ρ G n)] j) =
      ![b2n (decide (CBad len useU fU fT fY K ρ G n j))] := by
    funext r
    fin_cases r
    simp [regValP, cbadN_eq_b2n]
  rw [hv, cxBitAuto_eval]
  by_cases h : CBad len useU fU fT fY K ρ G n j <;> simp [h]

set_option maxHeartbeats 1000000 in
/-- **The compact repair pass.** On the stream moved by an actual permutation `πS` that agrees
with the ideal permutation `πT` off the exceptional set `CBad` (an invariant of `πT`), the
prepared repair machine with the indicator preparation returns the stream moved by `πT`, keys
stripped. -/
theorem compactRepair_exec (hA : 12 ≤ A) (useU : Bool) {cf : Fin nf → Fin T} {fT fU fY : Fin nf}
    {ι : BReg → Fin T} (hι : Function.Injective ι) {st : Fin T}
    (hcf : ∀ x f, ι x ≠ cf f) (hst : ∀ x, ι x ≠ st) (hcfst : ∀ f, cf f ≠ st)
    (hTY : cf fT ≠ cf fY) (hUY : useU = true → cf fU ≠ cf fY)
    (hTU : useU = true → cf fT ≠ cf fU) (len : Fin nf → ℕ) {K ρ G n : ℕ} (hG : 1 ≤ G)
    (hK : G + 3 ≤ K) (hρ : ρ < K) (hLT : len fT = n * G) (hLU : useU = true → len fU = n * G)
    (hLY : len fY = (n + 1) * K)
    {src gR bR g b ctrKB ctrB ctrK cnt tmp : Fin T} {ss : Fin 4 → Fin T}
    (h : RepairLayoutP src gR bR g b ctrKB ctrB ctrK cnt tmp st cf len 1 ![ι .comp] ![ι .t₁]
      ![.inr (cbadN len useU fU fT fY K ρ G n)] (scrB ι) (prmB ι) ss)
    {M k B : ℕ} (hk : M ≤ 2 ^ k) (hB : 1 ≤ B) {πS πT : Equiv.Perm (Fin M)}
    (hT : ∀ x : Fin M, CBad len useU fU fT fY K ρ G n (πT x) ↔ CBad len useU fU fT fY K ρ G n x)
    (agree : ∀ x : Fin M, ¬ CBad len useU fU fT fY K ρ G n x → πS x = πT x)
    (l : List (List (Fin (A + 4)))) (hl : l.length = M) (hlB : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = (moveRecs πS (keyRecs k πT l)).flatten)
    (hgR : S.R gR = []) (hbR : S.R bR = []) (hg : S.R g = []) (hb : S.R b = [])
    (hctr : (S.R ctrKB).length = k + B) (hctrB : (S.R ctrB).length = B)
    (hctrK : (S.R ctrK).length = k) (hcnt : (S.R cnt).length = M) (htmp : S.R tmp = [])
    (hss : ∀ r, S.R (ss r) = [])
    (hI : IdxStateP cf len 1 ![ι .comp] ![ι .t₁] ![.inr (cbadN len useU fU fT fY K ρ G n)]
      (scrB ι) (prmB ι) (prmB₀ K ρ G n) S.R 0) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ M * (2 * badPrepCost ((n + 1) * K) (n * G) 1 + 16 * (k + B) + 12 + 8 * (∑ f, len f) +
          8 * nf + 39) +
        k * (Fintype.card {j : Fin M // CBad len useU fU fT fY K ρ G n j} *
          (12 * k + 6 * B + 13)) + 10 * k + 8 * (∑ f, len f) + 8 * nf + 18 ∧
      Exec body (repairAtP (badPrep useU cf fT fU fY ι st) src gR bR g b ctrKB ctrB ctrK cnt tmp st
        cf ![ι .comp] ![ι .t₁] ss (cxBitAuto A)) (mk v S) m (mk v' { S with R := R' }) ∧
      R' src = (moveRecs πT l).flatten ∧ (R' (ι .comp)).length = 1 ∧
      ∀ x, x ≠ src → x ≠ ι .comp → R' x = S.R x := by
  set X := moveRecs πS (keyRecs k πT l) with hX
  set Y := moveRecs πT (keyRecs k πT l) with hY
  set code := idxCodeP (cxBitAuto A) 1 len ![.inr (cbadN len useU fU fT fY K ρ G n)] with hcodedef
  have hcode : ∀ j : Fin M, code j =
      if (fun j : Fin M => CBad len useU fU fT fY K ρ G n j) j then 1 else 0 :=
    fun j => idxCodeP_cxBitAuto len useU fU fT fY K ρ G n j
  have hXl : X.length = M := length_moveRecs _ _
  have hYl : Y.length = M := length_moveRecs _ _
  have hXB : ∀ r ∈ X, r.length = k + B :=
    moveRecs_length_mem _ _ (length_keyRecs _ _ _) (keyRecs_length_mem k B πT l hl hlB)
  have hYB : ∀ r ∈ Y, r.length = k + B :=
    moveRecs_length_mem _ _ (length_keyRecs _ _ _) (keyRecs_length_mem k B πT l hl hlB)
  have hgood := repair_good_refl hcode hT agree k l
  have hbad := repair_bad_refl hcode hT agree k hk l
  obtain ⟨v', R', m, hu, hm, he, hsrc', hcomp', hoth⟩ := repairAtP_exec body
    (badPrep_spec body hA useU hι hcf hst hcfst hTY hUY hTU len hG hK hρ hLT hLU hLY) h
    (cxBitAuto A) hB X Y (hXl.trans hYl.symm) hXB hYB hgood hbad v S hsrc hgR hbR hg hb hctr hctrB
    hctrK (hcnt.trans hXl.symm) htmp hss hI
  refine ⟨v', R', m, hu, ?_, he, ?_, hcomp' 0 _ rfl, fun x hx hxc => hoth x hx ?_⟩
  · rw [hXl, codeRecs_bad_refl hcode X hXl, List.length_map, length_badRanks_refl] at hm
    exact hm
  · rw [hsrc', hY, map_drop_moveRecs_keyRecs]
  · intro r g _
    fin_cases r
    exact hxc.symm

end RepairPass

end IntegerMultBounds.MathlibTM2.Node
