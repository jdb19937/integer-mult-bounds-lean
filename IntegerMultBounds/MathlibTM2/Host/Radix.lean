module

public import IntegerMultBounds.MathlibTM2.Host.Route
public import IntegerMultBounds.MathlibTM2.Host.Auto
public import IntegerMultBounds.Machine.RadixSort

/-!
# Stable LSD radix sort of fixed-length records on host registers

A register holds `recs.flatten` for a list `recs` of records, each a list of `B` symbols, with the
first symbol of the first record on top. Key bit `j` of a record `rec` is `symBit (rec.getD j 0)`.

## One pass

`radixPass src out ctr ctmp tc ttmp buf b0 b1 ck` stably partitions the records in `src` by key
bit `t`, where `t` is the length of the counter register `tc`, and leaves
`(RadixSort.pass (fun rec => symBit (rec.getD t 0)) recs).flatten` on top of `out` in forward
order. Registers:

* `src`: the input stream (left empty, unless `out = src`);
* `ctr`: `B` symbols (the record length), with the empty temp `ctmp`;
* `tc`: `t < B` symbols (the key index), with the empty temp `ttmp`;
* `buf`: an empty buffer for the first `t` symbols of a record;
* `b0`, `b1`: the empty buckets of key bit `false` and `true`;
* `out`: the destination, distinct from all registers above except possibly `src`;
* `ck`: the scan slot that holds the key symbol of the current record.

Each record is processed by `recordStep`: `keyBlock` moves its first `t` symbols onto `buf`
(counted by `tc`) and copies the next symbol, the key symbol, into `scan ck`; `moveR` moves
`buf` back onto `src`, restoring the record; then an `xferBlock` counted by `ctr` moves the
whole record onto the bucket selected by `symBit (scan ck)` (via `bitSel`). Bucket `b` ends with
the reversal of the flattened records of key bit `b`; moving `b1` and then `b0` onto `out`
concatenates them in forward order, false bucket first. Every counter, temp and bucket is
restored, every other register is unchanged, and `user` is kept; the scratch fields `flag`,
`sym` and `scan` end unspecified.

`radixPass_exec`: at most `6 * n * B + 6 * n * t + 13 * n + 6` steps for `n` records.
`radixPass_exec_self` is the in-place case `out = src`.

## Full sort

`radixSort src ctr ctmp tc ttmp buf b0 b1 ck kc` runs in-place passes for bits
`0, 1, …, K' - 1`, where `K'` is the length of the counter register `kc`. The pass counter `tc`
starts empty; after each pass one symbol moves from `kc` onto `tc`, and a final `moveR` moves
`tc` back onto `kc`. The result on `src` is
`(RadixSort.sort (fun rec j => symBit (rec.getD j 0)) K' recs).flatten`.

`radixSort_exec`: for `K' ≤ K ≤ B`, at most
`K' * (6 * n * B + 6 * n * K + 13 * n + 6) + 4 * K' + 4` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Records and buckets -/

/-- A list of records of length `B` flattens to `B` symbols per record. -/
lemma length_flatten_of_length {α : Type} {B : ℕ} :
    ∀ (L : List (List α)), (∀ r ∈ L, r.length = B) → L.flatten.length = L.length * B
  | [], _ => by simp
  | r :: L, h => by
      rw [List.flatten_cons, List.length_append, h r List.mem_cons_self,
        length_flatten_of_length L (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]
      simp only [List.length_cons]
      ring

/-- The bucket index of a key symbol value: `1` for the bit symbol of `true`, else `0`. -/
def bitSel (n : ℕ) : Fin 2 := if n = 2 then 1 else 0

/-- The two buckets as a family over `Fin 2`. -/
def bucketOf (b0 b1 : Fin T) (d : Fin 2) : Fin T := if d = 1 then b1 else b0

lemma bucketOf_bitSel (b0 b1 : Fin T) (x : Fin (A + 4)) :
    bucketOf b0 b1 (bitSel x.val) = if symBit x then b1 else b0 := by
  by_cases h : x.val = 2
  · have hx : symBit x = true := by simp [symBit, bitSymbol, Fin.ext_iff, h]
    simp [bucketOf, bitSel, h, hx]
  · have hx : symBit x = false := by simp [symBit, bitSymbol, Fin.ext_iff, h]
    simp [bucketOf, bitSel, h, hx]

/-! ### One record -/

/-- Copy the top symbol of register `src` into scan slot `ck`. -/
def peekKey (src ck : Fin T) : Act T Q A U :=
  .peek (.rt src) (fun v o => { v with scan := Function.update v.scan ck (o.getD blank) }) .done

lemma peekKey_run (src ck : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (peekKey src ck : Act T Q A U).run (mk v S) =
      mk { v with scan := Function.update v.scan ck ((S.R src).head?.getD blank) } S := rfl

/-- Move the first `|tc|` symbols of `src` onto `buf` (counted by `tc` with temp `ttmp`), then
copy the next symbol of `src`, the key symbol, into scan slot `ck`. -/
def keyBlock (src buf tc ttmp ck : Fin T) : Pr P T Q A U :=
  xferBlock (fun _ : Fin 1 => src) (fun _ => buf) tc ttmp ck 1 (fun _ => 0) (peekKey src ck)

/-- One record: read its key symbol with `keyBlock`, move the buffered prefix back onto `src`,
then move the whole record (`|ctr|` symbols) onto the bucket of its key bit, and record in `flag`
whether `src` is nonempty. -/
def recordStep (src ctr ctmp tc ttmp buf b0 b1 ck : Fin T) : Pr P T Q A U :=
  .seq (keyBlock src buf tc ttmp ck)
    (.seq (moveR buf src id)
      (xferBlock (fun _ : Fin 2 => src) (bucketOf b0 b1) ctr ctmp ck 1 bitSel (peekR src)))

/-- One record of `B` symbols with key index `t < B`, in `4 * B + 6 * t + 12` steps: the record
leaves `src` and its reversal is pushed onto the bucket of its key bit; every other register is
unchanged. -/
theorem recordStep_exec (src ctr ctmp tc ttmp buf b0 b1 ck : Fin T)
    (hreg : [src, ctr, ctmp, tc, ttmp, buf, b0, b1].Nodup) {B t : ℕ} (htB : t < B)
    (r rest : List (Fin (A + 4))) (hr : r.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = r ++ rest) (hc : (S.R ctr).length = B) (hct : S.R ctmp = [])
    (htc : (S.R tc).length = t) (htt : S.R ttmp = []) (hbuf : S.R buf = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.flag = rest.head?.isSome ∧
      Exec body (recordStep src ctr ctmp tc ttmp buf b0 b1 ck) (mk v S) (4 * B + 6 * t + 12)
        (mk v' { S with R := (Function.update (Function.update S.R src rest)
          (if symBit (r.getD t 0) then b1 else b0)
          (r.reverse ++ S.R (if symBit (r.getD t 0) then b1 else b0))) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, ⟨c1, c2, c3, c4, c5, c6⟩, ⟨m1, m2, m3, m4, m5⟩,
    ⟨t1, t2, t3, t4⟩, ⟨u1, u2, u3⟩, ⟨f1, f2⟩, g1⟩ := hreg
  -- the key symbol
  have hdrop : r.drop t = r[t] :: r.drop (t + 1) := List.drop_eq_getElem_cons (by omega)
  have hkey : (r.drop t ++ rest).head?.getD blank = r.getD t 0 := by
    rw [hdrop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  -- the first `t` symbols onto `buf`, then the key symbol into `scan ck`
  obtain ⟨v₁, R₁, hu₁, hsc₁, he₁, htc₁, htt₁, hsrc₁, hbuf₁, hoth₁⟩ :=
    xferBlock_exec body (fun _ : Fin 1 => src) (fun _ => buf) tc ttmp ck 1 (fun _ => 0)
      (peekKey src ck) 0 s3 s4 t1 (Ne.symm s5) (Ne.symm t2) (Ne.symm u1) (S.R tc) (r.take t)
      (r.drop t ++ rest) v S (by rw [htc, List.length_take]; omega) rfl htt
      (by show S.R src = _; rw [hs, ← List.append_assoc, List.take_append_drop]) rfl
  set w₁ : HS T Q A U := { v₁ with scan := Function.update v.scan ck (r.getD t 0) } with hw₁
  have he₁' : Exec body (keyBlock src buf tc ttmp ck) (mk v S) (4 * t + 5)
      (mk w₁ { S with R := R₁ }) := by
    refine Exec.cast he₁ (by rw [htc]) ?_
    rw [peekKey_run]
    dsimp only
    rw [hsrc₁, hkey, Function.update_idem]
  -- the prefix back onto `src`
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := moveR_exec_scan body buf src (Ne.symm s5) id w₁
    { S with R := R₁ }
  set R₂ := movedR R₁ buf src id (R₁ buf) with hR₂
  have hsrc₂ : R₂ src = r ++ rest := by
    simp [hR₂, movedR, hbuf₁, hsrc₁, hbuf]
    rw [← List.append_assoc, List.take_append_drop]
  have hR₂k : ∀ k, k ≠ src → k ≠ tc → k ≠ ttmp → k ≠ buf → R₂ k = S.R k := by
    intro k h1 h2 h3 h4
    rw [hR₂, movedR, Function.update_of_ne h1, Function.update_of_ne h4]
    exact hoth₁ k h1 h2 h3 h4
  -- the whole record onto its bucket
  set bk := if symBit (r.getD t 0) then b1 else b0 with hbk
  have hbk' : bucketOf b0 b1 (bitSel (r.getD t 0).val) = bk := bucketOf_bitSel b0 b1 _
  have hbk0 : bk = b0 ∨ bk = b1 := by
    rw [hbk]; split_ifs <;> simp
  have k1 : bk ≠ src := by rcases hbk0 with h | h <;> rw [h] <;> exact Ne.symm (by assumption)
  have k2 : bk ≠ ctr := by rcases hbk0 with h | h <;> rw [h] <;> exact Ne.symm (by assumption)
  have k3 : bk ≠ ctmp := by rcases hbk0 with h | h <;> rw [h] <;> exact Ne.symm (by assumption)
  have k4 : bk ≠ tc := by rcases hbk0 with h | h <;> rw [h] <;> exact Ne.symm (by assumption)
  have k5 : bk ≠ ttmp := by rcases hbk0 with h | h <;> rw [h] <;> exact Ne.symm (by assumption)
  have k6 : bk ≠ buf := by rcases hbk0 with h | h <;> rw [h] <;> exact Ne.symm (by assumption)
  obtain ⟨v₃, R₃, hu₃, hsc₃, he₃, hctr₃, hct₃, hsrc₃, hbk₃, hoth₃⟩ :=
    xferBlock_exec body (fun _ : Fin 2 => src) (bucketOf b0 b1) ctr ctmp ck 1 bitSel (peekR src)
      (bitSel (r.getD t 0).val) s1 s2 c1 (by rw [hbk']; exact k1) (by rw [hbk']; exact k2)
      (by rw [hbk']; exact k3) (S.R ctr) r rest v₂ { S with R := R₂ } (by rw [hc, hr])
      (hR₂k ctr (Ne.symm s1) c2 c3 c4) ((hR₂k ctmp (Ne.symm s2) m1 m2 m3).trans hct)
      hsrc₂ (by rw [hsc₂, hw₁]; simp)
  rw [peekR_run] at he₃
  rw [hbk'] at hbk₃ hoth₃
  dsimp only at hbk₃ hoth₃
  have hR₃ : R₃ = Function.update (Function.update S.R src rest) bk (r.reverse ++ S.R bk) := by
    funext k
    by_cases h1 : k = bk
    · rw [h1, Function.update_self, hbk₃, hR₂k bk k1 k4 k5 k6]
    rw [Function.update_of_ne h1]
    by_cases h2 : k = src
    · rw [h2, Function.update_self, hsrc₃]
    rw [Function.update_of_ne h2]
    by_cases h3 : k = ctr
    · rw [h3, hctr₃]
    by_cases h4 : k = ctmp
    · rw [h4, hct₃, hct]
    rw [hoth₃ k h2 h3 h4 h1]
    by_cases h5 : k = tc
    · rw [h5, hR₂, movedR, Function.update_of_ne (Ne.symm s3), Function.update_of_ne t2, htc₁]
    by_cases h6 : k = ttmp
    · rw [h6, hR₂, movedR, Function.update_of_ne (Ne.symm s4), Function.update_of_ne u1, htt₁,
        htt]
    by_cases h7 : k = buf
    · rw [h7, hR₂, movedR, Function.update_of_ne (Ne.symm s5), Function.update_self, hbuf]
    exact hR₂k k h2 h5 h6 h7
  subst hR₃
  refine ⟨_, ?_, ?_, Exec.cast (Exec.seq he₁' (Exec.seq he₂ he₃)) ?_ rfl⟩
  · simp [hu₃, hu₂, hw₁, hu₁]
  · simp [Function.update_of_ne k1.symm]
  · simp only [hbuf₁, hbuf, hc, List.append_nil, List.length_reverse, List.length_take]
    omega

/-! ### One pass -/

/-- One stable pass on key bit `|tc|`: the records in `src` go to the buckets `b0` (key bit
`false`) and `b1` (key bit `true`), and then `b1` and `b0` are moved onto `out`. -/
def radixPass (src out ctr ctmp tc ttmp buf b0 b1 ck : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (recordStep src ctr ctmp tc ttmp buf b0 b1 ck))
      (.seq (moveR b1 out id) (moveR b0 out id)))

/-- The record loop of `radixPass`: bucket `b` receives the reversal of the flattened records of
key bit `b`, `src` ends empty, and every other register is unchanged. -/
theorem radixPass_loop (src ctr ctmp tc ttmp buf b0 b1 ck : Fin T)
    (hreg : [src, ctr, ctmp, tc, ttmp, buf, b0, b1].Nodup) {B t : ℕ} (htB : t < B) :
    ∀ (recs : List (List (Fin (A + 4)))) (v : HS T Q A U) (S : Stacks T A),
      (∀ r ∈ recs, r.length = B) → S.R src = recs.flatten → (S.R ctr).length = B →
      S.R ctmp = [] → (S.R tc).length = t → S.R ttmp = [] → S.R buf = [] →
      v.flag = recs.flatten.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (recordStep src ctr ctmp tc ttmp buf b0 b1 ck)) (mk v S)
          (recs.length * (4 * B + 6 * t + 13) + 1)
          (mk v' { S with R := (Function.update (Function.update (Function.update S.R src [])
            b0 ((recs.filter fun r => !symBit (r.getD t 0)).flatten.reverse ++ S.R b0))
            b1 ((recs.filter fun r => symBit (r.getD t 0)).flatten.reverse ++ S.R b1)) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg'
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, ⟨c1, c2, c3, c4, c5, c6⟩, ⟨m1, m2, m3, m4, m5⟩,
    ⟨t1, t2, t3, t4⟩, ⟨u1, u2, u3⟩, ⟨f1, f2⟩, g1⟩ := hreg'
  intro recs
  induction recs with
  | nil =>
      intro v S _ hs _ _ _ _ _ hf
      have h0 : Function.update S.R src [] = S.R := by
        rw [Function.update_eq_self_iff, hs]; rfl
      refine ⟨v, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) ?_⟩
      simp only [List.filter_nil, List.flatten_nil, List.reverse_nil, List.nil_append, h0,
        Function.update_eq_self]
  | cons r recs ih =>
      intro v S hrec hs hc hct htc htt hbuf hf
      have hr : r.length = B := hrec r List.mem_cons_self
      obtain ⟨v₁, hu₁, hf₁, he₁⟩ := recordStep_exec body src ctr ctmp tc ttmp buf b0 b1 ck hreg
        htB r recs.flatten hr v S (by rw [hs, List.flatten_cons]) hc hct htc htt hbuf
      set bk := if symBit (r.getD t 0) then b1 else b0 with hbk
      have hbk0 : bk = b0 ∨ bk = b1 := by
        rw [hbk]; split_ifs <;> simp
      have k1 : src ≠ bk := by rcases hbk0 with h | h <;> rw [h] <;> assumption
      have k2 : ctr ≠ bk := by rcases hbk0 with h | h <;> rw [h] <;> assumption
      have k3 : ctmp ≠ bk := by rcases hbk0 with h | h <;> rw [h] <;> assumption
      have k4 : tc ≠ bk := by rcases hbk0 with h | h <;> rw [h] <;> assumption
      have k5 : ttmp ≠ bk := by rcases hbk0 with h | h <;> rw [h] <;> assumption
      have k6 : buf ≠ bk := by rcases hbk0 with h | h <;> rw [h] <;> assumption
      obtain ⟨v', hu', he'⟩ := ih v₁
        { S with R := (Function.update (Function.update S.R src recs.flatten) bk
          (r.reverse ++ S.R bk)) } (fun r' h => hrec r' (List.mem_cons_of_mem _ h))
        (by simp [Function.update_of_ne k1])
        (by simp [Function.update_of_ne k2, Function.update_of_ne (Ne.symm s1), hc])
        (by simp [Function.update_of_ne k3, Function.update_of_ne (Ne.symm s2), hct])
        (by simp [Function.update_of_ne k4, Function.update_of_ne (Ne.symm s3), htc])
        (by simp [Function.update_of_ne k5, Function.update_of_ne (Ne.symm s4), htt])
        (by simp [Function.update_of_ne k6, Function.update_of_ne (Ne.symm s5), hbuf]) hf₁
      have hne : v.flag = true := by
        rw [hf, List.flatten_cons]
        cases r with
        | nil => simp at hr; omega
        | cons x r' => simp
      refine ⟨v', hu'.trans hu₁,
        Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hne he₁ he')
        (by simp only [List.length_cons]; ring) ?_⟩
      congr 2
      funext k
      rcases Bool.eq_false_or_eq_true (symBit (r.getD t 0)) with hb | hb <;>
        have hb' := hb <;> simp only [List.getD_eq_getElem?_getD] at hb'
      · have hbk1 : bk = b1 := by rw [hbk, hb]; rfl
        rw [hbk1] at k1 k2 k3 k4 k5 k6 ⊢
        by_cases kb1 : k = b1
        · subst kb1
          simp [hb, hb', List.filter_cons]
        by_cases kb0 : k = b0
        · subst kb0
          simp [hb, hb', List.filter_cons, Function.update_of_ne g1,
            Function.update_of_ne (Ne.symm s6)]
        by_cases ks : k = src
        · subst ks
          simp [Function.update_of_ne s6, Function.update_of_ne s7]
        simp [Function.update_of_ne kb1, Function.update_of_ne kb0, Function.update_of_ne ks]
      · have hbk1 : bk = b0 := by rw [hbk, hb]; rfl
        rw [hbk1] at k1 k2 k3 k4 k5 k6 ⊢
        by_cases kb1 : k = b1
        · subst kb1
          simp [hb, hb', List.filter_cons, Function.update_of_ne (Ne.symm g1),
            Function.update_of_ne (Ne.symm s7)]
        by_cases kb0 : k = b0
        · subst kb0
          simp [hb, hb', List.filter_cons, Function.update_of_ne g1]
        by_cases ks : k = src
        · subst ks
          simp [Function.update_of_ne s6, Function.update_of_ne s7]
        simp [Function.update_of_ne kb1, Function.update_of_ne kb0, Function.update_of_ne ks]

/-- One stable pass by key bit `t = |tc|` over `n` records of `B > t` symbols in `src`: `out`
receives `(RadixSort.pass (fun rec => symBit (rec.getD t 0)) recs).flatten` on top, in forward
order, and `src` ends empty (`out` may be `src`). Counters, temps and buckets are restored and
every other register is unchanged. At most `6 * n * B + 6 * n * t + 13 * n + 6` steps. -/
theorem radixPass_exec (src out ctr ctmp tc ttmp buf b0 b1 ck : Fin T)
    (hreg : [src, ctr, ctmp, tc, ttmp, buf, b0, b1].Nodup)
    (hout : out ∉ [ctr, ctmp, tc, ttmp, buf, b0, b1])
    {recs : List (List (Fin (A + 4)))} {B t : ℕ} (htB : t < B) (hrec : ∀ r ∈ recs, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hs : S.R src = recs.flatten) (hc : (S.R ctr).length = B)
    (hct : S.R ctmp = []) (htc : (S.R tc).length = t) (htt : S.R ttmp = [])
    (hbuf : S.R buf = []) (h0 : S.R b0 = []) (h1 : S.R b1 = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 6 * recs.length * B + 6 * recs.length * t + 13 * recs.length + 6 ∧
      Exec body (radixPass src out ctr ctmp tc ttmp buf b0 b1 ck) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R src []) out
          ((RadixSort.pass (fun rec => symBit (rec.getD t 0)) recs).flatten ++
            Function.update S.R src [] out)) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg' hout
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, ⟨c1, c2, c3, c4, c5, c6⟩, ⟨m1, m2, m3, m4, m5⟩,
    ⟨t1, t2, t3, t4⟩, ⟨u1, u2, u3⟩, ⟨f1, f2⟩, g1⟩ := hreg'
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hout
  have he₀ := Exec.act (body := body) (peekR src) (mk v S)
  rw [peekR_run] at he₀
  obtain ⟨v₁, hu₁, he₁⟩ := radixPass_loop body src ctr ctmp tc ttmp buf b0 b1 ck hreg htB recs
    { v with flag := (S.R src).head?.isSome } S hrec hs hc hct htc htt hbuf (by simp [hs])
  set F := recs.filter fun r => !symBit (r.getD t 0) with hF
  set Tr := recs.filter fun r => symBit (r.getD t 0) with hTr
  set R₁ := Function.update (Function.update (Function.update S.R src []) b0
    (F.flatten.reverse ++ S.R b0)) b1 (Tr.flatten.reverse ++ S.R b1) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body b1 out (Ne.symm o7) id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ b1 out id (R₁ b1) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body b0 out (Ne.symm o6) id v₂ { S with R := R₂ }
  have hR₁b0 : R₁ b0 = F.flatten.reverse := by
    rw [hR₁, Function.update_of_ne g1, Function.update_self, h0, List.append_nil]
  have hR₁b1 : R₁ b1 = Tr.flatten.reverse := by
    rw [hR₁, Function.update_self, h1, List.append_nil]
  have hR₁out : R₁ out = Function.update S.R src [] out := by
    rw [hR₁, Function.update_of_ne o7, Function.update_of_ne o6]
  have hR₂b0 : R₂ b0 = F.flatten.reverse := by
    rw [hR₂, movedR, Function.update_of_ne (Ne.symm o6), Function.update_of_ne g1, hR₁b0]
  have hR₂out : R₂ out = Tr.flatten ++ Function.update S.R src [] out := by
    rw [hR₂, movedR, Function.update_self, hR₁b1, hR₁out]
    simp
  have hFT : F.length + Tr.length = recs.length := by
    have := RadixSort.pass_length (fun rec => symBit (rec.getD t 0)) recs
    rw [RadixSort.pass, List.length_append] at this
    exact this
  have hFl : F.flatten.length = F.length * B :=
    length_flatten_of_length F (fun r hr => hrec r (List.mem_filter.1 hr).1)
  have hTl : Tr.flatten.length = Tr.length * B :=
    length_flatten_of_length Tr (fun r hr => hrec r (List.mem_filter.1 hr).1)
  have hfin : movedR R₂ b0 out id (R₂ b0) = Function.update (Function.update S.R src []) out
      ((RadixSort.pass (fun rec => symBit (rec.getD t 0)) recs).flatten ++
        Function.update S.R src [] out) := by
    funext k
    by_cases ko : k = out
    · rw [ko, movedR, Function.update_self, Function.update_self, hR₂b0, hR₂out, RadixSort.pass,
        List.flatten_append]
      simp [hF, hTr]
    rw [movedR, Function.update_of_ne ko, Function.update_of_ne ko]
    by_cases k0 : k = b0
    · rw [k0, Function.update_self, Function.update_of_ne (Ne.symm s6), h0]
    rw [Function.update_of_ne k0, hR₂, movedR, Function.update_of_ne ko]
    by_cases k1 : k = b1
    · rw [k1, Function.update_self, Function.update_of_ne (Ne.symm s7), h1]
    rw [Function.update_of_ne k1, hR₁, Function.update_of_ne k1, Function.update_of_ne k0]
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], le_of_eq ?_,
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃))) rfl ?_⟩
  · show 1 + (recs.length * (4 * B + 6 * t + 13) + 1 +
      (2 * (R₁ b1).length + 2 + (2 * (R₂ b0).length + 2))) = _
    rw [hR₁b1, hR₂b0, List.length_reverse, List.length_reverse, hFl, hTl, ← hFT]
    ring
  · show mk v₃ { S with R := movedR R₂ b0 out id (R₂ b0) } = _
    rw [hfin]

/-- `radixPass_exec` in place (`out = src`): `src` is replaced by the result. -/
theorem radixPass_exec_self (src ctr ctmp tc ttmp buf b0 b1 ck : Fin T)
    (hreg : [src, ctr, ctmp, tc, ttmp, buf, b0, b1].Nodup)
    {recs : List (List (Fin (A + 4)))} {B t : ℕ} (htB : t < B) (hrec : ∀ r ∈ recs, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hs : S.R src = recs.flatten) (hc : (S.R ctr).length = B)
    (hct : S.R ctmp = []) (htc : (S.R tc).length = t) (htt : S.R ttmp = [])
    (hbuf : S.R buf = []) (h0 : S.R b0 = []) (h1 : S.R b1 = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 6 * recs.length * B + 6 * recs.length * t + 13 * recs.length + 6 ∧
      Exec body (radixPass src src ctr ctmp tc ttmp buf b0 b1 ck) (mk v S) m
        (mk v' { S with R := (Function.update S.R src
          (RadixSort.pass (fun rec => symBit (rec.getD t 0)) recs).flatten) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := radixPass_exec body src src ctr ctmp tc ttmp buf b0 b1 ck hreg
    (List.nodup_cons.1 hreg).1 htB hrec v S hs hc hct htc htt hbuf h0 h1
  refine ⟨v', m, hu, hm, Exec.cast he rfl ?_⟩
  simp [Function.update_idem]

/-! ### The full sort -/

/-- Stable passes for key bits `0, 1, …, |kc| - 1`, in place on `src`. The pass counter `tc`
starts empty and gains one symbol of `kc` after each pass; a final `moveR` returns them. -/
def radixSort (src ctr ctmp tc ttmp buf b0 b1 ck kc : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR kc))
    (.seq (.loop (·.flag) (.seq (radixPass src src ctr ctmp tc ttmp buf b0 b1 ck)
        (.act (moveStep kc tc id))))
      (moveR tc kc id))

/-- The pass loop of `radixSort`, after `j` passes with the symbols `ks` left in `kc`. -/
theorem radixSort_loop (src ctr ctmp tc ttmp buf b0 b1 ck kc : Fin T)
    (hreg : [src, ctr, ctmp, tc, ttmp, buf, b0, b1, kc].Nodup)
    {recs : List (List (Fin (A + 4)))} {B K : ℕ} (hKB : K ≤ B)
    (hrec : ∀ r ∈ recs, r.length = B) :
    ∀ (ks : List (Fin (A + 4))) (j : ℕ) (v : HS T Q A U) (S : Stacks T A),
      j + ks.length ≤ K → S.R kc = ks → (S.R tc).length = j →
      S.R src = (RadixSort.sort (fun rec j => symBit (rec.getD j 0)) j recs).flatten →
      (S.R ctr).length = B → S.R ctmp = [] → S.R ttmp = [] → S.R buf = [] → S.R b0 = [] →
      S.R b1 = [] → v.flag = ks.head?.isSome →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
        m ≤ ks.length * (6 * recs.length * B + 6 * recs.length * K + 13 * recs.length + 8) + 1 ∧
        Exec body (.loop (·.flag) (.seq (radixPass src src ctr ctmp tc ttmp buf b0 b1 ck)
          (.act (moveStep kc tc id)))) (mk v S) m
          (mk v' { S with R := (Function.update (Function.update (Function.update S.R src
            (RadixSort.sort (fun rec j => symBit (rec.getD j 0)) (j + ks.length) recs).flatten)
            kc []) tc (ks.reverse ++ S.R tc)) }) := by
  have hreg8 : [src, ctr, ctmp, tc, ttmp, buf, b0, b1].Nodup :=
    (show ([src, ctr, ctmp, tc, ttmp, buf, b0, b1] ++ [kc]).Nodup from hreg).sublist
      (List.sublist_append_left _ _)
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg'
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8⟩, ⟨c1, c2, c3, c4, c5, c6, c7⟩,
    ⟨m1, m2, m3, m4, m5, m6⟩, ⟨t1, t2, t3, t4, t5⟩, ⟨u1, u2, u3, u4⟩, ⟨f1, f2, f3⟩,
    ⟨g1, g2⟩, g3⟩ := hreg'
  intro ks
  induction ks with
  | nil =>
      intro j v S _ hk _ hs _ _ _ _ _ _ hf
      have hid : Function.update (Function.update (Function.update S.R src
          (RadixSort.sort (fun rec j => symBit (rec.getD j 0))
            (j + ([] : List (Fin (A + 4))).length) recs).flatten)
          kc []) tc (([] : List (Fin (A + 4))).reverse ++ S.R tc) = S.R := by
        funext k
        by_cases ktc : k = tc
        · rw [ktc, Function.update_self]; simp
        rw [Function.update_of_ne ktc]
        by_cases kkc : k = kc
        · rw [kkc, Function.update_self, hk]
        rw [Function.update_of_ne kkc]
        by_cases ks : k = src
        · rw [ks, Function.update_self, hs]; simp
        rw [Function.update_of_ne ks]
      refine ⟨v, 1, rfl, by simp, Exec.cast (.loop_false (by simpa using hf)) rfl ?_⟩
      rw [hid]
  | cons e ks ih =>
      intro j v S hjK hk htc hs hc hct htt hbuf h0 h1 hf
      simp only [List.length_cons] at hjK
      have hjB : j < B := by omega
      have hrec' : ∀ r ∈ RadixSort.sort (fun rec j => symBit (rec.getD j 0)) j recs,
          r.length = B := fun r hr =>
        hrec r ((RadixSort.sort_perm (fun rec j => symBit (rec.getD j 0)) j recs).mem_iff.1 hr)
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := radixPass_exec_self body src ctr ctmp tc ttmp buf b0 b1
        ck hreg8 hjB hrec' v S hs hc hct htc htt hbuf h0 h1
      rw [RadixSort.sort_length] at hm₁
      set R₁ := Function.update S.R src (RadixSort.pass (fun rec => symBit (rec.getD j 0))
        (RadixSort.sort (fun rec j => symBit (rec.getD j 0)) j recs)).flatten with hR₁
      have hR₁kc : R₁ kc = e :: ks := by rw [hR₁, Function.update_of_ne (Ne.symm s8), hk]
      have hR₁tc : R₁ tc = S.R tc := by rw [hR₁, Function.update_of_ne (Ne.symm s3)]
      have hrun : (moveStep kc tc id : Act T Q A U).run (mk v₁ { S with R := R₁ }) =
          mk { v₁ with sym := some e, flag := ks.head?.isSome }
            { S with R := Function.update (Function.update R₁ kc ks) tc (e :: R₁ tc) } := by
        simp [moveStep, peekR, Action.run, hR₁kc, update_rt, Function.update_of_ne t5,
          Function.update_of_ne (Ne.symm t5)]
      have he₂ := Exec.act (body := body) (moveStep kc tc id) (mk v₁ { S with R := R₁ })
      rw [hrun] at he₂
      have hsort : RadixSort.sort (fun rec j => symBit (rec.getD j 0)) (j + 1) recs =
          RadixSort.pass (fun rec => symBit (rec.getD j 0))
            (RadixSort.sort (fun rec j => symBit (rec.getD j 0)) j recs) := rfl
      obtain ⟨v', m', hu', hm', he'⟩ := ih (j + 1)
        { v₁ with sym := some e, flag := ks.head?.isSome }
        { S with R := Function.update (Function.update R₁ kc ks) tc (e :: R₁ tc) } (by omega)
        (by simp [Function.update_of_ne (Ne.symm t5)])
        (by simp [hR₁tc, htc])
        (by
          show Function.update (Function.update R₁ kc ks) tc (e :: R₁ tc) src = _
          rw [Function.update_of_ne s3, Function.update_of_ne s8, hR₁, Function.update_self,
            hsort])
        (by simp [Function.update_of_ne c2, Function.update_of_ne c7, hR₁,
          Function.update_of_ne (Ne.symm s1), hc])
        (by simp [Function.update_of_ne m1, Function.update_of_ne m6, hR₁,
          Function.update_of_ne (Ne.symm s2), hct])
        (by simp [Function.update_of_ne (Ne.symm t1), Function.update_of_ne u4, hR₁,
          Function.update_of_ne (Ne.symm s4), htt])
        (by simp [Function.update_of_ne (Ne.symm t2), Function.update_of_ne f3, hR₁,
          Function.update_of_ne (Ne.symm s5), hbuf])
        (by simp [Function.update_of_ne (Ne.symm t3), Function.update_of_ne g2, hR₁,
          Function.update_of_ne (Ne.symm s6), h0])
        (by simp [Function.update_of_ne (Ne.symm t4), Function.update_of_ne g3, hR₁,
          Function.update_of_ne (Ne.symm s7), h1])
        rfl
      have hne : v.flag = true := by rw [hf]; rfl
      refine ⟨v', _, hu'.trans hu₁, ?_,
        Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hne (Exec.seq he₁ he₂) he') rfl ?_⟩
      · have hjK' : 6 * recs.length * j ≤ 6 * recs.length * K :=
          Nat.mul_le_mul_left _ (by omega)
        rw [List.length_cons, Nat.add_one_mul]
        omega
      · have hlen : j + 1 + ks.length = j + (e :: ks).length := by
          simp only [List.length_cons]; omega
        rw [hlen]
        congr 2
        funext k
        dsimp only
        by_cases ktc : k = tc
        · rw [ktc, Function.update_self, Function.update_self, Function.update_self, hR₁tc]
          simp
        rw [Function.update_of_ne ktc, Function.update_of_ne ktc]
        by_cases kkc : k = kc
        · rw [kkc, Function.update_self, Function.update_self]
        rw [Function.update_of_ne kkc, Function.update_of_ne kkc]
        by_cases ks' : k = src
        · rw [ks', Function.update_self, Function.update_self]
        rw [Function.update_of_ne ks', Function.update_of_ne ks', Function.update_of_ne ktc,
          Function.update_of_ne kkc, hR₁, Function.update_of_ne ks']

/-- Stable LSD radix sort by key bits `0, 1, …, K' - 1` (`K'` the length of `kc`, `K' ≤ K ≤ B`)
of `n` records of `B` symbols in `src`, in place: `src` receives
`(RadixSort.sort (fun rec j => symBit (rec.getD j 0)) K' recs).flatten`. Every other register is
restored. At most `K' * (6 * n * B + 6 * n * K + 13 * n + 6) + 4 * K' + 4` steps. -/
theorem radixSort_exec (src ctr ctmp tc ttmp buf b0 b1 ck kc : Fin T)
    (hreg : [src, ctr, ctmp, tc, ttmp, buf, b0, b1, kc].Nodup)
    {recs : List (List (Fin (A + 4)))} {B K K' : ℕ} (hKB : K ≤ B) (hK' : K' ≤ K)
    (hrec : ∀ r ∈ recs, r.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = recs.flatten) (hk : (S.R kc).length = K') (hc : (S.R ctr).length = B)
    (hct : S.R ctmp = []) (htc : S.R tc = []) (htt : S.R ttmp = []) (hbuf : S.R buf = [])
    (h0 : S.R b0 = []) (h1 : S.R b1 = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ K' * (6 * recs.length * B + 6 * recs.length * K + 13 * recs.length + 6) +
        4 * K' + 4 ∧
      Exec body (radixSort src ctr ctmp tc ttmp buf b0 b1 ck kc) (mk v S) m
        (mk v' { S with R := (Function.update S.R src
          (RadixSort.sort (fun rec j => symBit (rec.getD j 0)) K' recs).flatten) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg'
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8⟩, -, -, ⟨t1, t2, t3, t4, t5⟩, -, -, -, -⟩ := hreg'
  have he₀ := Exec.act (body := body) (peekR kc) (mk v S)
  rw [peekR_run] at he₀
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := radixSort_loop body src ctr ctmp tc ttmp buf b0 b1 ck kc hreg
    hKB hrec (S.R kc) 0 { v with flag := (S.R kc).head?.isSome } S (by omega) rfl (by simp [htc])
    hs hc hct htt hbuf h0 h1 rfl
  rw [Nat.zero_add, hk, htc, List.append_nil] at he₁
  rw [hk] at hm₁
  set R₁ := Function.update (Function.update (Function.update S.R src
    (RadixSort.sort (fun rec j => symBit (rec.getD j 0)) K' recs).flatten) kc []) tc
    (S.R kc).reverse with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tc kc t5 id v₁ { S with R := R₁ }
  have hR₁tc : R₁ tc = (S.R kc).reverse := by rw [hR₁, Function.update_self]
  have hfin : movedR R₁ tc kc id (R₁ tc) = Function.update S.R src
      (RadixSort.sort (fun rec j => symBit (rec.getD j 0)) K' recs).flatten := by
    funext k
    by_cases kkc : k = kc
    · rw [kkc, movedR, Function.update_self, hR₁tc, Function.update_of_ne (Ne.symm s8), hR₁,
        Function.update_of_ne (Ne.symm t5), Function.update_self]
      simp
    rw [movedR, Function.update_of_ne kkc]
    by_cases ktc : k = tc
    · rw [ktc, Function.update_self, Function.update_of_ne (Ne.symm s3), htc]
    rw [Function.update_of_ne ktc, hR₁, Function.update_of_ne ktc, Function.update_of_ne kkc]
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ he₂)) rfl ?_⟩
  · show 1 + (m₁ + (2 * (R₁ tc).length + 2)) ≤ _
    rw [hR₁tc, List.length_reverse, hk]
    have : K' * (6 * recs.length * B + 6 * recs.length * K + 13 * recs.length + 8) =
        K' * (6 * recs.length * B + 6 * recs.length * K + 13 * recs.length + 6) + 2 * K' := by
      ring
    omega
  · show mk v₂ { S with R := movedR R₁ tc kc id (R₁ tc) } = _
    rw [hfin]

end IntegerMultBounds.MathlibTM2.Host
