module

public import IntegerMultBounds.MathlibTM2.Host.Stream
public import IntegerMultBounds.MathlibTM2.Host.Auto

/-!
# Gathering and spreading bits by a mask

Bit lists on registers are `l.map bitSymbol`, least significant bit on top.

* `gatherL s m`: the bits of `s` at the set positions of the mask `m`, in order. `gather src mask
  ts tm dst out` pushes `gatherL s m` onto `out` (`gather_exec`), restoring `src` and `mask`.
* `spreadL s m`: for each position of `m`, the next bit of `s` if the mask bit is set and `false`
  otherwise. `spread src mask ts tm dst out` pushes `spreadL s m` onto `out` (`spread_exec`).

`ts`, `tm` and `dst` are spare registers; they start and end empty.

`gatherL_ofFn` and `spreadL_ofFn` describe both maps on `List.ofFn`: gathering reads the source
at the set positions in increasing order; spreading writes source bit `c` at the `c`-th set
position.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

/-! ### List semantics -/

/-- The bits of `s` at the set positions of `m`. -/
def gatherL : List Bool → List Bool → List Bool
  | s :: ss, m :: ms => if m then s :: gatherL ss ms else gatherL ss ms
  | _, _ => []

/-- One output bit per mask bit: the next source bit at a set position, `false` elsewhere. -/
def spreadL : List Bool → List Bool → List Bool
  | _, [] => []
  | ss, true :: ms => ss.headD false :: spreadL ss.tail ms
  | ss, false :: ms => false :: spreadL ss ms

lemma length_spreadL : ∀ (ss ms : List Bool), (spreadL ss ms).length = ms.length
  | _, [] => rfl
  | ss, true :: ms => by simp [spreadL, length_spreadL ss.tail ms]
  | ss, false :: ms => by simp [spreadL, length_spreadL ss ms]

lemma length_gatherL : ∀ (ss ms : List Bool), ss.length = ms.length →
    (gatherL ss ms).length = ms.count true
  | [], [], _ => rfl
  | s :: ss, m :: ms, h => by
    have := length_gatherL ss ms (by simpa using h)
    cases m <;> simp [gatherL, this]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ### Gathering on registers -/

section Machine

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- One gather step: pop a mask bit into `sym` and a source bit into scan slot `cs`, save both on
`tm` and `ts`, and push the source bit onto `dst` when the mask bit is set. -/
def gatherStep (src mask ts tm dst cs : Fin T) : Act T Q A U :=
  .pop (.rt mask) (fun v o => { v with sym := o })
    (.pop (.rt src) (fun v o => { v with scan := Function.update v.scan cs (o.getD blank) })
      (.push (.rt tm) (fun v => v.sym.getD blank)
        (.push (.rt ts) (fun v => v.scan cs)
          (.branch (fun v => symBit (v.sym.getD blank))
            (.push (.rt dst) (fun v => v.scan cs) (peekR mask))
            (peekR mask)))))

/-- Gather the bits of `src` at the set bits of `mask` onto `out`. -/
def gather (src mask ts tm dst out cs : Fin T) : Pr P T Q A U :=
  .seq (whileR mask (gatherStep src mask ts tm dst cs))
    (.seq (moveR tm mask id) (.seq (moveR ts src id) (moveR dst out id)))

/-- Distinct registers of a gather or a spread. -/
def GSRegs (src mask ts tm dst out : Fin T) : Prop := [src, mask, ts, tm, dst, out].Nodup

lemma bits_cons (b : Bool) (l : List Bool) :
    ((b :: l).map bitSymbol : List (Fin (A + 4))) = bitSymbol b :: l.map bitSymbol := rfl

/-- The registers after a gather or spread loop: `mask` and the consumed source bits `ss` moved
reversed onto `tm` and `ts`, the outputs `os` reversed onto `dst`. -/
def loopR (R : Fin T → List (Fin (A + 4))) (src mask ts tm dst : Fin T)
    (rest ss ms os : List Bool) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R mask [])
    src (rest.map bitSymbol)) tm ((ms.map bitSymbol).reverse ++ R tm)) ts
    ((ss.map bitSymbol).reverse ++ R ts)) dst ((os.map bitSymbol).reverse ++ R dst)

theorem gather_loop {src mask ts tm dst cs : Fin T} (h : [src, mask, ts, tm, dst].Nodup) :
    ∀ (ms ss : List Bool) (v : HS T Q A U) (S : Stacks T A), ms.length = ss.length →
      S.R mask = ms.map bitSymbol → S.R src = ss.map bitSymbol →
      v.flag = ms.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (gatherStep src mask ts tm dst cs))) (mk v S)
          (2 * ms.length + 1)
          (mk v' { S with R := loopR S.R src mask ts tm dst [] ss ms (gatherL ss ms) }) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hn
  intro ms
  induction ms with
  | nil =>
    intro ss v S hl hm hs hf
    obtain rfl : ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    refine ⟨v, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) ?_⟩
    congr 1
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [loopR]
    by_cases hk1 : k = dst
    · subst hk1; simp [gatherL]
    by_cases hk2 : k = ts
    · subst hk2; simp [hk1]
    by_cases hk3 : k = tm
    · subst hk3; simp [hk1, hk2]
    by_cases hk4 : k = src
    · subst hk4; simp [hk1, hk2, hk3, hs]
    by_cases hk5 : k = mask
    · subst hk5; simp [hk1, hk2, hk3, hk4, hm]
    simp [hk1, hk2, hk3, hk4, hk5]
  | cons m ms ih =>
    intro ss v S hl hm hs hf
    obtain ⟨s, ss, rfl⟩ : ∃ s ss', ss = s :: ss' := by
      cases ss with
      | nil => simp at hl
      | cons s ss' => exact ⟨s, ss', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hm' : S.R mask = bitSymbol m :: ms.map bitSymbol := hm
    have hs' : S.R src = bitSymbol s :: ss.map bitSymbol := hs
    set R₁ := Function.update (Function.update (Function.update (Function.update S.R mask
      (ms.map bitSymbol)) src (ss.map bitSymbol)) tm (bitSymbol m :: S.R tm)) ts
      (bitSymbol s :: S.R ts) with hR₁
    set R₂ := if m then Function.update R₁ dst (bitSymbol s :: S.R dst) else R₁ with hR₂
    have hrun : (gatherStep src mask ts tm dst cs : Act T Q A U).run (mk v S) =
        mk { v with
            sym := some (bitSymbol m)
            scan := Function.update v.scan cs (bitSymbol s)
            flag := ms.head?.isSome } { S with R := R₂ } := by
      cases m <;>
      simp [gatherStep, Action.run, peekR, update_rt, hm', hs', R₂, R₁,
        a1, b1, b2, b3, c1, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4,
        Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm c2, Ne.symm d1]
    have hR₂m : R₂ mask = ms.map bitSymbol := by
      cases m <;> simp [R₂, R₁, Ne.symm a1, b1, b2, b3]
    have hR₂s : R₂ src = ss.map bitSymbol := by
      cases m <;> simp [R₂, R₁, a2, a3, a4]
    obtain ⟨v', hu, he⟩ := ih ss { v with
        sym := some (bitSymbol m)
        scan := Function.update v.scan cs (bitSymbol s)
        flag := ms.head?.isSome } { S with R := R₂ } hl hR₂m hR₂s rfl
    refine ⟨v', hu, Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
      (hrun ▸ Exec.act (body := body) (gatherStep src mask ts tm dst cs) (mk v S)) he)
      (by simp; ring) ?_⟩
    congr 2
    funext k
    cases m <;>
    simp [loopR, R₂, R₁, gatherL, Function.update_apply, c2, d1, Ne.symm a4, Ne.symm b3,
      Ne.symm c1, Ne.symm c2, Ne.symm d1] <;> split_ifs <;> simp_all

/-- **Gathering.** With `src` holding `ss` and `mask` holding `ms` (equal lengths) and the spares
empty, `out` gains `gatherL ss ms` on top; every other register ends as it started. -/
theorem gather_exec {src mask ts tm dst out cs : Fin T} (h : GSRegs src mask ts tm dst out)
    (ms ss : List Bool) (hl : ms.length = ss.length) (v : HS T Q A U) (S : Stacks T A)
    (hm : S.R mask = ms.map bitSymbol) (hs : S.R src = ss.map bitSymbol)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 8 * ms.length + 8 ∧
      Exec body (gather src mask ts tm dst out cs) (mk v S) m
        (mk v' { S with R := Function.update S.R out ((gatherL ss ms).map bitSymbol ++ S.R out) }) := by
  have hn := h
  simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1⟩ := hn
  have h5 : [src, mask, ts, tm, dst].Nodup := by
    simp [a1, a2, a3, a4, b1, b2, b3, c1, c2, d1]
  have a1' := Ne.symm a1; have a2' := Ne.symm a2; have a3' := Ne.symm a3
  have a4' := Ne.symm a4; have a5' := Ne.symm a5; have b1' := Ne.symm b1
  have b2' := Ne.symm b2; have b3' := Ne.symm b3; have b4' := Ne.symm b4
  have c1' := Ne.symm c1; have c2' := Ne.symm c2; have c3' := Ne.symm c3
  have d1' := Ne.symm d1; have d2' := Ne.symm d2; have e1' := Ne.symm e1
  obtain ⟨v₁, hu₁, he₁⟩ := gather_loop body (cs := cs) h5 ms ss
    { v with flag := (S.R mask).head?.isSome } S hl hm hs (by rw [hm]; cases ms <;> rfl)
  set R₁ := loopR S.R src mask ts tm dst [] ss ms (gatherL ss ms) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tm mask (Ne.symm b2) id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ tm mask id (R₁ tm) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body ts src (Ne.symm a2) id v₂ { S with R := R₂ }
  set R₃ := movedR R₂ ts src id (R₂ ts) with hR₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body dst out e1 id v₃ { S with R := R₃ }
  have hg := length_gatherL ss ms hl.symm
  have hcount := List.count_le_length (a := true) (l := ms)
  have ht₁ : R₁ tm = (ms.map bitSymbol).reverse := by
    simp [hR₁, loopR, htm, d1, c1']
  have hs₁ : R₁ ts = (ss.map bitSymbol).reverse := by
    simp [hR₁, loopR, hts, c2]
  have hd₁ : R₁ dst = ((gatherL ss ms).map bitSymbol).reverse := by
    simp [hR₁, loopR, hdst]
  have hs₂ : R₂ ts = (ss.map bitSymbol).reverse := by
    simp [hR₂, movedR, Ne.symm b1, hs₁, c1]
  have hd₃ : R₃ dst = ((gatherL ss ms).map bitSymbol).reverse := by
    simp [hR₃, hR₂, movedR, Ne.symm a4, Ne.symm b3, hd₁, a1, a3, c1, b1', c2', d1']
  refine ⟨v₄, 1 + (2 * ms.length + 1) + ((2 * (R₁ tm).length + 2) + ((2 * (R₂ ts).length + 2) +
    (2 * (R₃ dst).length + 2))), by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq (Exec.seq (peekR_run mask v S ▸ Exec.act (body := body) (peekR mask) (mk v S)) he₁)
      (Exec.seq he₂ (Exec.seq he₃ (Exec.cast he₄ rfl ?_)))⟩
  · rw [ht₁, hs₂, hd₃]
    simp only [List.length_reverse, List.length_map]
    omega
  · congr 2
    funext k
    simp [hR₃, hR₂, hR₁, movedR, loopR, Function.update_apply, hts, htm, hdst, a1, a2,
      a3, a4, b1, b2, b3, c1, c2, d1, Ne.symm a1,
      Ne.symm a4, Ne.symm a5, Ne.symm b1, Ne.symm b3, Ne.symm b4, Ne.symm c1,
      Ne.symm c2, Ne.symm c3, Ne.symm d1, Ne.symm d2, Ne.symm e1]
    split_ifs <;> simp_all

/-! ### Spreading on registers -/

/-- One spread step: pop a mask bit and save it on `tm`; at a set bit pop a source bit, save it on
`ts` and push it onto `dst`, otherwise push `false` onto `dst`. -/
def spreadStep (src mask ts tm dst : Fin T) : Act T Q A U :=
  .pop (.rt mask) (fun v o => { v with sym := o })
    (.push (.rt tm) (fun v => v.sym.getD blank)
      (.branch (fun v => symBit (v.sym.getD blank))
        (.pop (.rt src) (fun v o => { v with sym := o })
          (.push (.rt ts) (fun v => v.sym.getD blank)
            (.push (.rt dst) (fun v => v.sym.getD blank) (peekR mask))))
        (.push (.rt dst) (fun _ => bitSymbol false) (peekR mask))))

/-- Spread the bits of `src` onto the set bits of `mask`, onto `out`. -/
def spread (src mask ts tm dst out : Fin T) : Pr P T Q A U :=
  .seq (whileR mask (spreadStep src mask ts tm dst))
    (.seq (moveR tm mask id) (.seq (moveR ts src id) (moveR dst out id)))

theorem spread_loop {src mask ts tm dst : Fin T} (h : [src, mask, ts, tm, dst].Nodup) :
    ∀ (ms ss rest : List Bool) (v : HS T Q A U) (S : Stacks T A), ms.count true = ss.length →
      S.R mask = ms.map bitSymbol → S.R src = (ss ++ rest).map bitSymbol →
      v.flag = ms.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (spreadStep src mask ts tm dst))) (mk v S)
          (2 * ms.length + 1)
          (mk v' { S with R := loopR S.R src mask ts tm dst rest ss ms (spreadL ss ms) }) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hn
  intro ms
  induction ms with
  | nil =>
    intro ss rest v S hl hm hs hf
    obtain rfl : ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    refine ⟨v, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) ?_⟩
    congr 1
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [loopR]
    simp [spreadL, Function.update_apply]
    split_ifs <;> simp_all
  | cons m ms ih =>
    intro ss rest v S hl hm hs hf
    have hm' : S.R mask = bitSymbol m :: ms.map bitSymbol := hm
    cases m with
    | false =>
      simp only [List.count_cons, Bool.false_eq_true, ite_false, Nat.add_zero,
        beq_iff_eq] at hl
      set R₂ := Function.update (Function.update (Function.update S.R mask (ms.map bitSymbol)) tm
        (bitSymbol false :: S.R tm)) dst (bitSymbol false :: S.R dst) with hR₂
      have hrun : (spreadStep src mask ts tm dst : Act T Q A U).run (mk v S) =
          mk { v with sym := some (bitSymbol false), flag := ms.head?.isSome }
            { S with R := R₂ } := by
        simp [spreadStep, Action.run, peekR, update_rt, hm', R₂,
          b2, b3, Ne.symm b2, Ne.symm b3, Ne.symm d1]
      obtain ⟨v', hu, he⟩ := ih ss rest
        { v with sym := some (bitSymbol false), flag := ms.head?.isSome } { S with R := R₂ }
        (by simpa using hl)
        (by simp [R₂, b2, b3])
        (by simp [R₂, a1, a3, a4, hs]) rfl
      refine ⟨v', hu, Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (spreadStep src mask ts tm dst) (mk v S)) he)
        (by simp; ring) ?_⟩
      congr 2
      funext k
      simp [loopR, R₂, spreadL, Function.update_apply, c1, c2, d1, Ne.symm b1]
      split_ifs <;> simp_all
    | true =>
      obtain ⟨s, ss, rfl⟩ : ∃ s ss', ss = s :: ss' := by
        cases ss with
        | nil => simp at hl
        | cons s ss' => exact ⟨s, ss', rfl⟩
      simp only [List.count_cons, ite_true, beq_self_eq_true, List.length_cons,
        Nat.add_right_cancel_iff] at hl
      have hs' : S.R src = bitSymbol s :: (ss ++ rest).map bitSymbol := hs
      set R₂ := Function.update (Function.update (Function.update (Function.update (Function.update
        S.R mask (ms.map bitSymbol)) tm (bitSymbol true :: S.R tm)) src ((ss ++ rest).map bitSymbol))
        ts (bitSymbol s :: S.R ts)) dst (bitSymbol s :: S.R dst) with hR₂
      have hrun : (spreadStep src mask ts tm dst : Act T Q A U).run (mk v S) =
          mk { v with sym := some (bitSymbol s), flag := ms.head?.isSome }
            { S with R := R₂ } := by
        simp [spreadStep, Action.run, peekR, update_rt, hm', hs', R₂,
          a1, a3, b1, b2, b3, c1, Ne.symm a1, Ne.symm a2, Ne.symm a4,
          Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm c2, Ne.symm d1]
      obtain ⟨v', hu, he⟩ := ih ss rest
        { v with sym := some (bitSymbol s), flag := ms.head?.isSome } { S with R := R₂ }
        (by simpa using hl)
        (by simp [R₂, Ne.symm a1, b1, b2, b3])
        (by simp [R₂, a2, a4]) rfl
      refine ⟨v', hu, Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (spreadStep src mask ts tm dst) (mk v S)) he)
        (by simp; ring) ?_⟩
      congr 2
      funext k
      simp [loopR, R₂, spreadL, Function.update_apply, c2, d1, Ne.symm a3,
        Ne.symm c1]
      split_ifs <;> simp_all

/-- **Spreading.** With `mask` holding `ms`, `src` holding `ss` with one bit per set mask bit,
and the spares empty, `out` gains `spreadL ss ms` on top; every other register ends as it
started. -/
theorem spread_exec {src mask ts tm dst out : Fin T} (h : GSRegs src mask ts tm dst out)
    (ms ss : List Bool) (hl : ms.count true = ss.length) (v : HS T Q A U) (S : Stacks T A)
    (hm : S.R mask = ms.map bitSymbol) (hs : S.R src = ss.map bitSymbol)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 8 * ms.length + 8 ∧
      Exec body (spread src mask ts tm dst out) (mk v S) m
        (mk v' { S with R := Function.update S.R out ((spreadL ss ms).map bitSymbol ++ S.R out) }) := by
  have hn := h
  simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1⟩ := hn
  have h5 : [src, mask, ts, tm, dst].Nodup := by
    simp [a1, a2, a3, a4, b1, b2, b3, c1, c2, d1]
  have a1' := Ne.symm a1; have a2' := Ne.symm a2; have a3' := Ne.symm a3
  have a4' := Ne.symm a4; have a5' := Ne.symm a5; have b1' := Ne.symm b1
  have b2' := Ne.symm b2; have b3' := Ne.symm b3; have b4' := Ne.symm b4
  have c1' := Ne.symm c1; have c2' := Ne.symm c2; have c3' := Ne.symm c3
  have d1' := Ne.symm d1; have d2' := Ne.symm d2; have e1' := Ne.symm e1
  obtain ⟨v₁, hu₁, he₁⟩ := spread_loop body h5 ms ss [] { v with flag := (S.R mask).head?.isSome }
    S hl hm (by simpa using hs) (by rw [hm]; cases ms <;> rfl)
  set R₁ := loopR S.R src mask ts tm dst [] ss ms (spreadL ss ms) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tm mask (Ne.symm b2) id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ tm mask id (R₁ tm) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body ts src (Ne.symm a2) id v₂ { S with R := R₂ }
  set R₃ := movedR R₂ ts src id (R₂ ts) with hR₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body dst out e1 id v₃ { S with R := R₃ }
  have hsp := length_spreadL ss ms
  have hcount := List.count_le_length (a := true) (l := ms)
  have ht₁ : R₁ tm = (ms.map bitSymbol).reverse := by
    simp [hR₁, loopR, htm, d1, c1']
  have hs₁ : R₁ ts = (ss.map bitSymbol).reverse := by
    simp [hR₁, loopR, hts, c2]
  have hd₁ : R₁ dst = ((spreadL ss ms).map bitSymbol).reverse := by
    simp [hR₁, loopR, hdst]
  have hs₂ : R₂ ts = (ss.map bitSymbol).reverse := by
    simp [hR₂, movedR, Ne.symm b1, hs₁, c1]
  have hd₃ : R₃ dst = ((spreadL ss ms).map bitSymbol).reverse := by
    simp [hR₃, hR₂, movedR, Ne.symm a4, Ne.symm b3, hd₁, a1, a3, c1, b1', c2', d1']
  refine ⟨v₄, 1 + (2 * ms.length + 1) + ((2 * (R₁ tm).length + 2) + ((2 * (R₂ ts).length + 2) +
    (2 * (R₃ dst).length + 2))), by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq (Exec.seq (peekR_run mask v S ▸ Exec.act (body := body) (peekR mask) (mk v S)) he₁)
      (Exec.seq he₂ (Exec.seq he₃ (Exec.cast he₄ rfl ?_)))⟩
  · rw [ht₁, hs₂, hd₃]
    simp only [List.length_reverse, List.length_map]
    omega
  · congr 2
    funext k
    simp [hR₃, hR₂, hR₁, movedR, loopR, Function.update_apply, hts, htm, hdst, a1, a2,
      a3, a4, b1, b2, b3, c1, c2, d1, Ne.symm a1,
      Ne.symm a4, Ne.symm a5, Ne.symm b1, Ne.symm b3, Ne.symm b4, Ne.symm c1,
      Ne.symm c2, Ne.symm c3, Ne.symm d1, Ne.symm d2, Ne.symm e1]
    split_ifs <;> simp_all

end Machine

end IntegerMultBounds.MathlibTM2.Host
