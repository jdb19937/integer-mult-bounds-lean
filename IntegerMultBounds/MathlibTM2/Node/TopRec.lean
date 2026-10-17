module

public import IntegerMultBounds.MathlibTM2.Node.Params
public import IntegerMultBounds.MathlibTM2.Host.Route
import Mathlib.Tactic.IntervalCases

/-!
# Records of unary fields, residues and dispatch

Host utilities for the machine of the simultaneous layer (`Node/TopProc.lean`); every `_exec`
theorem gives the final register file exactly and `v'.user = v.user`.

**Records.** `topRec l` stores the list of numbers `l` as unary fields, each field `x` being `x`
ticks followed by the separator `topSep = bitSymbol false`, the first field on top.
`topField src bk dst b` moves the top field of `src` onto `bk` (its ticks also onto `dst` when
`b`), `topSkips` moves `i` fields, and `topGet cf t₁ dst i` copies field `i` of the record on
`cf` onto `dst` as ticks and restores `cf` through the empty spare `t₁` (`topGet_exec`).

**Residues and dispatch.** `topResid W i t cs` puts `|i| mod W` into the scan slot `cs`
(`topResid_exec`), and `topDisp8 cs p` runs `p q` for the value `q < 8` of the scan slot `cs`
(`topDisp8_exec`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host


variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Records -/

/-- The separator of the fields of a record. -/
def topSep : Fin (A + 4) := bitSymbol false

/-- A record of unary fields: each number `x` of `l` as `x` ticks and a separator. -/
def topRec (l : List ℕ) : List (Fin (A + 4)) :=
  l.flatMap fun x => List.replicate x tick ++ [topSep]

lemma topSep_ne_tick : (topSep : Fin (A + 4)) ≠ tick := by
  simp [topSep, tick, bitSymbol, Fin.ext_iff]

@[simp] lemma topRec_nil : (topRec [] : List (Fin (A + 4))) = [] := rfl

lemma topRec_cons (x : ℕ) (l : List ℕ) :
    (topRec (x :: l) : List (Fin (A + 4))) = List.replicate x tick ++ topSep :: topRec l := by
  simp [topRec]

lemma topRec_append (l l' : List ℕ) :
    (topRec (l ++ l') : List (Fin (A + 4))) = topRec l ++ topRec l' := by
  simp [topRec]

lemma length_topRec (l : List ℕ) :
    (topRec l : List (Fin (A + 4))).length = (l.map (· + 1)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [topRec_cons, ih]; ring

/-- Record in `flag` whether the top of `x` is a tick. -/
def peekTick (x : Fin T) : Act T Q A U :=
  .peek (.rt x) (fun v o => { v with flag := decide (o = some tick) }) .done

lemma topMoveStep_run {i j : Fin T} (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4))
    {x : Fin (A + 4)} {rest : List (Fin (A + 4))} (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R i = x :: rest) :
    (moveStep i j f : Act T Q A U).run (mk v S) =
      mk { v with sym := some x, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R i rest) j (f x :: S.R j) } := by
  simp [moveStep, peekR, Action.run, hS, update_rt, Function.update_of_ne hij,
    Function.update_of_ne hij.symm]

/-- One tick of a field: the top of `src` onto `bk`, a tick onto `dst` when `b`. -/
def topFieldStep (src bk dst : Fin T) (b : Bool) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.push (.rt bk) (fun v => v.sym.getD blank)
      (if b then .push (.rt dst) (fun _ => tick) (peekTick src) else peekTick src))

/-- Move the top field of `src` onto `bk` (its ticks also onto `dst` when `b`), then its
separator. -/
def topField (src bk dst : Fin T) (b : Bool) : Pr P T Q A U :=
  .seq (.act (peekTick src))
    (.seq (.loop (·.flag) (.act (topFieldStep src bk dst b))) (.act (moveStep src bk id)))

theorem topField_loop {src bk dst : Fin T} (hsb : src ≠ bk) (hsd : src ≠ dst) (hbd : bk ≠ dst)
    (b : Bool) (rest : List (Fin (A + 4))) :
    ∀ (k : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R src = List.replicate k tick ++ topSep :: rest → v.flag = decide (0 < k) →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (topFieldStep src bk dst b))) (mk v S) (2 * k + 1)
          (mk v' { S with
            R := Function.update (Function.update (Function.update S.R src (topSep :: rest)) bk
              (List.replicate k tick ++ S.R bk)) dst
                (if b then List.replicate k tick ++ S.R dst else S.R dst) }) := by
  intro k
  induction k with
  | zero =>
      intro v S hs hf
      refine ⟨v, rfl, ?_⟩
      have hR : ({ S with
          R := Function.update (Function.update (Function.update S.R src (topSep :: rest)) bk
            (List.replicate 0 tick ++ S.R bk)) dst
              (if b then List.replicate 0 tick ++ S.R dst else S.R dst) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hs ⊢
          congr 1
          funext j
          by_cases hj : j = dst
          · subst hj; cases b <;> simp
          · by_cases hj' : j = bk
            · subst hj'; simp [hj]
            · by_cases hj'' : j = src
              · subst hj''; simp [hj, hj', hs]
              · simp [hj, hj', hj'']
      rw [hR]
      exact .loop_false (by simpa using hf)
  | succ k ih =>
      intro v S hs hf
      have hrun : (topFieldStep src bk dst b : Act T Q A U).run (mk v S) =
          mk { v with sym := some tick, flag := decide (0 < k) }
            { S with
              R := Function.update (Function.update (Function.update S.R src
                (List.replicate k tick ++ topSep :: rest)) bk (tick :: S.R bk)) dst
                  (if b then tick :: S.R dst else S.R dst) } := by
        cases b <;> cases k <;>
          simp [topFieldStep, peekTick, Action.run, hs, update_rt, Function.update_of_ne hsb,
            Function.update_of_ne hsd, Function.update_of_ne hsb.symm,
            Function.update_of_ne hsd.symm, Function.update_of_ne hbd.symm, List.replicate_succ,
            topSep_ne_tick] <;>
          (congr 2; funext j; simp only [Function.update_apply]; split_ifs <;> simp_all)
      obtain ⟨v', hu, he⟩ := ih { v with sym := some tick, flag := decide (0 < k) }
        { S with
          R := Function.update (Function.update (Function.update S.R src
            (List.replicate k tick ++ topSep :: rest)) bk (tick :: S.R bk)) dst
              (if b then tick :: S.R dst else S.R dst) }
        (by simp [Function.update_of_ne hsb, Function.update_of_ne hsd]) rfl
      refine ⟨v', hu, Exec.cast (Exec.loop_true (by simpa using hf)
        (hrun ▸ Exec.act (body := body) _ (mk v S)) he) (by ring) ?_⟩
      congr 2
      funext j
      by_cases hj : j = dst
      · subst hj; cases b <;> simp [List.replicate_succ']
      · by_cases hj' : j = bk
        · subst hj'; simp [hj, List.replicate_succ']
        · by_cases hj'' : j = src
          · subst hj''; simp [hj, hj']
          · simp [hj, hj', hj'']

theorem topField_exec {src bk dst : Fin T} (hsb : src ≠ bk) (hsd : src ≠ dst) (hbd : bk ≠ dst)
    (b : Bool) (k : ℕ) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = List.replicate k tick ++ topSep :: rest) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (topField src bk dst b) (mk v S) (2 * k + 3)
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R src rest) bk
            (topSep :: List.replicate k tick ++ S.R bk)) dst
              (if b then List.replicate k tick ++ S.R dst else S.R dst) }) := by
  have h0 := Exec.act (body := body) (peekTick src : Act T Q A U) (mk v S)
  have hrun : (peekTick src : Act T Q A U).run (mk v S) =
      mk { v with flag := decide (0 < k) } S := by
    cases k <;> simp [peekTick, Action.run, hs, topSep_ne_tick, List.replicate_succ]
  rw [hrun] at h0
  obtain ⟨v₁, hu₁, h1⟩ := topField_loop body hsb hsd hbd b rest k
    { v with flag := decide (0 < k) } S
    hs rfl
  set R₁ := Function.update (Function.update (Function.update S.R src (topSep :: rest)) bk
    (List.replicate k tick ++ S.R bk)) dst
      (if b then List.replicate k tick ++ S.R dst else S.R dst) with hR₁
  have h2 := Exec.act (body := body) (moveStep src bk id : Act T Q A U) (mk v₁ { S with R := R₁ })
  have hR₁s : R₁ src = topSep :: rest := by simp [hR₁, Function.update_of_ne hsd, hsb]
  rw [topMoveStep_run hsb id v₁ { S with R := R₁ } hR₁s] at h2
  refine ⟨{ v₁ with sym := some topSep, flag := rest.head?.isSome }, hu₁,
    Exec.cast (Exec.seq h0 (Exec.seq h1 h2)) (by ring) ?_⟩
  congr 2
  funext j
  by_cases hj : j = dst
  · subst hj; simp [hR₁, hbd.symm, hsd.symm]
  · by_cases hj' : j = bk
    · subst hj'; simp [hR₁, hj]
    · by_cases hj'' : j = src
      · subst hj''; simp [hR₁, hj, hj']
      · simp [hR₁, hj, hj', hj'']

/-- Move `i` fields of `src` onto `bk`. -/
def topSkips (src bk dst : Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | i + 1 => .seq (topField src bk dst false) (topSkips src bk dst i)

theorem topSkips_exec {src bk dst : Fin T} (hsb : src ≠ bk) (hsd : src ≠ dst) (hbd : bk ≠ dst) :
    ∀ (i : ℕ) (l : List ℕ) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      i ≤ l.length → S.R src = topRec l ++ rest →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (topSkips src bk dst i) (mk v S)
          (2 * (topRec (l.take i) : List (Fin (A + 4))).length + i + 1)
          (mk v' { S with
            R := Function.update (Function.update S.R src (topRec (l.drop i) ++ rest)) bk
              ((topRec (l.take i)).reverse ++ S.R bk) })
  | 0, l, rest, v, S, _, hs => by
      refine ⟨v, rfl, ?_⟩
      have hR : ({ S with
          R := Function.update (Function.update S.R src (topRec (l.drop 0) ++ rest)) bk
            ((topRec (l.take 0)).reverse ++ S.R bk) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hs ⊢
          congr 1
          funext j
          by_cases hj : j = bk
          · subst hj; simp
          · by_cases hj' : j = src
            · subst hj'; simp [hj, hs]
            · simp [hj, hj']
      rw [hR]
      simpa [topSkips] using Exec.act (body := body) (.done : Act T Q A U) (mk v S)
  | i + 1, [], rest, v, S, hi, _ => by simp at hi
  | i + 1, x :: l, rest, v, S, hi, hs => by
      obtain ⟨v₁, hu₁, h1⟩ := topField_exec body hsb hsd hbd false x (topRec l ++ rest) v S
        (by rw [hs, topRec_cons]; simp)
      obtain ⟨v₂, hu₂, h2⟩ := topSkips_exec hsb hsd hbd i l rest v₁
        { S with
          R := Function.update (Function.update (Function.update S.R src (topRec l ++ rest)) bk
            (topSep :: List.replicate x tick ++ S.R bk)) dst
              (if false = true then List.replicate x tick ++ S.R dst else S.R dst) }
        (by simpa using hi) (by simp [Function.update_of_ne hsd, hsb])
      refine ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq h1 h2) ?_ ?_⟩
      · simp [topRec_cons, length_topRec]; ring
      · congr 2
        funext j
        by_cases hj : j = bk
        · subst hj; simp [hbd, topRec_cons]
        · by_cases hj' : j = src
          · subst hj'; simp [hj]
          · simp only [Function.update_apply]; split_ifs <;> simp_all

/-- The number of symbols of `topRec l`. -/
def topRecLen (l : List ℕ) : ℕ := (l.map (· + 1)).sum

lemma length_topRec' (l : List ℕ) : (topRec l : List (Fin (A + 4))).length = topRecLen l :=
  length_topRec l

/-- Copy field `i` of the record on `cf` onto `dst` as ticks, through the empty spare `t₁`. -/
def topGet (cf t₁ dst : Fin T) (i : ℕ) : Pr P T Q A U :=
  .seq (topSkips cf t₁ dst i) (.seq (topField cf t₁ dst true) (moveR t₁ cf id))

/-- The step bound of `topGet` on the record of `l`. -/
def topGetCost (l : List ℕ) : ℕ := 8 * topRecLen l + 8

/-- **Reading a field.** With `cf` holding `topRec l ++ rest` and `t₁` empty, `topGet` pushes
`l[i]` ticks onto `dst`; every other register ends as it started. -/
theorem topGet_exec {cf t₁ dst : Fin T} (hreg : [cf, t₁, dst].Nodup) (l : List ℕ) (i : ℕ)
    (hi : i < l.length) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hcf : S.R cf = topRec l ++ rest) (ht : S.R t₁ = []) :
    ∃ (v' : HS T Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topGetCost l ∧
      Exec body (topGet cf t₁ dst i) (mk v S) c
        (mk v' { S with R := Function.update S.R dst (List.replicate l[i] tick ++ S.R dst) }) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil] at hreg
  obtain ⟨⟨hct, hcd⟩, htd⟩ := hreg
  obtain ⟨v₁, hu₁, h1⟩ := topSkips_exec body hct hcd htd i l rest v S hi.le hcf
  have hdrop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
  set R₁ := Function.update (Function.update S.R cf (topRec (l.drop i) ++ rest)) t₁
    ((topRec (l.take i)).reverse ++ S.R t₁) with hR₁
  obtain ⟨v₂, hu₂, h2⟩ := topField_exec body hct hcd htd true l[i] (topRec (l.drop (i + 1)) ++ rest)
    v₁ { S with R := R₁ } (by
      show R₁ cf = _
      rw [hR₁, Function.update_of_ne hct, Function.update_self, hdrop, topRec_cons]
      simp)
  simp only [ite_true] at h2
  set R₂ := Function.update (Function.update (Function.update R₁ cf
    (topRec (l.drop (i + 1)) ++ rest))
    t₁ (topSep :: List.replicate l[i] tick ++ R₁ t₁)) dst (List.replicate l[i] tick ++ R₁ dst)
    with hR₂
  obtain ⟨v₃, hu₃, h3⟩ := moveR_exec body t₁ cf (Ne.symm hct) id v₂ { S with R := R₂ }
  have htake : topRec (l.take (i + 1)) =
      (topRec (l.take i) ++ List.replicate l[i] tick ++ [topSep] : List (Fin (A + 4))) := by
    rw [List.take_succ_eq_append_getElem hi, topRec_append]
    simp [topRec]
  have hR₂t : R₂ t₁ = topSep :: List.replicate l[i] tick ++ (topRec (l.take i)).reverse := by
    simp [hR₂, hR₁, htd, ht]
  have hlen : (topRec (l.take i) : List (Fin (A + 4))).length + l[i] + 1 ≤ topRecLen l := by
    have h1 := congrArg List.length (congrArg (topRec (A := A)) (List.take_append_drop (i + 1) l))
    rw [topRec_append, List.length_append, htake] at h1
    simp only [List.length_append, List.length_replicate, List.length_singleton] at h1
    rw [← length_topRec' (A := A) l]
    omega
  have hil : i + 1 ≤ topRecLen l := by
    have : l.length ≤ topRecLen l := by
      unfold topRecLen
      induction l with
      | nil => simp
      | cons x l ih => simp; omega
    omega
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq h1 (Exec.seq h2 h3)) rfl ?_⟩
  · dsimp only
    rw [hR₂t]
    simp only [List.length_cons, List.length_append, List.length_replicate, List.length_reverse]
    unfold topGetCost
    omega
  · congr 2
    funext j
    by_cases hj : j = cf
    · subst hj
      have hR₂c : R₂ j = topRec (l.drop (i + 1)) ++ rest := by
        rw [hR₂, Function.update_of_ne hcd, Function.update_of_ne hct, Function.update_self]
      rw [Function.update_of_ne hcd, hcf]
      simp only [movedR, Function.update_self, List.map_id]
      rw [hR₂t, hR₂c]
      conv_rhs => rw [← List.take_append_drop (i + 1) l, topRec_append, htake]
      simp
    by_cases hj' : j = t₁
    · subst hj'; simp [movedR, ht, hj, Function.update_of_ne htd]
    by_cases hj'' : j = dst
    · subst hj''; simp [movedR, hR₂, hR₁, (Ne.symm hcd), (Ne.symm htd)]
    simp [movedR, hR₂, hR₁, hj, hj', hj'']

/-! ### Residues and dispatch -/

/-- Move the top of `i` onto `j` and advance the counter in the scan slot `cs` modulo `W`. -/
def topCntStep (W : ℕ) (i j cs : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.push (.rt j) (fun v => v.sym.getD blank)
      (.load (fun v => { v with scan := Function.update v.scan cs (nextC W (v.scan cs)) })
        (peekR i)))

theorem topCntStep_loop {W : ℕ} (hW1 : 1 ≤ W) (hW : W ≤ A + 4) {i j : Fin T} (hij : i ≠ j)
    (cs : Fin T) :
    ∀ (l : List (Fin (A + 4))) (c : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R i = l → v.flag = l.head?.isSome → (v.scan cs).val = c % W →
      ∃ v', v'.user = v.user ∧ (v'.scan cs).val = (c + l.length) % W ∧
        Exec body (.loop (·.flag) (.act (topCntStep W i j cs))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := movedR S.R i j id l }) := by
  intro l
  induction l with
  | nil =>
      intro c v S hS hf hc
      refine ⟨v, rfl, by simpa using hc, ?_⟩
      have : ({ S with R := movedR S.R i j id [] } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk; simp [movedR]
          · by_cases hk' : k = i
            · subst hk'; simp [movedR, hk, hS]
            · simp [movedR, hk, hk']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro c v S hS hf hc
      have hn := nextC_val (A := A) (W := W) (n := c) hW1 hW hc
      obtain ⟨v', hu, hsc, he⟩ := ih (c + 1)
        { v with sym := some e, scan := Function.update v.scan cs (nextC W (v.scan cs)),
                 flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R i rest) j (e :: S.R j) }
        (by simp [Function.update_of_ne hij]) rfl (by simpa using hn)
      refine ⟨v', hu, by rw [hsc, List.length_cons]; ring_nf, ?_⟩
      have hrun : (topCntStep W i j cs : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, scan := Function.update v.scan cs (nextC W (v.scan cs)),
                      flag := rest.head?.isSome }
            { S with R := Function.update (Function.update S.R i rest) j (e :: S.R j) } := by
        simp [topCntStep, peekR, Action.run, hS, update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (topCntStep W i j cs) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = j
      · subst hk; simp [movedR]
      · by_cases hk' : k = i
        · subst hk'; simp [movedR, hk]
        · simp [movedR, hk, hk']

/-- The residue of `|i|` modulo `W` into the scan slot `cs`, through the empty spare `t`. -/
def topResid (W : ℕ) (i t cs : Fin T) : Pr P T Q A U :=
  .seq (.act (initCounter cs i)) (.seq (.loop (·.flag) (.act (topCntStep W i t cs))) (moveR t i id))

/-- `topResid`: the registers end as they started and the scan slot `cs` holds `|i| mod W`. -/
theorem topResid_exec {W : ℕ} (hW1 : 1 ≤ W) (hW : W ≤ A + 4) {i t : Fin T} (hit : i ≠ t)
    (cs : Fin T) (v : HS T Q A U) (S : Stacks T A) (ht : S.R t = []) :
    ∃ v', v'.user = v.user ∧ (v'.scan cs).val = (S.R i).length % W ∧
      Exec body (topResid W i t cs) (mk v S) (4 * (S.R i).length + 4) (mk v' S) := by
  have he₀ := Exec.act (body := body) (initCounter cs i) (mk v S)
  have hrun : (initCounter cs i : Act T Q A U).run (mk v S) =
      mk { v with scan := Function.update v.scan cs 0, flag := (S.R i).head?.isSome } S := rfl
  rw [hrun] at he₀
  obtain ⟨v₁, hu₁, hsc₁, he₁⟩ := topCntStep_loop body hW1 hW hit cs (S.R i) 0
    { v with scan := Function.update v.scan cs 0, flag := (S.R i).head?.isSome } S rfl rfl
    (by simp)
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := moveR_exec_scan body t i (Ne.symm hit) id v₁
    { S with R := movedR S.R i t id (S.R i) }
  refine ⟨v₂, by rw [hu₂, hu₁], by rw [hsc₂, hsc₁, Nat.zero_add],
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ he₂)) ?_ ?_⟩
  · simp [movedR, ht]; ring
  · congr 1
    cases S with
    | mk inp out L R =>
      simp only at ht ⊢
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp [movedR, hit, ht]
      · by_cases hk' : k = t
        · subst hk'; simp [movedR, hk, ht]
        · simp [movedR, hk, hk']

/-- Run `p q` for the value `q < 8` of the scan slot `cs`. -/
def topDisp8 (cs : Fin T) (p : Fin 8 → Pr P T Q A U) : Pr P T Q A U :=
  .cond (fun v => decide ((v.scan cs).val = 0)) (p 0)
    (.cond (fun v => decide ((v.scan cs).val = 1)) (p 1)
    (.cond (fun v => decide ((v.scan cs).val = 2)) (p 2)
    (.cond (fun v => decide ((v.scan cs).val = 3)) (p 3)
    (.cond (fun v => decide ((v.scan cs).val = 4)) (p 4)
    (.cond (fun v => decide ((v.scan cs).val = 5)) (p 5)
    (.cond (fun v => decide ((v.scan cs).val = 6)) (p 6) (p 7)))))))

/-- `topDisp8` runs the branch of the value `q` of the scan slot, in at most seven more steps. -/
lemma topDisp8_exec (cs : Fin T) (p : Fin 8 → Pr P T Q A U) (q : Fin 8) (v : HS T Q A U)
    (S : Stacks T A) (hq : (v.scan cs).val = q.val) {c : ℕ}
    {t : Store (HΓ (T := T) A) (HS T Q A U)} (h : Exec body (p q) (mk v S) c t) :
    ∃ c', c' ≤ c + 7 ∧ Exec body (topDisp8 cs p) (mk v S) c' t := by
  obtain ⟨q, hq8⟩ := q
  simp only at hq
  interval_cases q
  · refine ⟨c + 1, by omega, ?_⟩
    exact .cond_true (by simp [hq]) h
  · refine ⟨c + 2, by omega, ?_⟩
    exact .cond_false (by simp [hq])
      (.cond_true (by simp [hq]) h)
  · refine ⟨c + 3, by omega, ?_⟩
    exact .cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_true (by simp [hq]) h))
  · refine ⟨c + 4, by omega, ?_⟩
    exact .cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_true (by simp [hq]) h)))
  · refine ⟨c + 5, by omega, ?_⟩
    exact .cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_true (by simp [hq]) h))))
  · refine ⟨c + 6, by omega, ?_⟩
    exact .cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_true (by simp [hq]) h)))))
  · refine ⟨c + 7, by omega, ?_⟩
    exact .cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_true (by simp [hq]) h))))))
  · refine ⟨c + 7, by omega, ?_⟩
    exact .cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (.cond_false (by simp [hq])
      (h)))))))

end IntegerMultBounds.MathlibTM2.Node
