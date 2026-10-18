module

public import IntegerMultBounds.MathlibTM2.DFT.IO
public import IntegerMultBounds.MathlibTM2.DFT.Fields
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-!
# Moving numbers between host registers and the multiplier's input and output

The fast multiplier reads `pairEnc (x, y)` from the host stack `.inp` and leaves
`encodeNat (x * y)` on `.out`. These host procedures connect those stacks to binary registers
(`binSyms L x`, least significant bit on top).

* `drainInp t tag` pops register `t` onto `.inp`, each bit `b` as `tag b`; `drainOut t` pops
  `.out` onto register `t`, each bit as `bitSymbol` (`drainInp_exec`, `drainOut_exec`).
* `pushNat s t₁ t₂ t₃ tag`: `.inp` gains `(encodeNat y).map tag` on top for `s` holding
  `binSyms L y`; `s` is kept and the scratch registers end empty (`pushNat_exec`,
  `10 L + 12` steps). Pushing `y` with `Sum.inr`, then `x` with `Sum.inl`, leaves
  `pairEnc (x, y)` on `.inp`.
* `readProduct c a b t₁ … t₅`: `.out` holding `encodeNat z` for `z < 2 ^ (La + Lb)` moves onto
  the empty register `c` as `binSyms (La + Lb) z`, where `La`, `Lb` are the lengths of
  registers `a`, `b`, which are kept (`readProduct_exec`).
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-! ### Register onto `.inp` -/

/-- Pop register `t`, push its bit onto `.inp` under `tag`, and test `t` again. -/
def inpStep (t : Fin T) (tag : Bool → Bool ⊕ Bool) : Act T Q A U :=
  .pop (.rt t) (fun v o => { v with sym := o })
    (.push .inp (fun v => tag (symBit (v.sym.getD blank))) (peekR t))

/-- Move register `t` onto `.inp`, each bit `b` as `tag b`. -/
def drainInp (t : Fin T) (tag : Bool → Bool ⊕ Bool) : Pr P T Q A U :=
  .seq (.act (peekR t)) (.loop (·.flag) (.act (inpStep t tag)))

theorem inpStep_run (t : Fin T) (tag : Bool → Bool ⊕ Bool) (x : Fin (A + 4))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A) (hS : S.R t = x :: rest) :
    (inpStep t tag : Act T Q A U).run (mk v S) =
      mk { v with sym := some x, flag := rest.head?.isSome }
        { S with inp := tag (symBit x) :: S.inp, R := Function.update S.R t rest } := by
  simp [inpStep, peekR, Action.run, hS, update_rt, update_inp]

theorem drainInp_loop (t : Fin T) (tag : Bool → Bool ⊕ Bool) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), S.R t = l →
      v.flag = l.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (inpStep t tag))) (mk v S) (2 * l.length + 1)
          (mk v' { S with
            inp := (l.map fun x => tag (symBit x)).reverse ++ S.inp
            R := Function.update S.R t [] })
  | [], v, S, hS, hf => by
      refine ⟨v, rfl, ?_⟩
      have hS' : ({ S with
          inp := (([] : List (Fin (A + 4))).map fun x => tag (symBit x)).reverse ++ S.inp
          R := Function.update S.R t [] } : Stacks T A) = S := by
        simp only [List.map_nil, List.reverse_nil, List.nil_append]
        rw [← hS, Function.update_eq_self]
      rw [hS']
      exact .loop_false (by simpa using hf)
  | x :: rest, v, S, hS, hf => by
      obtain ⟨v', hu, he⟩ := drainInp_loop t tag rest
        { v with sym := some x, flag := rest.head?.isSome }
        { S with inp := tag (symBit x) :: S.inp, R := Function.update S.R t rest } (by simp) rfl
      refine ⟨v', hu, ?_⟩
      have hact : Exec body (.act (inpStep t tag)) (mk v S) 1
          (mk { v with sym := some x, flag := rest.head?.isSome }
            { S with inp := tag (symBit x) :: S.inp, R := Function.update S.R t rest }) := by
        rw [← inpStep_run t tag x rest v S hS]
        exact .act _ _
      refine Exec.cast (Exec.loop_true (f := (·.flag)) (by simpa using hf) hact he)
        (by simp only [List.length_cons]; ring) ?_
      simp [Function.update_idem]

/-- `drainInp t tag`: `.inp` gains register `t`, read as bits under `tag`, reversed; `t`
empties. -/
theorem drainInp_exec (t : Fin T) (tag : Bool → Bool ⊕ Bool) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (drainInp t tag) (mk v S) (2 * (S.R t).length + 2)
        (mk v' { S with
          inp := ((S.R t).map fun x => tag (symBit x)).reverse ++ S.inp
          R := Function.update S.R t [] }) := by
  obtain ⟨v', hu, he⟩ :=
    drainInp_loop body t tag (S.R t) { v with flag := (S.R t).head?.isSome } S rfl rfl
  exact ⟨v', hu, Exec.cast (Exec.seq (peekR_run t v S ▸ Exec.act (body := body) (peekR t)
    (mk v S)) he) (by ring) rfl⟩

/-! ### `.out` onto a register -/

/-- Record in `flag` whether `.out` is nonempty. -/
def peekOutH : Act T Q A U := .peek .out (fun v o => { v with flag := o.isSome }) .done

/-- Pop `.out`, push its bit onto register `t` as `bitSymbol`, and test `.out` again. -/
def outStep (t : Fin T) : Act T Q A U :=
  .pop .out (fun v o => { v with sym := o.map bitSymbol })
    (.push (.rt t) (fun v => v.sym.getD blank) peekOutH)

/-- Move `.out` onto register `t`. -/
def drainOut (t : Fin T) : Pr P T Q A U :=
  .seq (.act peekOutH) (.loop (·.flag) (.act (outStep t)))

theorem outStep_run (t : Fin T) (b : Bool) (rest : List Bool) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.out = b :: rest) :
    (outStep t : Act T Q A U).run (mk v S) =
      mk { v with sym := some (bitSymbol b), flag := rest.head?.isSome }
        { S with out := rest, R := Function.update S.R t (bitSymbol b :: S.R t) } := by
  simp [outStep, peekOutH, Action.run, hS, update_rt, update_out]

theorem drainOut_loop (t : Fin T) :
    ∀ (o : List Bool) (v : HS T Q A U) (S : Stacks T A), S.out = o →
      v.flag = o.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (outStep t))) (mk v S) (2 * o.length + 1)
          (mk v' { S with
            out := []
            R := Function.update S.R t ((o.map bitSymbol).reverse ++ S.R t) })
  | [], v, S, hS, hf => by
      refine ⟨v, rfl, ?_⟩
      have hS' : ({ S with
          out := []
          R := Function.update S.R t ((([] : List Bool).map bitSymbol).reverse ++ S.R t) } :
            Stacks T A) = S := by
        simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
        rw [← hS]
      rw [hS']
      exact .loop_false (by simpa using hf)
  | b :: rest, v, S, hS, hf => by
      obtain ⟨v', hu, he⟩ := drainOut_loop t rest
        { v with sym := some (bitSymbol b), flag := rest.head?.isSome }
        { S with out := rest, R := Function.update S.R t (bitSymbol b :: S.R t) } rfl rfl
      refine ⟨v', hu, ?_⟩
      have hact : Exec body (.act (outStep t)) (mk v S) 1
          (mk { v with sym := some (bitSymbol b), flag := rest.head?.isSome }
            { S with out := rest, R := Function.update S.R t (bitSymbol b :: S.R t) }) := by
        rw [← outStep_run t b rest v S hS]
        exact .act _ _
      refine Exec.cast (Exec.loop_true (f := (·.flag)) (by simpa using hf) hact he)
        (by simp only [List.length_cons]; ring) ?_
      simp [Function.update_idem]

/-- `drainOut t`: register `t` gains `.out` as `bitSymbol`s, reversed; `.out` empties. -/
theorem drainOut_exec (t : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (drainOut t) (mk v S) (2 * S.out.length + 2)
        (mk v' { S with
          out := []
          R := Function.update S.R t ((S.out.map bitSymbol).reverse ++ S.R t) }) := by
  obtain ⟨v', hu, he⟩ :=
    drainOut_loop body t S.out { v with flag := S.out.head?.isSome } S rfl rfl
  have hpeek : Exec body (.act peekOutH) (mk v S) 1 (mk { v with flag := S.out.head?.isSome } S) :=
    Exec.act (body := body) peekOutH (mk v S)
  exact ⟨v', hu, Exec.cast (Exec.seq hpeek he) (by ring) rfl⟩

/-! ### A number onto `.inp` -/

/-- Push `y` in shortest form onto `.inp` under `tag`, for register `s` holding `binSyms L y`:
copy `s` onto `t₁`, reverse it onto `t₂`, drop the high zeros, and drain `t₂`. -/
def pushNat (s t₁ t₂ t₃ : Fin T) (tag : Bool → Bool ⊕ Bool) : Pr P T Q A U :=
  .seq (bcopy s t₁ t₂ t₃) (.seq (moveR t₁ t₂ id) (.seq (stripZeros t₂) (drainInp t₂ tag)))

theorem binSyms_map_symBit (L y : ℕ) (tag : Bool → Bool ⊕ Bool) :
    ((binSyms L y : List (Fin (A + 4))).map fun x => tag (symBit x)) = (binBits L y).map tag := by
  rw [binSyms_eq, List.map_map]
  congr 1
  funext b
  simp

/-- `pushNat`: `.inp` gains `(encodeNat y).map tag` on top; every register is kept. -/
theorem pushNat_exec {s t₁ t₂ t₃ : Fin T} (hreg : [s, t₁, t₂, t₃].Nodup)
    (tag : Bool → Bool ⊕ Bool) {L y : ℕ} (hy : y < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R s = binSyms L y) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) (h₃ : S.R t₃ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (pushNat s t₁ t₂ t₃ tag) (mk v S) (10 * L + 12)
        (mk v' { S with inp := (encodeNat y).map tag ++ S.inp }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hsize : Nat.size y ≤ L := Nat.size_le.2 hy
  have hlen : (binSyms (A := A) L y).length = L := by simp [binSyms]
  obtain ⟨v₁, hu₁, h₁e⟩ := bcopy_exec body (a := s) (c := t₁) (t₁ := t₂) (t₂ := t₃) hreg v S h₂ h₃
  rw [hs, hlen] at h₁e
  set S₁ : Stacks T A := { S with R := Function.update S.R t₁ (binSyms L y ++ S.R t₁) } with hS₁
  obtain ⟨v₂, hu₂, h₂e⟩ := moveR_exec body t₁ t₂ ‹t₁ ≠ t₂› id v₁ S₁
  have hS₁t : S₁.R t₁ = binSyms L y := by simp [hS₁, h₁]
  rw [hS₁t, hlen] at h₂e
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R t₁ t₂ id (binSyms L y) } with hS₂
  have hS₂t : S₂.R t₂ = List.replicate (L - Nat.size y) (bitSymbol false) ++
      (binSyms (Nat.size y) y).reverse := by
    simp [hS₂, hS₁, movedR, binSyms_size_pad hy, Ne.symm ‹t₁ ≠ t₂›, h₂]
  have hzero : zeroTop ((binSyms (A := A) (Nat.size y) y).reverse).head? = false := by
    simpa using zeroTop_binSyms_reverse (A := A) y [] rfl
  obtain ⟨v₃, hu₃, h₃e⟩ := stripZeros_exec body t₂ (L - Nat.size y) _ hzero v₂ S₂ hS₂t
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R t₂ (binSyms (Nat.size y) y).reverse }
    with hS₃
  obtain ⟨v₄, hu₄, h₄e⟩ := drainInp_exec body t₂ tag v₃ S₃
  have hS₃t : S₃.R t₂ = (binSyms (Nat.size y) y).reverse := by simp [hS₃]
  rw [hS₃t] at h₄e
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq h₁e (Exec.seq h₂e
    (Exec.seq h₃e h₄e))) ?_ ?_⟩
  · rw [List.length_reverse, binSyms, List.length_ofFn]
    omega
  · rw [List.map_reverse, List.reverse_reverse, binSyms_map_symBit, ← encodeNat_eq_binBits]
    simp only [hS₃, hS₂, hS₁]
    congr 2
    regs_ext

/-! ### The product onto a register -/

/-- Move `.out` onto the empty register `c` and widen it to `|a| + |b|` bits, through `t₁ … t₅`.
-/
def readProduct (c a b t₁ t₂ t₃ t₄ t₅ : Fin T) : Pr P T Q A U :=
  .seq (drainOut t₁) (.seq (moveR t₁ c id) (.seq (bcopy a t₂ t₃ t₄) (.seq (bcopy b t₂ t₃ t₄)
    (.seq (bwiden c t₂ t₃ t₄ t₅) (bclear t₂)))))

/-- `readProduct`: register `c` gets `binSyms (|a| + |b|) z` from `.out = encodeNat z`. -/
theorem readProduct_exec {c a b t₁ t₂ t₃ t₄ t₅ : Fin T}
    (hreg : [c, a, b, t₁, t₂, t₃, t₄, t₅].Nodup) {z : ℕ} (v : HS T Q A U) (S : Stacks T A)
    (hz : z < 2 ^ ((S.R a).length + (S.R b).length)) (hout : S.out = encodeNat z)
    (hc : S.R c = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) (h₃ : S.R t₃ = [])
    (h₄ : S.R t₄ = []) (h₅ : S.R t₅ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (readProduct c a b t₁ t₂ t₃ t₄ t₅) (mk v S)
        (4 * Nat.size z + 20 * ((S.R a).length + (S.R b).length) + 36)
        (mk v' { S with
          out := []
          R := Function.update S.R c (binSyms ((S.R a).length + (S.R b).length) z) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set W := (S.R a).length + (S.R b).length with hW
  have hsize : Nat.size z ≤ W := Nat.size_le.2 hz
  have hlenz : (encodeNat z).length = Nat.size z := by
    rw [encodeNat_eq_binBits, binBits, List.length_ofFn]
  -- `.out` onto `t₁`
  obtain ⟨v₁, hu₁, e₁⟩ := drainOut_exec body t₁ v S
  rw [hout, hlenz, h₁, List.append_nil] at e₁
  set S₁ : Stacks T A := { S with
    out := []
    R := Function.update S.R t₁ ((encodeNat z).map bitSymbol).reverse } with hS₁
  -- `t₁` onto `c`
  obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body t₁ c ‹c ≠ t₁›.symm id v₁ S₁
  have hS₁t : S₁.R t₁ = ((encodeNat z).map bitSymbol).reverse := by simp [hS₁]
  rw [hS₁t, List.length_reverse, List.length_map, hlenz] at e₂
  set S₂ : Stacks T A := { S₁ with
    R := movedR S₁.R t₁ c id ((encodeNat z).map bitSymbol).reverse } with hS₂
  have hS₂c : S₂.R c = binSyms (Nat.size z) z := by
    simp [hS₂, hS₁, movedR, ‹c ≠ t₁›, hc, binSyms_eq, encodeNat_eq_binBits]
  -- the width register `t₂`
  obtain ⟨v₃, hu₃, e₃⟩ := bcopy_exec body (a := a) (c := t₂) (t₁ := t₃) (t₂ := t₄)
    (by regs_nodup) v₂ S₂ (by simp [hS₂, hS₁, movedR, *, Ne.symm])
    (by simp [hS₂, hS₁, movedR, *, Ne.symm])
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R t₂ (S₂.R a ++ S₂.R t₂) } with hS₃
  obtain ⟨v₄, hu₄, e₄⟩ := bcopy_exec body (a := b) (c := t₂) (t₁ := t₃) (t₂ := t₄)
    (by regs_nodup) v₃ S₃ (by simp [hS₃, hS₂, hS₁, movedR, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, movedR, *, Ne.symm])
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R t₂ (S₃.R b ++ S₃.R t₂) } with hS₄
  have hS₂a : S₂.R a = S.R a := by simp [hS₂, hS₁, movedR, *, Ne.symm]
  have hS₂b : S₂.R b = S.R b := by simp [hS₂, hS₁, movedR, *, Ne.symm]
  have hS₄w : (S₄.R t₂).length = W := by
    simp [hS₄, hS₃, hS₂, hS₁, movedR, *, Ne.symm]
    omega
  -- widen `c`
  obtain ⟨v₅, hu₅, e₅⟩ := bwiden_exec body (a := c) (wR := t₂) (cnt := t₃) (t₁ := t₄) (t₂ := t₅)
    (by regs_nodup) hsize (Nat.lt_size_self z) v₄ S₄
    (by simp [hS₄, hS₃, ‹c ≠ t₂›, hS₂c]) hS₄w
    (by simp [hS₄, hS₃, hS₂, hS₁, movedR, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, movedR, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, movedR, *, Ne.symm])
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R c (binSyms W z) } with hS₅
  obtain ⟨v₆, hu₆, -, e₆⟩ := bclear_exec body t₂ v₅ S₅
  have hS₅w : (S₅.R t₂).length = W := by simp [hS₅, ‹c ≠ t₂›.symm, hS₄w]
  rw [hS₅w] at e₆
  rw [hS₂a] at e₃
  have hS₃b : S₃.R b = S.R b := by simp [hS₃, ‹b ≠ t₂›, hS₂b]
  rw [hS₃b] at e₄
  refine ⟨v₆, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂
    (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆))))) ?_ ?_⟩
  · omega
  · congr 1
    simp only [hS₅, hS₄, hS₃, hS₂, hS₁]
    congr 1
    regs_ext

end IntegerMultBounds.MathlibTM2.DFT
