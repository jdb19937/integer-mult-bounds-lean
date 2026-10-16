module

public import IntegerMultBounds.MathlibTM2.Host.Route
public import IntegerMultBounds.MathlibTM2.Host.Auto

/-!
# Index counters and code passes on host registers

A binary number on a register: `binSyms L a` is the list of the low `L` bits of `a` as
`bitSymbol`s, least significant bit on top.

**Field counter.** Registers `cf f`, `f : Fin nf`, hold an index `i` in the mixed radix with
field lengths `len` (field `0` least significant): register `cf f` holds
`binSyms (len f) (digit len f i)`, where `digit len f i = (i / 2 ^ fieldOff len f) % 2 ^ len f`
and `fieldOff len f` is the total length of the fields below `f`. `incrFields cf tmp cy` adds one
with carry from field `0` upward, wrapping modulo `2 ^ (∑ f, len f)` (`digit_mod`). Each field
moves bit by bit onto the empty register `tmp` and back, so every register keeps its
orientation; the carry lives in scan slot `cy`. `incrFields_exec`: exactly
`4 * (∑ f, len f) + 4 * nf + 2` steps, and only the registers `cf f` change.

**Code pass.** A code automaton `C : CAuto A nr nd` steps a state symbol on one bit of each of
`nr` values; `C.eval L vals` is its output after bits `0, …, L - 1` (`CAuto.run_eq_foldl`).
`codePass rs tmps st C` reads the registers `rs r`, each holding `binSyms L (vals r)`, in
parallel: one step of `C` per column, moving the column onto the empty registers `tmps r`, then
a second loop moves the columns back. `codePass_exec`: exactly `6 * L + 4` steps, every register
restored, and scan slot `st` holds `C.run L C.init vals`. The scan slots `rs r` and `tmps r`
serve as scratch.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2


variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nf nr nd : ℕ}

/-! ### Binary numerals -/

/-- The low `L` bits of `a`, least significant first. -/
def binBits (L a : ℕ) : List Bool := List.ofFn fun t : Fin L => a.testBit t

/-- The low `L` bits of `a` as register symbols, least significant bit on top. -/
def binSyms (L a : ℕ) : List (Fin (A + 4)) := List.ofFn fun t : Fin L => bitSymbol (a.testBit t)

lemma binSyms_eq (L a : ℕ) :
    (binSyms L a : List (Fin (A + 4))) = (binBits L a).map bitSymbol := by
  simp [binSyms, binBits, List.map_ofFn, Function.comp_def]

@[simp] lemma length_binBits (L a : ℕ) : (binBits L a).length = L := by simp [binBits]

@[simp] lemma length_binSyms (L a : ℕ) : (binSyms L a : List (Fin (A + 4))).length = L := by
  simp [binSyms]

@[simp] lemma binBits_zero (a : ℕ) : binBits 0 a = [] := rfl

lemma binBits_succ (L a : ℕ) : binBits (L + 1) a = a.testBit 0 :: binBits L (a / 2) := by
  simp [binBits, List.ofFn_succ, Nat.testBit_add_one]

lemma binSyms_succ (L a : ℕ) :
    (binSyms (L + 1) a : List (Fin (A + 4))) = bitSymbol (a.testBit 0) :: binSyms L (a / 2) := by
  simp [binSyms_eq, binBits_succ]

/-- Only the low `L` bits of `a` are written. -/
lemma binBits_mod (L a : ℕ) : binBits L (a % 2 ^ L) = binBits L a := by
  simp [binBits, Nat.testBit_mod_two_pow]

lemma binSyms_mod (L a : ℕ) : (binSyms L (a % 2 ^ L) : List (Fin (A + 4))) = binSyms L a := by
  simp [binSyms_eq, binBits_mod]

/-- Add the carry `c` to the bits `bs` (least significant first), dropping the carry out. -/
def incBits : Bool → List Bool → List Bool
  | _, [] => []
  | c, b :: bs => xor b c :: incBits (b && c) bs

/-- The carry out of `incBits c bs`. -/
def carryOut : Bool → List Bool → Bool
  | c, [] => c
  | c, b :: bs => carryOut (b && c) bs

@[simp] lemma length_incBits : ∀ (c : Bool) (bs : List Bool), (incBits c bs).length = bs.length
  | _, [] => rfl
  | c, b :: bs => by simp [incBits, length_incBits (b && c) bs]

lemma testBit_zero_add_toNat (a : ℕ) (c : Bool) :
    (a + c.toNat).testBit 0 = xor (a.testBit 0) c ∧
      (a + c.toNat) / 2 = a / 2 + (a.testBit 0 && c).toNat := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;> cases c <;>
    simp [Nat.testBit_zero, h] <;> omega

lemma incBits_binBits (c : Bool) (L a : ℕ) :
    incBits c (binBits L a) = binBits L (a + c.toNat) := by
  induction L generalizing a c with
  | zero => rfl
  | succ L ih =>
      obtain ⟨h0, h1⟩ := testBit_zero_add_toNat a c
      rw [binBits_succ, binBits_succ, incBits, ih, h0, h1]

lemma carryOut_binBits (c : Bool) (L a : ℕ) :
    (carryOut c (binBits L a)).toNat + a / 2 ^ L = (a + c.toNat) / 2 ^ L := by
  induction L generalizing a c with
  | zero => simp [carryOut, Nat.add_comm]
  | succ L ih =>
      obtain ⟨_, h1⟩ := testBit_zero_add_toNat a c
      rw [binBits_succ, carryOut, pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul,
        ← Nat.div_div_eq_div_mul, ih, h1]

/-! ### Mixed-radix fields -/

/-- Bit offset of field `f`: the total length of the fields below it. -/
def fieldOff (len : Fin nf → ℕ) (f : Fin nf) : ℕ :=
  ∑ g ∈ Finset.univ.filter (· < f), len g

/-- Digit `f` of the index `i` in the mixed radix with field lengths `len`, field `0` least
significant. -/
def digit (len : Fin nf → ℕ) (f : Fin nf) (i : ℕ) : ℕ := (i / 2 ^ fieldOff len f) % 2 ^ len f

lemma fieldOff_zero (len : Fin nf → ℕ) (f : Fin nf) (hf : f.val = 0) : fieldOff len f = 0 := by
  apply Finset.sum_eq_zero
  intro g hg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hg
  omega

lemma fieldOff_succ (len : Fin nf → ℕ) (j : ℕ) (h : j + 1 < nf) :
    fieldOff len ⟨j + 1, h⟩ = fieldOff len ⟨j, by omega⟩ + len ⟨j, by omega⟩ := by
  have hs : Finset.univ.filter (· < (⟨j + 1, h⟩ : Fin nf)) =
      insert ⟨j, by omega⟩ (Finset.univ.filter (· < (⟨j, by omega⟩ : Fin nf))) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
      Fin.ext_iff]
    omega
  rw [fieldOff, hs, Finset.sum_insert (by simp), Nat.add_comm]
  rfl

lemma fieldOff_add_le (len : Fin nf → ℕ) (f : Fin nf) :
    fieldOff len f + len f ≤ ∑ g, len g := by
  rw [fieldOff, Nat.add_comm, ← Finset.sum_insert (s := Finset.univ.filter (· < f)) (by simp)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Digits depend on the index modulo `2 ^ (∑ f, len f)`. -/
lemma digit_mod (len : Fin nf → ℕ) (f : Fin nf) (i : ℕ) :
    digit len f (i % 2 ^ ∑ g, len g) = digit len f i := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (fieldOff_add_le len f)
  unfold digit
  rw [he, Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Dvd.intro _ rfl)]


/-! ### Incrementing the field counter -/

/-- One bit of an increment: pop register `a` into `sym`, push the sum of the bit and the carry
(slot `cy`) onto `tmp`, update the carry, and record in `flag` whether `a` is nonempty. -/
def incStep (a tmp cy : Fin T) : Act T Q A U :=
  .pop (.rt a) (fun v o => { v with sym := o })
    (.push (.rt tmp) (fun v => bitSymbol (xor (symBit (v.sym.getD blank)) (symBit (v.scan cy))))
      (.load (fun v => { v with
          scan := Function.update v.scan cy (bitSymbol (symBit (v.sym.getD blank) && symBit (v.scan cy))) })
        (peekR a)))

/-- Add the carry in slot `cy` to the binary number in register `a`, through the empty
register `tmp`. -/
def incrField (a tmp cy : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR a)) (.seq (.loop (·.flag) (.act (incStep a tmp cy))) (moveR tmp a id))

/-- Set the carry in slot `cy`. -/
def setCarry (cy : Fin T) : Act T Q A U :=
  .load (fun v => { v with scan := Function.update v.scan cy (bitSymbol true) }) .done

/-- Add one to the index held by the field registers `cf`, carrying from field `0` upward;
the carry lives in scan slot `cy` and `tmp` is an empty spare register. -/
def incrFields (cf : Fin nf → Fin T) (tmp cy : Fin T) : Pr P T Q A U :=
  .seq (.act (setCarry cy)) (Prog.seqList ((List.finRange nf).map fun f => incrField (cf f) tmp cy))

theorem incStep_loop (a tmp cy : Fin T) (hat : a ≠ tmp) :
    ∀ (bs : List Bool) (c : Bool) (v : HS T Q A U) (S : Stacks T A),
      S.R a = bs.map bitSymbol → symBit (v.scan cy) = c → v.flag = bs.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧ symBit (v'.scan cy) = carryOut c bs ∧
        Exec body (.loop (·.flag) (.act (incStep a tmp cy))) (mk v S) (2 * bs.length + 1)
          (mk v' { S with
            R := Function.update (Function.update S.R a []) tmp
              (((incBits c bs).map bitSymbol).reverse ++ S.R tmp) }) := by
  intro bs
  induction bs with
  | nil =>
      intro c v S hS hc hf
      refine ⟨v, rfl, hc, ?_⟩
      have : ({ S with
          R := Function.update (Function.update S.R a []) tmp
            (((incBits c []).map bitSymbol).reverse ++ S.R tmp) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = tmp
          · subst hk; simp [incBits]
          · by_cases hk' : k = a
            · subst hk'; simp [hk, hS]
            · simp [hk, hk']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons b bs ih =>
      intro c v S hS hc hf
      obtain ⟨v', hu, hcy, he⟩ := ih (b && c)
        { v with
          sym := some (bitSymbol b)
          scan := Function.update v.scan cy (bitSymbol (b && c))
          flag := bs.head?.isSome }
        { S with
          R := Function.update (Function.update S.R a (bs.map bitSymbol)) tmp
            (bitSymbol (xor b c) :: S.R tmp) }
        (by simp [Function.update_of_ne hat]) (by simp) rfl
      refine ⟨v', hu, by rw [hcy]; rfl, ?_⟩
      have hrun : (incStep a tmp cy : Act T Q A U).run (mk v S) =
          mk { v with
              sym := some (bitSymbol b)
              scan := Function.update v.scan cy (bitSymbol (b && c))
              flag := bs.head?.isSome }
            { S with
              R := Function.update (Function.update S.R a (bs.map bitSymbol)) tmp
                (bitSymbol (xor b c) :: S.R tmp) } := by
        simp [incStep, peekR, Action.run, hS, hc, update_rt, Function.update_of_ne hat,
          Function.update_of_ne hat.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (incStep a tmp cy) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = tmp
      · subst hk; simp [incBits]
      · by_cases hk' : k = a
        · subst hk'; simp [hk]
        · simp [hk, hk']

/-- One field: the number in register `a` gains the carry `c`; the new carry is
`carryOut c bs`. Exactly `4 * |bs| + 4` steps. -/
theorem incrField_exec (a tmp cy : Fin T) (hat : a ≠ tmp) (bs : List Bool) (c : Bool)
    (v : HS T Q A U) (S : Stacks T A) (hS : S.R a = bs.map bitSymbol) (ht : S.R tmp = [])
    (hc : symBit (v.scan cy) = c) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ symBit (v'.scan cy) = carryOut c bs ∧
      Exec body (incrField a tmp cy) (mk v S) (4 * bs.length + 4)
        (mk v' { S with R := Function.update S.R a ((incBits c bs).map bitSymbol) }) := by
  obtain ⟨v₁, hu₁, hc₁, he₁⟩ := incStep_loop body a tmp cy hat bs c
    { v with flag := (S.R a).head?.isSome } S hS hc (by rw [hS]; simp)
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := moveR_exec_scan body tmp a hat.symm id v₁
    { S with
      R := Function.update (Function.update S.R a []) tmp
        (((incBits c bs).map bitSymbol).reverse ++ S.R tmp) }
  refine ⟨v₂, by rw [hu₂, hu₁], by rw [hsc₂, hc₁], Exec.cast (Exec.seq
    (peekR_run a v S ▸ Exec.act (body := body) (peekR a) (mk v S)) (Exec.seq he₁ he₂)) ?_ ?_⟩
  · simp [ht, length_incBits]; ring
  · congr 2
    funext k
    by_cases hk : k = a
    · subst hk; simp [movedR, ht, Function.update_of_ne hat]
    · by_cases hk' : k = tmp
      · subst hk'; simp [movedR, hk, ht]
      · simp [movedR, hk, hk']

/-- The field loop over a duplicate-free list `fs` of fields with bit offsets `off`
(consecutive fields of `fs` are adjacent), for the index `i`. -/
theorem incrList_exec (cf : Fin nf → Fin T) (hcf : Function.Injective cf) (tmp cy : Fin T)
    (htmp : ∀ f, cf f ≠ tmp) (len off : Fin nf → ℕ) (i : ℕ) :
    ∀ (fs : List (Fin nf)), fs.Nodup →
      (∀ j (h : j + 1 < fs.length), off fs[j + 1] = off fs[j] + len fs[j]) →
      ∀ (v : HS T Q A U) (S : Stacks T A), S.R tmp = [] →
      (∀ f ∈ fs.head?, (symBit (v.scan cy)).toNat + i / 2 ^ off f = (i + 1) / 2 ^ off f) →
      (∀ f ∈ fs, S.R (cf f) = binSyms (len f) (i / 2 ^ off f)) →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (Prog.seqList (fs.map fun f => incrField (cf f) tmp cy)) (mk v S)
          ((fs.map fun f => 4 * len f + 4).sum + 1) (mk v' { S with R := R' }) ∧
        (∀ f ∈ fs, R' (cf f) = binSyms (len f) ((i + 1) / 2 ^ off f)) ∧
        ∀ k, (∀ f ∈ fs, k ≠ cf f) → R' k = S.R k := by
  intro fs
  induction fs with
  | nil =>
      intro _ _ v S _ _ _
      exact ⟨v, S.R, rfl, by simpa [Prog.seqList] using Exec.act (body := body) .done (mk v S),
        by simp, fun _ _ => rfl⟩
  | cons f fs ih =>
      intro hnd hoff v S ht hcy hcf'
      rw [List.nodup_cons] at hnd
      have hc0 := hcy f rfl
      obtain ⟨v₁, hu₁, hc₁, he₁⟩ := incrField_exec body (cf f) tmp cy (htmp f)
        (binBits (len f) (i / 2 ^ off f)) (symBit (v.scan cy)) v S
        (by rw [hcf' f List.mem_cons_self, binSyms_eq]) ht rfl
      have hval : (incBits (symBit (v.scan cy)) (binBits (len f) (i / 2 ^ off f))).map bitSymbol =
          (binSyms (len f) ((i + 1) / 2 ^ off f) : List (Fin (A + 4))) := by
        rw [incBits_binBits, binSyms_eq, Nat.add_comm _ (Bool.toNat _), hc0]
      rw [hval] at he₁
      obtain ⟨v', R', hu, he, hfs, hoth⟩ := ih hnd.2
        (fun j h => by
          have := hoff (j + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at this
          exact this) v₁
        { S with R := Function.update S.R (cf f) (binSyms (len f) ((i + 1) / 2 ^ off f)) }
        (by simp [Function.update_of_ne (htmp f).symm, ht])
        (by
          intro g hg
          have hg' : fs[0]? = some g := by simpa [List.head?_eq_getElem?] using hg
          obtain ⟨h0, rfl⟩ := List.getElem?_eq_some_iff.1 hg'
          have hoff0 := hoff 0 (by simp; omega)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hoff0
          have hco := carryOut_binBits (symBit (v.scan cy)) (len f) (i / 2 ^ off f)
          rw [Nat.add_comm _ (Bool.toNat _), hc0, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
            ← Nat.pow_add, ← hoff0, ← hc₁] at hco
          exact hco)
        (by
          intro g hg
          have hgf : g ≠ f := fun h => hnd.1 (h ▸ hg)
          simp [Function.update_of_ne (fun h => hgf (hcf h)), hcf' g (List.mem_cons_of_mem _ hg)])
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.seq he₁ he) ?_ rfl, ?_, ?_⟩
      · simp [binBits]; ring
      · intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · rw [hoth _ (fun g' hg' h => hnd.1 (by rw [hcf h]; exact hg'))]
          simp
        · exact hfs g hg
      · intro k hk
        rw [hoth k (fun g hg => hk g (List.mem_cons_of_mem _ hg))]
        simp [Function.update_of_ne (hk f List.mem_cons_self)]

/-- Incrementing the field counter: registers `cf f` holding the digits of `i` end holding the
digits of `i + 1` (modulo `2 ^ (∑ f, len f)`, see `digit_mod`); every other register, `tmp`
included, is unchanged. Exactly `4 * (∑ f, len f) + 4 * nf + 2` steps. -/
theorem incrFields_exec (cf : Fin nf → Fin T) (hcf : Function.Injective cf) (tmp cy : Fin T)
    (htmp : ∀ f, cf f ≠ tmp) (len : Fin nf → ℕ) (i : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (ht : S.R tmp = []) (hc : ∀ f, S.R (cf f) = binSyms (len f) (digit len f i)) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body (incrFields cf tmp cy) (mk v S) (4 * (∑ f, len f) + 4 * nf + 2)
        (mk v' { S with R := R' }) ∧
      (∀ f, R' (cf f) = binSyms (len f) (digit len f (i + 1))) ∧
      ∀ k, (∀ f, k ≠ cf f) → R' k = S.R k := by
  obtain ⟨v', R', hu, he, hfs, hoth⟩ := incrList_exec body cf hcf tmp cy htmp len (fieldOff len) i
    (List.finRange nf) (List.nodup_finRange nf)
    (by
      intro j h
      simp only [List.getElem_finRange]
      exact fieldOff_succ len j (by simpa using h))
    { v with scan := Function.update v.scan cy (bitSymbol true) } S ht
    (by
      intro f hf
      have hf' : (List.finRange nf)[0]? = some f := by simpa [List.head?_eq_getElem?] using hf
      obtain ⟨h0, rfl⟩ := List.getElem?_eq_some_iff.1 hf'
      rw [fieldOff_zero len _ (by simp)]
      simp [Nat.add_comm])
    (fun f _ => by rw [hc f, digit, binSyms_mod])
  refine ⟨v', R', hu, Exec.cast (Exec.seq (Exec.act (body := body) (setCarry cy) (mk v S)) he)
    ?_ rfl, fun f => by rw [hfs f (List.mem_finRange f), digit, binSyms_mod],
    fun k hk => hoth k (fun f _ => hk f)⟩
  rw [← Fin.sum_univ_def, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp; ring

/-! ### Code automata -/

/-- A code automaton: a state symbol stepped on one bit of each of `nr` values per step, and a
final output in `Fin nd`. -/
structure CAuto (A nr nd : ℕ) where
  init : Fin (A + 4)
  step : Fin (A + 4) → (Fin nr → Bool) → Fin (A + 4)
  out : Fin (A + 4) → Fin nd

namespace CAuto

variable (C : CAuto A nr nd)

/-- The state after reading bits `0, …, L - 1` of every value, from state `s`. -/
def run : ℕ → Fin (A + 4) → (Fin nr → ℕ) → Fin (A + 4)
  | 0, s, _ => s
  | L + 1, s, vals => run L (C.step s fun r => (vals r).testBit 0) fun r => vals r / 2

/-- The code of the values `vals`: the output after reading bits `0, …, L - 1` of each. -/
def eval (L : ℕ) (vals : Fin nr → ℕ) : Fin nd := C.out (C.run L C.init vals)

lemma run_eq_foldl (L : ℕ) (s : Fin (A + 4)) (vals : Fin nr → ℕ) :
    C.run L s vals = (List.range L).foldl (fun s t => C.step s fun r => (vals r).testBit t) s := by
  induction L generalizing s vals with
  | zero => rfl
  | succ L ih =>
      rw [run, ih, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      simp only [Nat.testBit_div_two]

/-- The word automaton of a code pass: it copies each input column to the outputs and steps
the state on the bits of the column. -/
def toAuto : Auto A nr nr := ⟨C.init, fun s col => (C.step s fun r => symBit (col r), col)⟩

end CAuto

/-- The word automaton that copies each input column and keeps its state. -/
def copyAuto (n : ℕ) : Auto A n n := ⟨blank, fun s col => (s, col)⟩

/-- The state of `M` after `m` steps from `s` on the columns of the lists `ws`. -/
def Auto.stateAfter {ni no : ℕ} (M : Auto A ni no) :
    ℕ → Fin (A + 4) → (Fin ni → List (Fin (A + 4))) → Fin (A + 4)
  | 0, s, _ => s
  | m + 1, s, ws => stateAfter M m (M.step s fun i => (ws i).head?.getD blank).1 fun i => (ws i).tail

lemma CAuto.stateAfter_toAuto (C : CAuto A nr nd) (L : ℕ) (s : Fin (A + 4)) (vals : Fin nr → ℕ) :
    C.toAuto.stateAfter L s (fun r => binSyms L (vals r)) = C.run L s vals := by
  induction L generalizing s vals with
  | zero => rfl
  | succ L ih =>
      simp only [Auto.stateAfter, binSyms_succ, List.head?_cons, Option.getD_some, List.tail_cons,
        CAuto.toAuto, symBit_bitSymbol, CAuto.run]
      exact ih _ _

lemma stateAfter_copyAuto (n m : ℕ) (s : Fin (A + 4)) (ws : Fin n → List (Fin (A + 4))) :
    (copyAuto n).stateAfter m s ws = s := by
  induction m generalizing ws with
  | zero => rfl
  | succ m ih => exact ih _

/-! ### The column loop -/

/-- Run `autoStep` while register `ins 0` is nonempty. -/
def colLoop [NeZero nr] (ins outs : Fin nr → Fin T) (st : Fin T) (M : Auto A nr nr) :
    Pr P T Q A U :=
  .loop (·.flag) (.seq (.act (autoStep ins outs st M)) (.act (peekR (ins 0))))

/-- The column loop of a copying automaton over `m` columns: each input register moves onto its
output register, reversed, and slot `st` follows the automaton state. -/
theorem colLoop_exec [NeZero nr] {ins outs : Fin nr → Fin T} {st : Fin T}
    (hins : Function.Injective ins) (houts : Function.Injective outs)
    (hio : ∀ i j, ins i ≠ outs j) (hst : ∀ i, ins i ≠ st) (M : Auto A nr nr)
    (hM : ∀ s col, (M.step s col).2 = col) :
    ∀ (m : ℕ) (ws : Fin nr → List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      (∀ i, (ws i).length = m) → (∀ i, S.R (ins i) = ws i) → v.flag = (ws 0).head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        v'.scan st = M.stateAfter m (v.scan st) ws ∧
        Exec body (colLoop ins outs st M) (mk v S) (3 * m + 1) (mk v' { S with R := R' }) ∧
        (∀ i, R' (ins i) = []) ∧ (∀ i, R' (outs i) = (ws i).reverse ++ S.R (outs i)) ∧
        ∀ k, k ∉ Set.range ins → k ∉ Set.range outs → R' k = S.R k := by
  intro m
  induction m with
  | zero =>
      intro ws v S hlen hS hf
      have hnil : ∀ i, ws i = [] := fun i => List.eq_nil_of_length_eq_zero (hlen i)
      refine ⟨v, S.R, rfl, rfl, Exec.cast (.loop_false (by simp [hf, hnil])) (by simp) rfl,
        fun i => by rw [hS, hnil], fun i => by simp [hnil], fun _ _ _ => rfl⟩
  | succ m ih =>
      intro ws v S hlen hS hf
      obtain ⟨v₁, S₁, hrun₁, hu₁, _, hs₁, hi₁, ho₁, hl₁, hin₁, hout₁, hoth₁⟩ :=
        autoStep_run hins houts hio hst M v S
      have htop : topCol ins S = fun i => (ws i).head?.getD blank := by
        funext i; simp [topCol, hS]
      obtain ⟨v', R', hu, hs', he, hin', hout', hoth'⟩ := ih (fun i => (ws i).tail)
        { v₁ with flag := (S₁.R (ins 0)).head?.isSome } S₁
        (fun i => by simp [hlen]) (fun i => by rw [hin₁, hS]) (by rw [hin₁, hS])
      have hS₁ : ({ S₁ with R := R' } : Stacks T A) = { S with R := R' } := by
        cases S₁; cases S; simp_all
      have hne : ∀ i, ws i ≠ [] := fun i h => by simpa [h] using hlen i
      have hft : v.flag = true := by
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (hne 0)
        rw [hf, hx]; rfl
      refine ⟨v', R', by rw [hu, hu₁], ?_, ?_, hin', ?_, ?_⟩
      · rw [hs', Auto.stateAfter, ← htop, ← hs₁]
      · rw [← hS₁]
        exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hft
          (Exec.seq (hrun₁ ▸ Exec.act (body := body) (autoStep ins outs st M) (mk v S))
            (Exec.act (body := body) (peekR (ins 0)) (mk v₁ S₁))) he) (by ring) rfl
      · intro i
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (hne i)
        rw [hout', hout₁, hM, htop]
        simp [hx]
      · intro k hk1 hk2
        rw [hoth' k hk1 hk2, hoth₁ k hk1 hk2]

/-! ### The code pass -/

/-- Register layout of a code pass: injective families `rs` (read) and `tmps` (spare), disjoint
from each other, and a code slot `st` outside both. -/
structure CodeLayout (rs tmps : Fin nr → Fin T) (st : Fin T) : Prop where
  rs_inj : Function.Injective rs
  tmps_inj : Function.Injective tmps
  rs_tmps : ∀ r r', rs r ≠ tmps r'
  rs_st : ∀ r, rs r ≠ st
  tmps_st : ∀ r, tmps r ≠ st

/-- Start a code pass: put the initial state in slot `st` and test register `rs 0`. -/
def codeInit [NeZero nr] (rs : Fin nr → Fin T) (st : Fin T) (C : CAuto A nr nd) : Act T Q A U :=
  .load (fun v => { v with scan := Function.update v.scan st C.init }) (peekR (rs 0))

/-- A code pass: read the registers `rs` in parallel, one bit of each per step, stepping the
state of `C` in slot `st` and moving the bits onto `tmps`; then move them back. -/
def codePass [NeZero nr] (rs tmps : Fin nr → Fin T) (st : Fin T) (C : CAuto A nr nd) :
    Pr P T Q A U :=
  .seq (.act (codeInit rs st C))
    (.seq (colLoop rs tmps st C.toAuto)
      (.seq (.act (peekR (tmps 0))) (colLoop tmps rs st (copyAuto nr))))

/-- A code pass on registers `rs r` holding `binSyms L (vals r)` and empty `tmps`: slot `st`
ends holding `C.run L C.init vals` (so `C.out` of it is `C.eval L vals`) and every register is
restored. Exactly `6 * L + 4` steps. -/
theorem codePass_exec [NeZero nr] {rs tmps : Fin nr → Fin T} {st : Fin T}
    (h : CodeLayout rs tmps st) (C : CAuto A nr nd) (L : ℕ) (vals : Fin nr → ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hrs : ∀ r, S.R (rs r) = binSyms L (vals r))
    (htmps : ∀ r, S.R (tmps r) = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan st = C.run L C.init vals ∧
      Exec body (codePass rs tmps st C) (mk v S) (6 * L + 4) (mk v' S) := by
  obtain ⟨v₁, R₁, hu₁, hs₁, he₁, hrs₁, htm₁, hoth₁⟩ := colLoop_exec body h.rs_inj h.tmps_inj
    h.rs_tmps h.rs_st C.toAuto (fun _ _ => rfl) L (fun r => binSyms L (vals r))
    { v with
      scan := Function.update v.scan st C.init
      flag := (S.R (rs 0)).head?.isSome } S (fun r => by simp) hrs (by rw [hrs])
  obtain ⟨v₂, R₂, hu₂, hs₂, he₂, htm₂, hrs₂, hoth₂⟩ := colLoop_exec body h.tmps_inj h.rs_inj
    (fun i j => (h.rs_tmps j i).symm) h.tmps_st (copyAuto nr) (fun _ _ => rfl) L
    (fun r => (binSyms L (vals r)).reverse) { v₁ with flag := (R₁ (tmps 0)).head?.isSome }
    { S with R := R₁ } (fun r => by simp) (fun r => by simp [htm₁, htmps]) (by simp [htm₁, htmps])
  have hR₂ : ({ S with R := R₂ } : Stacks T A) = S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    show R₂ k = S.R k
    by_cases hk : k ∈ Set.range rs
    · obtain ⟨r, rfl⟩ := hk
      rw [hrs₂]
      simp [hrs₁, hrs]
    by_cases hk' : k ∈ Set.range tmps
    · obtain ⟨r, rfl⟩ := hk'
      rw [htm₂]
      exact (htmps r).symm
    rw [hoth₂ k hk' hk]
    exact hoth₁ k hk hk'
  refine ⟨v₂, by simp [hu₂, hu₁], ?_, ?_⟩
  · rw [hs₂, stateAfter_copyAuto]
    simp only
    rw [hs₁]
    simpa using C.stateAfter_toAuto L C.init vals
  · exact Exec.cast (Exec.seq (Exec.act (body := body) (codeInit rs st C) (mk v S))
      (Exec.seq he₁ (Exec.seq (Exec.act (body := body) (peekR (tmps 0)) (mk v₁ { S with R := R₁ }))
        he₂))) (by ring) (by rw [← hR₂])

end IntegerMultBounds.MathlibTM2.Host
