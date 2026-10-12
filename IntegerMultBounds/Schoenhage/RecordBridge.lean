module

public import IntegerMultBounds.Schoenhage.WordBridge
public import IntegerMultBounds.Schoenhage.RecordWords
public import IntegerMultBounds.Machine.RecordPack
public import IntegerMultBounds.Machine.RecordRewind
public import IntegerMultBounds.Spec.SignedRingProduct
public import IntegerMultBounds.Schoenhage.FixedMulPlaced

/-! The two bridges between the paper's arrays and the resampling machines'
records, as literal four-tape programs. Tape `0` holds the paper's array, a
raw bit string from cell zero; tape `1` the component width `w` in unary;
tape `2` the records, blank-separated with each component least significant
bit first. `paperToRecords` cuts the array into width-`w` components and
reverses each (`paperToRecords_hoare`); `recordsToPaper` packs the records,
reverses each component and joins them into an array, consuming the records
(`recordsToPaper_hoare`). Both end with every head at cell zero. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct
open OrderedSelect (inTape flat)

/-- Four tapes at cell zero. -/
def bank4 (f0 f1 f2 f3 : ℤ → Fin 4) : Tapes 4 0 := ⟨fun _ => 0, ![f0, f1, f2, f3]⟩

/-- `M` on tape `i` of the four. -/
noncomputable def on4 (i : Fin 4) {q : ℕ} (M : Program 1 q 0) : Program 4 q 0 :=
  Placement.placed M (InjectivePlacement.placement (fun _ : Fin 1 => i) (slot_const_inj i) (one_size i))

theorem wordAt_nil0 : wordAt (a := 0) [] = fun _ => blank := by funext j; simp [wordAt, wordTape]

theorem emp_tape0 : (emp : WTape).tape (a := 0) = fun _ => blank := by
  funext j; simp [WTape.tape, wordTape, WTape.words, emp, cells, syms]

/-! ### Paper array to records -/

/-- The compiled word program. -/
noncomputable def toWordsProg : Program 4 (compile (a := 0) (by decide) toWords).1 0 :=
  (compile (a := 0) (by decide) toWords).2

/-- Seal, cut and reverse, unseal, turn separators into blanks. -/
noncomputable def paperToRecords :=
  Machine.seq (sealAt (a := 0) (0 : Fin 4)) <| Machine.seq (sealAt (a := 0) (1 : Fin 4)) <|
  Machine.seq toWordsProg <| Machine.seq (unsealAt (a := 0) (0 : Fin 4)) <|
  Machine.seq (unsealAt (a := 0) (1 : Fin 4)) (on4 2 desepProg)

/-- The words of an array, least significant bit first. -/
def lsbWords (w : ℕ) (A : List Bool) : List (List Bool) := (cut w A).map List.reverse

set_option maxHeartbeats 4000000 in
theorem paperToRecords_hoare {w : ℕ} (hw : 1 ≤ w) (A : List Bool) :
    HoareTime paperToRecords (· = bank4 (wordAt A) (wordAt (ones w)) (fun _ => blank) (fun _ => blank))
      (· = bank4 (wordAt A) (wordAt (ones w)) (inTape (recsOf (lsbWords w A))) (fun _ => blank))
      (40 * A.length + 20 * (cut w A).length * (A.length + 1) + 2 * (cut w A).length + 4 * w + 120) := by
  set v0 := bank4 (wordAt A) (wordAt (ones w)) (fun _ => blank) (fun _ => blank)
  have h1 := sealAt_hoare (a := 0) (0 : Fin 4) A v0 rfl (by simp [v0, bank4])
  set v1 : Tapes 4 0 := ⟨v0.head, Function.update v0.tape 0 (⟨[], [A]⟩ : WTape).tape⟩
  have h2 := sealAt_hoare (a := 0) (1 : Fin 4) (ones w) v1 rfl (by simp [v1, v0, bank4])
  set σ0 : Fin 4 → WTape := ![reg A, reg (ones w), emp, emp]
  have e2 : (⟨v1.head, Function.update v1.tape 1 (⟨[], [ones w]⟩ : WTape).tape⟩ : Tapes 4 0) = enc σ0 := by
    simp only [enc]
    congr 1 <;> funext i <;> fin_cases i <;> simp [v1, v0, bank4, σ0, reg, WTape.pos, emp_tape0]
  rw [e2] at h2
  obtain ⟨σ', k, hx, hq, hk⟩ := runs_toWords (a := 0) hw A σ0 rfl rfl rfl rfl
  subst hq
  have h3 := (compile_correct (by decide) hx).consequence (fun v e => e) (fun v e => e) hk
  set σ1 := Function.update σ0 2 ⟨[], lsbWords w A⟩
  have h4 := unsealAt_hoare (a := 0) (0 : Fin 4) A (enc σ1) (by simp [enc, σ1, σ0, reg, WTape.pos])
    (by simp [enc, σ1, σ0, reg])
  set v4 : Tapes 4 0 := ⟨(enc σ1).head, Function.update (enc σ1).tape 0 (wordAt A)⟩
  have h5 := unsealAt_hoare (a := 0) (1 : Fin 4) (ones w) v4 (by simp [v4, enc, σ1, σ0, reg, WTape.pos])
    (by simp [v4, enc, σ1, σ0, reg])
  set v5 : Tapes 4 0 := ⟨v4.head, Function.update v4.tape 1 (wordAt (ones w))⟩
  have h6 := place_one (a := 0) (2 : Fin 4) (desepProg_hoare (lsbWords w A)) v5
    (by simp [v5, v4, enc, σ1, WTape.pos]) (by simp [v5, v4, enc, σ1])
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).consequence (fun v e => e) (fun v e => e.trans ?_) ?_
  · simp only [v5, v4, bank4, enc, σ1, σ0]
    congr 1
    · funext i; fin_cases i <;> simp [reg, WTape.pos]
    · funext i; fin_cases i <;> simp [reg, emp_tape0]
  · have hc : clen (lsbWords w A) = A.length + (cut w A).length := by
      rw [lsbWords, clen_map_reverse, clen_eq, cut_flatten]
    rw [hc]; simp only [length_ones]
    omega

/-! ### Records to paper array -/

/-- Cut the packed bits on tape `3` into words on tape `2`, then reverse and join them onto tape `0`. -/
noncomputable def packWords : Cmd 0 4 :=
  .seq (chunkw 3 1 2 (by decide) (by decide) (by decide)) <| .seq (rewind 2) <| .seq (clear 3) fromWords

theorem runs_packWords {w : ℕ} (hw : 1 ≤ w) (ws : List (List Bool)) (hws : ∀ x ∈ ws, x.length = w)
    (σ : Fin 4 → WTape) (h0 : σ 0 = emp) (h1 : σ 1 = reg (ones w)) (h2 : σ 2 = emp)
    (h3 : σ 3 = reg ws.flatten) :
    Runs packWords σ (· = Function.update (Function.update σ 0 (reg (ws.map List.reverse).flatten)) 3 emp)
      (ws.length * (8 * w + 40) + 20 * clen ws + 50) := by
  have hcut : cut w ws.flatten = ws := cut_flatten_words hw ws hws
  have s1 := runs_chunkw (a := 0) (s := 3) (r := 1) (d := 2) (by decide) (by decide) (by decide) σ
    (L := []) (R := []) (x := ws.flatten) (by rw [h3]; rfl) h1 hw (by rw [h2]; rfl)
  rw [hcut] at s1
  set σ₁ := Function.update (Function.update σ 3 ⟨[ws.flatten], []⟩) 2 ⟨ws.reverse ++ (σ 2).left, []⟩
  have s2 := runs_rewind (a := 0) 2 σ₁
  set σ₂ := Function.update σ₁ 2 ⟨[], (σ₁ 2).left.reverse ++ (σ₁ 2).right⟩
  have s3 := runs_clear (a := 0) 3 σ₂
  set σ₃ := Function.update σ₂ 3 ⟨[], []⟩
  have s4 := runs_fromWords (a := 0) (W := w) ws (fun x hx => (hws x hx).le) σ₃
    (by simp [σ₃, σ₂, σ₁, h0]) (by simp [σ₃, σ₂, σ₁, h2, emp]) (by simp [σ₃, emp])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun σ' e => ?_) ?_
  · rw [e]; funext y
    fin_cases y <;> simp [σ₃, σ₂, σ₁, h2, emp]
  · have hf : ws.flatten.length + ws.length = clen ws := by rw [clen_eq]
    simp only [σ₂, σ₁, Function.update_self, Function.update_of_ne (show (3 : Fin 4) ≠ 2 by decide),
      h2, emp, WTape.words, List.append_nil, clen_reverse, clen_cons, clen_nil]
    nlinarith

/-- The compiled word program. -/
noncomputable def packWordsProg : Program 4 (compile (a := 0) (by decide) packWords).1 0 :=
  (compile (a := 0) (by decide) packWords).2

/-- Pack, erase the records, return, seal, cut-reverse-join, unseal. -/
noncomputable def recordsToPaper :=
  Machine.seq (at2 (2 : Fin 4) 3 (by decide) (RecordPack.program (a := 0))) <|
  Machine.seq (at1 (2 : Fin 4) (RecordRewind.program (a := 0) true)) <|
  Machine.seq (at1 (3 : Fin 4) (ReturnOrigin.program (a := 0))) <|
  Machine.seq (sealAt (a := 0) (1 : Fin 4)) <| Machine.seq (sealAt (a := 0) (3 : Fin 4)) <|
  Machine.seq packWordsProg <| Machine.seq (unsealAt (a := 0) (0 : Fin 4)) (unsealAt (a := 0) (1 : Fin 4))

/-- The paper's array of least-significant-first words. -/
def msbArray (ws : List (List Bool)) : List Bool := (ws.map List.reverse).flatten

theorem flatten_recsOf (ws : List (List Bool)) : (recsOf (a := 0) ws).flatten = ws.flatten.map bitSymbol := by
  simp [recsOf, List.map_flatten]

set_option maxHeartbeats 8000000 in
theorem recordsToPaper_hoare {w : ℕ} (hw : 1 ≤ w) (ws : List (List Bool)) (hws : ∀ x ∈ ws, x.length = w) :
    HoareTime recordsToPaper (· = bank4 (fun _ => blank) (wordAt (ones w)) (inTape (recsOf ws)) (fun _ => blank))
      (· = bank4 (wordAt (msbArray ws)) (wordAt (ones w)) (fun _ => blank) (fun _ => blank))
      (ws.length * (8 * w + 40) + 40 * clen ws + 4 * w + 150) := by
  have hne : ∀ z ∈ recsOf (a := 0) ws, z ≠ [] ∧ ∀ c ∈ z, c ≠ blank := by
    intro z hz
    simp only [recsOf, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨by have := hws x hx; intro e; simp at e; subst e; simp at this; omega, fun c hc => ?_⟩
    simp only [List.mem_map] at hc; obtain ⟨b, -, rfl⟩ := hc; exact bitSymbol_ne_blank b
  set R := recsOf (a := 0) ws
  set v0 := bank4 (fun _ => blank) (wordAt (ones w)) (inTape R) (fun _ => blank)
  have h1 := at2_hoare (i := (2 : Fin 4)) (j := 3) (by decide) (p := 0) (r := 0) (f := inTape R)
    (g := fun _ => blank) (p' := 0 + (OrderedSelect.flat R).length) (r' := 0 + R.flatten.length) (f' := inTape R) (g' := putWord (fun _ => blank) 0 R.flatten)
    (RecordPack.pack_hoare (inTape R) (fun _ => blank) 0 0 R hne
      (fun k hk => by simp [inTape, putWord_zero, wordTape, hk, List.getD_eq_getElem?_getD])
      (by simp [inTape, putWord_zero, wordTape])) v0 (by simp [v0, bank4]) (by simp [v0, bank4])
      (by simp [v0, bank4]) (by simp [v0, bank4])
  set v1 : Tapes 4 0 := ⟨Function.update (Function.update v0.head 2 (0 + (OrderedSelect.flat R).length)) 3
      (0 + R.flatten.length), Function.update (Function.update v0.tape 2 (inTape R)) 3
      (putWord (fun _ => blank) 0 R.flatten)⟩
  have h2 := at1_hoare (2 : Fin 4) (h := (OrderedSelect.flat R).length) (h' := 0) (f := inTape R)
    (g := fun _ => blank) (RecordRewind.erase_records R hne) v1 (by simp [v1]) (by simp [v1])
  set v2 : Tapes 4 0 := ⟨Function.update v1.head 2 0, Function.update v1.tape 2 (fun _ => blank)⟩
  have hRn : ∀ x ∈ R.flatten, x ≠ blank := fun x hx => by
    rw [flatten_recsOf] at hx; simp only [List.mem_map] at hx; obtain ⟨b, -, rfl⟩ := hx; exact bitSymbol_ne_blank b
  have h3 := at1_hoare (3 : Fin 4) (h := 0 + R.flatten.length) (h' := 0) (f := putWord (fun _ => blank) 0 R.flatten)
    (g := putWord (fun _ => blank) 0 R.flatten)
    (ReturnOrigin.return_hoare_at (fun _ => blank) 0 R.flatten hRn rfl) v2 (by simp [v2, v1]) (by simp [v2, v1])
  set v3 : Tapes 4 0 := ⟨Function.update v2.head 3 0, Function.update v2.tape 3 (putWord (fun _ => blank) 0 R.flatten)⟩
  have e3 : v3 = bank4 (fun _ => blank) (wordAt (ones w)) (fun _ => blank) (wordAt ws.flatten) := by
    simp only [v3, v2, v1, v0, bank4]
    congr 1 <;> funext i <;> fin_cases i <;> first | (simp [putWord_zero, wordAt]; done) | (simp [putWord_zero, wordAt]; rfl)
  rw [e3] at h3
  set u0 := bank4 (fun _ => blank) (wordAt (ones w)) (fun _ => blank) (wordAt ws.flatten)
  have h4 := sealAt_hoare (a := 0) (1 : Fin 4) (ones w) u0 rfl (by simp [u0, bank4])
  set u1 : Tapes 4 0 := ⟨u0.head, Function.update u0.tape 1 (⟨[], [ones w]⟩ : WTape).tape⟩
  have h5 := sealAt_hoare (a := 0) (3 : Fin 4) ws.flatten u1 rfl (by simp [u1, u0, bank4])
  set σ0 : Fin 4 → WTape := ![emp, reg (ones w), emp, reg ws.flatten]
  have e5 : (⟨u1.head, Function.update u1.tape 3 (⟨[], [ws.flatten]⟩ : WTape).tape⟩ : Tapes 4 0) = enc σ0 := by
    simp only [enc]
    congr 1 <;> funext i <;> fin_cases i <;> simp [u1, u0, bank4, σ0, reg, WTape.pos, emp_tape0]
  rw [e5] at h5
  obtain ⟨σ', k, hx, hq, hk⟩ := runs_packWords hw ws hws σ0 rfl rfl rfl rfl
  subst hq
  have h6 := (compile_correct (by decide) hx).consequence (fun v e => e) (fun v e => e) hk
  set σ1 := Function.update (Function.update σ0 0 (reg (msbArray ws))) 3 emp
  have h7 := unsealAt_hoare (a := 0) (0 : Fin 4) (msbArray ws) (enc σ1) (by simp [enc, σ1, σ0, reg, WTape.pos])
    (by simp [enc, σ1, σ0, reg])
  set u7 : Tapes 4 0 := ⟨(enc σ1).head, Function.update (enc σ1).tape 0 (wordAt (msbArray ws))⟩
  have h8 := unsealAt_hoare (a := 0) (1 : Fin 4) (ones w) u7 (by simp [u7, enc, σ1, σ0, reg, WTape.pos])
    (by simp [u7, enc, σ1, σ0, reg])
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))).consequence (fun v e => e)
    (fun v e => e.trans ?_) ?_
  · simp only [u7, bank4, enc, σ1, σ0]
    congr 1
    · funext i; fin_cases i <;> simp [reg, emp, WTape.pos]
    · funext i; fin_cases i <;> simp [reg, emp_tape0]
  · have hfl : (OrderedSelect.flat R).length = clen ws := by
      rw [← flat_recsOf, List.length_map, length_cellsOf]
    have hRl : R.flatten.length + ws.length = clen ws := by
      rw [flatten_recsOf, List.length_map, clen_eq]
    have hm : (msbArray ws).length + ws.length = clen ws := by
      rw [msbArray, ← clen_map_reverse, clen_eq, List.length_map]
    have hfw : ws.flatten.length + ws.length = clen ws := by rw [clen_eq]
    simp only [length_ones, hfl]
    omega

end IntegerMultBounds.Schoenhage
