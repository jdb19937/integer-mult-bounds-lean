import IntegerMultBounds.Schoenhage.RingPointwise

/-! The pointwise-product step as a literal program in the paper's formats:
seal the raw header and operand strings into word tapes, run the compiled
word program, unseal the four data tapes, and relabel the bank so that the
header, the two operands and the output are tapes 0–3
(`pointwise_meets`: `MeetsPointwise`). -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-- The compiled word program. -/
noncomputable def pwCoreProg : Program 𝕌 (compile (a := 0) (by decide) pwCore).1 0 :=
  (compile (a := 0) (by decide) pwCore).2

/-- Seal, run `core`, unseal. -/
noncomputable def pwProg91With {q : ℕ} (core : Program 𝕌 q 0) :=
  Machine.seq (sealAt (a := 0) zH) <| Machine.seq (sealAt (a := 0) zF) <| Machine.seq (sealAt (a := 0) zG) <|
  Machine.seq core <| Machine.seq (unsealAt (a := 0) zO) <| Machine.seq (unsealAt (a := 0) zH) <|
  Machine.seq (unsealAt (a := 0) zF) (unsealAt (a := 0) zG)

/-- Seal, run, unseal. -/
noncomputable def pwProg91 := pwProg91With pwCoreProg

/-- The raw bank: header and operands on `zH`, `zF`, `zG`, the output on `zO`, all else blank. -/
def raw91 (hdr F G out : List Bool) : Tapes 𝕌 0 :=
  ⟨fun _ => 0, fun i => if i = zH then wordAt hdr else if i = zF then wordAt F else if i = zG then wordAt G
    else if i = zO then wordAt out else fun _ => blank⟩

theorem emp_tape : (emp : WTape).tape (a := 0) = fun _ => blank := by
  funext j; simp [WTape.tape, wordTape, WTape.words, emp, cells, syms]

theorem wordAt_nil : wordAt (a := 0) [] = fun _ => blank := by
  funext j; simp [wordAt, wordTape]

theorem enc_startBank (hdr F G : List Bool) :
    enc (a := 0) (startBank hdr F G) = ⟨fun _ => 0, fun i => if i = zH then (⟨[], [hdr]⟩ : WTape).tape
      else if i = zF then (⟨[], [F]⟩ : WTape).tape else if i = zG then (⟨[], [G]⟩ : WTape).tape
      else fun _ => blank⟩ := by
  simp only [enc]
  congr 1
  · funext i; simp only [startBank, Function.update_apply]; split_ifs <;> rfl
  · funext i; simp only [startBank, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | exact emp_tape | (tsimp at *)

theorem enc_startBank_out (hdr F G out : List Bool) :
    enc (a := 0) (Function.update (startBank hdr F G) zO (reg out)) = ⟨fun _ => 0, fun i =>
      if i = zH then (⟨[], [hdr]⟩ : WTape).tape else if i = zF then (⟨[], [F]⟩ : WTape).tape
      else if i = zG then (⟨[], [G]⟩ : WTape).tape else if i = zO then (⟨[], [out]⟩ : WTape).tape
      else fun _ => blank⟩ := by
  simp only [enc]
  congr 1
  · funext i; simp only [startBank, Function.update_apply]; split_ifs <;> rfl
  · funext i; simp only [startBank, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | exact emp_tape | (tsimp at *)

/-- The core's contract on the encoded banks. -/
theorem pwCoreProg_hoare {p d l K w : ℕ} {ts : List ℕ} {fs gs : List (Rec (2 ^ l))}
    (hp : 2 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : p + 2 ≤ w) (hlen : fs.length = gs.length)
    (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) :
    HoareTime pwCoreProg (· = enc (startBank (transformHeader p d (2 ^ l) K w ts) (array w fs) (array w gs)))
      (· = enc (Function.update (startBank (transformHeader p d (2 ^ l) K w ts) (array w fs) (array w gs))
        zO (reg (array w (List.zipWith (prodRec p) fs gs)))))
      (pwCost p d l K w (transformHeader p d (2 ^ l) K w ts).length fs.length (array w fs).length) := by
  obtain ⟨σ', k, hx, hq, hk⟩ := runs_pwCore (ts := ts) hp hd hK hw hlen hf hg
  subst hq
  exact (compile_correct (by decide) hx).consequence (fun _ h => h) (fun _ h => h) hk

set_option maxHeartbeats 4000000 in
theorem pwProg91With_hoare {q : ℕ} {core : Program 𝕌 q 0} {hdr F G out : List Bool} {c : ℕ}
    (h4 : HoareTime core (· = enc (startBank hdr F G)) (· = enc (Function.update (startBank hdr F G) zO (reg out))) c) :
    HoareTime (pwProg91With core) (· = raw91 hdr F G []) (· = raw91 hdr F G out)
      (c + 4 * (hdr.length + F.length + G.length + out.length) + 60) := by
  set v0 := raw91 hdr F G []
  have h1 := sealAt_hoare (a := 0) zH hdr v0 rfl (by simp [v0, raw91])
  set v1 : Tapes 𝕌 0 := ⟨v0.head, Function.update v0.tape zH (⟨[], [hdr]⟩ : WTape).tape⟩
  have h2 := sealAt_hoare (a := 0) zF F v1 rfl (by tsimp [v1, v0, raw91])
  set v2 : Tapes 𝕌 0 := ⟨v1.head, Function.update v1.tape zF (⟨[], [F]⟩ : WTape).tape⟩
  have h3 := sealAt_hoare (a := 0) zG G v2 rfl (by tsimp [v2, v1, v0, raw91])
  have e3 : (⟨v2.head, Function.update v2.tape zG (⟨[], [G]⟩ : WTape).tape⟩ : Tapes 𝕌 0) =
      enc (startBank hdr F G) := by
    rw [enc_startBank]
    simp only [v2, v1, v0, raw91, Tapes.mk.injEq, true_and]
    funext i; simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | exact wordAt_nil | (tsimp at *)
  set v4 := enc (a := 0) (Function.update (startBank hdr F G) zO (reg out))
  have hv4 : v4 = _ := enc_startBank_out hdr F G out
  have h5 := unsealAt_hoare (a := 0) zO out v4 (by rw [hv4]) (by rw [hv4]; tsimp)
  set v5 : Tapes 𝕌 0 := ⟨v4.head, Function.update v4.tape zO (wordAt out)⟩
  have h6 := unsealAt_hoare (a := 0) zH hdr v5 (by simp only [v5]; rw [hv4])
    (by simp only [v5]; rw [hv4]; tsimp)
  set v6 : Tapes 𝕌 0 := ⟨v5.head, Function.update v5.tape zH (wordAt hdr)⟩
  have h7 := unsealAt_hoare (a := 0) zF F v6 (by simp only [v6, v5]; rw [hv4])
    (by simp only [v6, v5]; rw [hv4]; tsimp)
  set v7 : Tapes 𝕌 0 := ⟨v6.head, Function.update v6.tape zF (wordAt F)⟩
  have h8 := unsealAt_hoare (a := 0) zG G v7 (by simp only [v7, v6, v5]; rw [hv4])
    (by simp only [v7, v6, v5]; rw [hv4]; tsimp)
  have e8 : (⟨v7.head, Function.update v7.tape zG (wordAt G)⟩ : Tapes 𝕌 0) = raw91 hdr F G out := by
    simp only [v7, v6, v5, raw91, Tapes.mk.injEq]
    rw [hv4]
    refine ⟨rfl, ?_⟩
    funext i; simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | (tsimp at *)
  refine ((h1.seq (h2.seq (h3.seq ((h4.consequence (fun v h => h.trans e3) (fun v h => h) le_rfl).seq
    (h5.seq (h6.seq (h7.seq h8)))))))).consequence (fun v h => h) (fun v h => h.trans e8) ?_
  omega

theorem pwProg91_hoare {p d l K w : ℕ} {ts : List ℕ} {fs gs : List (Rec (2 ^ l))}
    (hp : 2 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : p + 2 ≤ w) (hlen : fs.length = gs.length)
    (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) :
    HoareTime pwProg91 (· = raw91 (transformHeader p d (2 ^ l) K w ts) (array w fs) (array w gs) [])
      (· = raw91 (transformHeader p d (2 ^ l) K w ts) (array w fs) (array w gs)
        (array w (List.zipWith (prodRec p) fs gs)))
      (pwCost p d l K w (transformHeader p d (2 ^ l) K w ts).length fs.length (array w fs).length +
        4 * ((transformHeader p d (2 ^ l) K w ts).length + (array w fs).length + (array w gs).length +
          (array w (List.zipWith (prodRec p) fs gs)).length) + 60) :=
  pwProg91With_hoare (pwCoreProg_hoare (ts := ts) hp hd hK hw hlen hf hg)

/-! ### Tapes 0–3 -/

/-- Exchange the data tapes `zH, zF, zG, zO` with tapes 0–3. -/
def dataSwap : Fin 𝕌 ≃ Fin 𝕌 :=
  (Equiv.swap 0 87).trans ((Equiv.swap 1 88).trans ((Equiv.swap 2 89).trans (Equiv.swap 3 90)))

set_option maxHeartbeats 8000000 in
theorem raw91_reindex (hdr F G out : List Bool) :
    (raw91 hdr F G out).reindex dataSwap = bank (t := 𝕌) (a := 0) hdr F G out := by
  simp only [Tapes.reindex, raw91, bank, Tapes.mk.injEq]
  refine ⟨trivial, ?_⟩
  funext i
  fin_cases i <;> tsimp [dataSwap, Equiv.swap_apply_def]

/-- The pointwise-product program on the paper's tapes. -/
noncomputable def pointwiseProgram := Machine.reindex pwProg91 dataSwap

/-- The time bound: the word-level bound maximized over the admissible widths. -/
def pointwiseTime (Cw : ℕ) (T p r H : ℕ) : ℕ :=
  (Finset.range (Cw * p + 1)).sup fun w =>
    pwCost p 0 (Nat.log 2 r) 0 w H (T / r) (2 * T * w) + 4 * (H + 3 * (2 * T * w)) + 60

set_option maxHeartbeats 4000000 in
theorem pointwise_meets (Cw : ℕ) : MeetsPointwise pointwiseProgram Cw (pointwiseTime Cw) := by
  intro p d l K w ts fs gs hl hp hpr hd hK hw hwC hax hfl hgl hf hg
  have h := (pwProg91_hoare (p := p) (d := d) (l := l) (K := K) (w := w) (ts := ts) hp (by omega) hK hw (hfl.trans hgl.symm) hf hg).reindex dataSwap
  refine h.consequence (fun v hv => ⟨_, rfl, by rw [hv, raw91_reindex]⟩)
    (fun v ⟨o, ho, hv⟩ => by rw [hv, ho, raw91_reindex]) ?_
  have hM : 2 ^ l * ts.prod / 2 ^ l = fs.length := by rw [hfl, Nat.mul_div_cancel_left _ (by positivity)]
  have hX : (array w fs).length = 2 * (2 ^ l * ts.prod) * w := by rw [length_array, hfl]; ring
  have hG : (array w gs).length = 2 * (2 ^ l * ts.prod) * w := by rw [length_array, hgl]; ring
  have hO : (array w (List.zipWith (prodRec p) fs gs)).length = 2 * (2 ^ l * ts.prod) * w := by
    rw [length_array, List.length_zipWith, hfl, hgl, min_self]; ring
  set H := (transformHeader p d (2 ^ l) K w ts).length
  set Tz := 2 ^ l * ts.prod
  let g := fun w' => pwCost p 0 (Nat.log 2 (2 ^ l)) 0 w' H (Tz / 2 ^ l) (2 * Tz * w') + 4 * (H + 3 * (2 * Tz * w')) + 60
  have hle : g w ≤ (Finset.range (Cw * p + 1)).sup g := Finset.le_sup (Finset.mem_range.mpr (by omega))
  have hgw : g w = pwCost p d l K w H fs.length (array w fs).length + 4 * (H + 3 * (2 * Tz * w)) + 60 := by
    simp only [g, Nat.log_pow (by norm_num : 1 < 2), hM, hX]; rfl
  unfold pointwiseTime
  refine le_trans ?_ hle
  rw [hgw, hX, hG, hO]
  generalize pwCost p d l K w H fs.length (2 * Tz * w) = P
  omega

end IntegerMultBounds.Schoenhage
