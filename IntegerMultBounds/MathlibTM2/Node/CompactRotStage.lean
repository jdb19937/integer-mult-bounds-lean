module

public import IntegerMultBounds.MathlibTM2.Node.CompactRotHost
public import IntegerMultBounds.Machine.ActivePrefixStageFullSelected

/-! # Full compact stages on normalized host banks

The original thirteen descriptors and raw array are the only persistent bank
contents. Reservation geometry and native density hypotheses remain explicit.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
open ActiveRepairLayoutRecordsData (Array)
noncomputable section
variable {s : Shape} {k A : ℕ}

def compactStageHeader : Fin 13 → Fin (66+k) := fun j => ⟨j.val, by omega⟩
lemma compactStageHeader_injective : Function.Injective (compactStageHeader (k := k)) := by
  intro i j h
  exact Fin.ext (show i.val = j.val from congrArg (fun z : Fin (66+k) => z.val) h)

def compactStageWords (d : Inputs s) (x : Array s d.rows) (j : Fin (66+k)) :
    List (Fin (A+4)) :=
  if h : j.val<13 then separator ::
    (RecursiveChildQuotientsConstant.bits (ActivePrefixStageHeadersData.originalValues d.stage d.rows ⟨j.val,h⟩)).map bitSymbol
  else if j.val=65 then List.ofFn (fun z => bitSymbol (x z)) else []

lemma compactStageHeader_mem (j : Fin (66+k)) :
    j ∈ Set.range compactStageHeader ↔ j.val<13 := by
  constructor
  · rintro ⟨i,rfl⟩; exact i.isLt
  · intro h; exact ⟨⟨j.val,h⟩,Fin.ext rfl⟩

lemma compactStageBank_head (d : Inputs s) (x : Array s d.rows) (j : Fin (66+k)) :
    (CleanSubbank.bank (s := k) (original d x)).head j =
      if j ∈ Set.range compactStageHeader then 1 else 0 := by
  simp only [compactStageHeader_mem]
  by_cases hj : j.val<13
  · rw [ite_eq_left hj]
    let i : Fin 13 := ⟨j.val,hj⟩
    have he : j = Fin.castAdd k (Fin.castAdd 53 i) := Fin.ext rfl
    rw [he]
    simpa only [CleanSubbank.bank,Tapes.append,Fin.addCases_left] using (ActivePrefixStageFullEndpoint.original_header d x i).1
  · rw [ite_eq_right hj]
    by_cases h65 : j.val=65
    · have he : j = Fin.castAdd k (65 : Fin 66) := Fin.ext h65
      rw [he]
      exact (ActivePrefixStageFullEndpoint.original_raw d x).1
    · exact (ActivePrefixStageFullEndpoint.bank_blank d x j (by omega) h65).1

lemma compactStageBank_tape (d : Inputs s) (x : Array s d.rows) (j : Fin (66+k)) :
    (CleanSubbank.bank (s := k) (original d x)).tape j =
      wordTape (compactStageWords (A := prime) d x j) := by
  unfold compactStageWords
  by_cases hj : j.val<13
  · rw [dite_eq_left hj]
    let i : Fin 13 := ⟨j.val,hj⟩
    have he : j = Fin.castAdd k (Fin.castAdd 53 i) := Fin.ext rfl
    have h := (ActivePrefixStageFullEndpoint.original_header d x i).2
    rw [encodedBinary_eq] at h
    change (CleanSubbank.bank (s := k) (original d x)).tape j = wordTape (separator :: (RecursiveChildQuotientsConstant.bits (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)).map bitSymbol)
    rw [he]
    simpa only [CleanSubbank.bank,Tapes.append,Fin.addCases_left] using h
  · rw [dite_eq_right hj]
    by_cases h65 : j.val=65
    · rw [ite_eq_left h65]
      have he : j = Fin.castAdd k (65 : Fin 66) := Fin.ext h65
      rw [he]
      change ActiveTargetRotation.word x = _
      exact putWord_blank_zero _
    · rw [ite_eq_right h65,wordTape_nil]
      exact (ActivePrefixStageFullEndpoint.bank_blank d x j (by omega) h65).2

lemma compactStageWords_header (d : Inputs s) (x : Array s d.rows) (i : Fin 13) :
    compactStageWords (A := A) d x (compactStageHeader (k := k) i) ≠ [] := by
  simp [compactStageWords,compactStageHeader,i.isLt]

lemma compactStageWords_free (d : Inputs s) (x : Array s d.rows) (j : Fin (66+k)) :
    blank ∉ compactStageWords (A := A) d x j := by
  have hb : ∀ b : Bool, (bitSymbol b : Fin (A+4)) ≠ blank := by
    intro b; cases b <;> simp [bitSymbol, blank, Fin.ext_iff]
  have hs : (separator : Fin (A+4)) ≠ blank := by simp [separator, blank, Fin.ext_iff]
  unfold compactStageWords
  split_ifs
  · simp only [List.mem_cons, List.mem_map, not_or, not_exists]
    exact ⟨Ne.symm hs, fun b h => hb b h.2⟩
  · simp only [List.mem_ofFn, not_exists]
    exact fun i => hb (x i)
  · simp

lemma compactStageWords_widen (K : ℕ) (d : Inputs s) (x : Array s d.rows) (j : Fin (66+k)) :
    (compactStageWords (A := prime) d x j).map (Alphabet.widen prime K).encode =
      compactStageWords (A := prime+K) d x j := by
  unfold compactStageWords
  split_ifs <;> simp [List.map_map,Function.comp_def]

lemma compactStageBank_widen_tape (K : ℕ) (d : Inputs s) (x : Array s d.rows)
    (j : Fin (66+k)) :
    (Alphabet.mapTapes (Alphabet.widen prime K) (CleanSubbank.bank (s := k) (original d x))).tape j =
      wordTape (compactStageWords (A := prime+K) d x j) := by
  funext z
  change (Alphabet.widen prime K).encode ((CleanSubbank.bank (s := k) (original d x)).tape j z) = _
  rw [compactStageBank_tape,encode_wordTape,compactStageWords_widen]


variable {T Q K : ℕ} {U F : Type}

/-- Widen and normalize a full stage bank while preserving the host frame. -/
theorem compactStageWiden_exec (body : F → Pr F T Q (prime+K) U)
    {q : ℕ} (M : Program (66+k) q prime) (hQ : q ≤ Q)
    (ι : Fin (66+k) → Fin T) (hι : Function.Injective ι) (hT : 66+k ≤ T)
    (d : Inputs s) (x y : Array s d.rows) (cost : ℕ)
    (hM : HoareTime M (fun w => w=CleanSubbank.bank (s := k) (original d x))
      (fun w => w=CleanSubbank.bank (s := k) (original d y)) cost)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j, S.L (ι j)=[])
    (hR : ∀ j, S.R (ι j)=compactStageWords d x j) :
    ∃ v' m, v'.user=v.user ∧
      m ≤ (T+12*(66+k)+5)*cost +
        6*(∑ j, (compactStageWords (A := prime+K) (k := k) d x j).length) +
        2*T+6*(66+k)+23 ∧
      Exec body (compactNativeProg (liftQ (Alphabet.program (Alphabet.widen prime K) M) hQ)
        compactStageHeader ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun z => if z ∈ Set.range ι then [] else S.L z
          R := fun z => if h : z ∈ Set.range ι then
            compactStageWords d y (Classical.choose h) else S.R z }) := by
  have hm := (Alphabet.map_hoare (Alphabet.widen prime K) hM).consequence
    (fun _ hv => ⟨_, rfl, hv⟩)
    (fun _ hv => by obtain ⟨w,rfl,hw⟩ := hv; exact hw) (Nat.le_refl cost)
  have he := compactNativeProg_exec body _ compactStageHeader compactStageHeader_injective
    ι hι hT _ _ cost (HoareTime.liftQ hQ hm)
    (compactStageWords d x) (compactStageWords d y)
    (compactStageBank_head d x) (compactStageBank_widen_tape K d x)
    (compactStageBank_widen_tape K d y) (compactStageWords_header d x)
    (compactStageWords_free d y) v S hL hR
  simpa [Nat.add_assoc] using he

abbrev compactEarlyStates := stateCount ActivePrefixStageFullEarlyRun.program
abbrev compactLateStates := stateCount ActivePrefixStageFullLateRun.program

def compactEarlyProg (hQ : compactEarlyStates ≤ Q)
    (ι : Fin ActivePrefixStageFullEarlyRun.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageFullEarlyRun.count ≤ T) : Pr F T Q (prime+K) U :=
  compactNativeProg (liftQ (Alphabet.program (Alphabet.widen prime K) ActivePrefixStageFullEarlyRun.program) hQ)
    compactStageHeader ι hι hT

theorem compactEarlyProg_exec (body : F → Pr F T Q (prime+K) U)
    (hQ : compactEarlyStates ≤ Q)
    (ι : Fin ActivePrefixStageFullEarlyRun.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageFullEarlyRun.count ≤ T)
    (d : Inputs s) (x : Array s d.rows) (horder : d.stage.source.val<d.stage.target.val)
    
    (hq3 : s.guard+3≤s.chunk)
    (hRbits : (ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1≤s.payload)
    (D : ℕ) (hdensity : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1)≤D)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j, S.L (ι j)=[])
    (hR : ∀ j, S.R (ι j)=compactStageWords d x j) :
    ∃ v' m, v'.user=v.user ∧
      m ≤ (T+12*ActivePrefixStageFullEarlyRun.count+5)*(ActivePrefixStageFullEarlyRun.cost D d horder) +
        6*(∑ j : Fin ActivePrefixStageFullEarlyRun.count, (compactStageWords (A := prime+K) d x j).length) +
        2*T+6*ActivePrefixStageFullEarlyRun.count+23 ∧
      Exec body (compactEarlyProg hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun z => if z ∈ Set.range ι then [] else S.L z
          R := fun z => if h : z ∈ Set.range ι then
            compactStageWords d (earlyResult d horder x) (Classical.choose h) else S.R z }) := by
  exact compactStageWiden_exec body ActivePrefixStageFullEarlyRun.program hQ ι hι hT d x _ _
    (ActivePrefixStageFullEarlyRun.runs d x horder hq3 hRbits D hdensity) v S hL hR

def compactLateProg (hQ : compactLateStates ≤ Q)
    (ι : Fin ActivePrefixStageFullLateRun.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageFullLateRun.count ≤ T) : Pr F T Q (prime+K) U :=
  compactNativeProg (liftQ (Alphabet.program (Alphabet.widen prime K) ActivePrefixStageFullLateRun.program) hQ)
    compactStageHeader ι hι hT

theorem compactLateProg_exec (body : F → Pr F T Q (prime+K) U)
    (hQ : compactLateStates ≤ Q)
    (ι : Fin ActivePrefixStageFullLateRun.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageFullLateRun.count ≤ T)
    (d : Inputs s) (x : Array s d.rows) (horder : d.stage.target.val<d.stage.source.val)
    (hn : 0<d.stage.f-1) (hb : 2≤s.guard)
    (hq3 : s.guard+3≤s.chunk)
    (hRbits : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1≤s.payload)
    (D : ℕ) (hdensity : VaryingControlRepairDensity.lateDensity s.chunk s.guard (d.stage.f-1)*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1)≤D)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j, S.L (ι j)=[])
    (hR : ∀ j, S.R (ι j)=compactStageWords d x j) :
    ∃ v' m, v'.user=v.user ∧
      m ≤ (T+12*ActivePrefixStageFullLateRun.count+5)*(ActivePrefixStageFullLateRun.cost D d horder hn hb) +
        6*(∑ j : Fin ActivePrefixStageFullLateRun.count, (compactStageWords (A := prime+K) d x j).length) +
        2*T+6*ActivePrefixStageFullLateRun.count+23 ∧
      Exec body (compactLateProg hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun z => if z ∈ Set.range ι then [] else S.L z
          R := fun z => if h : z ∈ Set.range ι then
            compactStageWords d (lateResult d horder x) (Classical.choose h) else S.R z }) := by
  exact compactStageWiden_exec body ActivePrefixStageFullLateRun.program hQ ι hι hT d x _ _
    (ActivePrefixStageFullLateRun.runs d x horder hn hb hq3 hRbits D hdensity) v S hL hR

end
end IntegerMultBounds.MathlibTM2.Node
