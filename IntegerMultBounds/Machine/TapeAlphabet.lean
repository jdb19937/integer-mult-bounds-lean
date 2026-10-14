module

public import IntegerMultBounds.Machine.Alphabet

@[expose] public section
namespace IntegerMultBounds.Machine.TapeAlphabet
variable {tapes states sourceAlphabet targetAlphabet : ℕ}

def mapConfig (encoding : Fin tapes → Alphabet.Encoding sourceAlphabet targetAlphabet)
    (configuration : Config tapes states sourceAlphabet) : Config tapes states targetAlphabet :=
  ⟨configuration.state, configuration.head,
    fun slot position => (encoding slot).encode (configuration.tape slot position)⟩

def mapTapes (encoding : Fin tapes → Alphabet.Encoding sourceAlphabet targetAlphabet)
    (bank : Tapes tapes sourceAlphabet) : Tapes tapes targetAlphabet :=
  ⟨bank.head, fun slot position => (encoding slot).encode (bank.tape slot position)⟩

def program (encoding : Fin tapes → Alphabet.Encoding sourceAlphabet targetAlphabet)
    (machine : Program tapes states sourceAlphabet) : Program tapes states targetAlphabet where
  tapes_pos := machine.tapes_pos
  start := machine.start
  transition := fun state symbols =>
    (machine.transition state (fun slot => (encoding slot).decode (symbols slot))).map
      (fun (nextState, action) => (nextState,
        fun slot => ((encoding slot).encode (action slot).1, (action slot).2)))

theorem map_step (encoding : Fin tapes → Alphabet.Encoding sourceAlphabet targetAlphabet)
    (machine : Program tapes states sourceAlphabet) (configuration : Config tapes states sourceAlphabet) :
    step (program encoding machine) (mapConfig encoding configuration) =
      (step machine configuration).map (mapConfig encoding) := by
  unfold step
  simp only [program, mapConfig, Alphabet.Encoding.decode_encode]
  cases transitionResult : machine.transition configuration.state
      (fun slot => configuration.tape slot (configuration.head slot)) with
  | none => rfl
  | some result =>
    rcases result with ⟨nextState, action⟩
    simp only [Option.map_some]
    congr 1
    congr 1
    funext slot position
    dsimp only
    by_cases atHead : position = configuration.head slot <;> simp [atHead]

theorem map_run (encoding : Fin tapes → Alphabet.Encoding sourceAlphabet targetAlphabet)
    (machine : Program tapes states sourceAlphabet) (elapsed : ℕ)
    (configuration : Config tapes states sourceAlphabet) :
    run (program encoding machine) elapsed (mapConfig encoding configuration) =
      (run machine elapsed configuration).map (mapConfig encoding) := by
  induction elapsed generalizing configuration with
  | zero => rfl
  | succ elapsed inductionHypothesis =>
    simp only [run, map_step]
    cases stepResult : step machine configuration with
    | none => rfl
    | some next => simpa only [Option.map_some, Option.bind_some] using inductionHypothesis next

theorem map_hoare (encoding : Fin tapes → Alphabet.Encoding sourceAlphabet targetAlphabet)
    {machine : Program tapes states sourceAlphabet} {pre post : TapePred tapes sourceAlphabet}
    {bound : ℕ} (execution : HoareTime machine pre post bound) :
    HoareTime (program encoding machine)
      (fun bank => ∃ original, pre original ∧ bank = mapTapes encoding original)
      (fun bank => ∃ original, post original ∧ bank = mapTapes encoding original) bound := by
  rintro bank ⟨original, ready, rfl⟩
  obtain ⟨elapsed, finalConfig, timeBound, executed, halted, endpoint⟩ := execution original ready
  refine ⟨elapsed, mapConfig encoding finalConfig, timeBound, ?_, ?_, finalConfig.tapes, endpoint, rfl⟩
  · change run (program encoding machine) elapsed (mapConfig encoding (original.start machine)) = _
    rw [map_run, executed]
    rfl
  · rw [map_step, halted]
    rfl

end IntegerMultBounds.Machine.TapeAlphabet
