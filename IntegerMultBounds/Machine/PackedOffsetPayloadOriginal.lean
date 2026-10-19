module

public import IntegerMultBounds.Machine.PackedOffsetPayload
public import IntegerMultBounds.Machine.PackedOffsetPowerHeader

/-! Packed-word controlled payload rotations from original B/n/w headers.
The power header is physically synthesized and erased; its cost is retained
when there are no fibers. -/

@[expose] public section

namespace IntegerMultBounds.Machine.PackedOffsetPayloadOriginal
noncomputable section
open SharedPlacementAlphabet (setTape)
open PackedOffsetPayload

def bank (payload offsets : ℤ → Fin 4) (p s : ℤ) (bs ns ws : List Bool) : Tapes 17 0 :=
  setTape (PackedOffsetPayload.bank payload (fun _ => blank) offsets p 0 s bs [] ns ws)
    7 (fun _ => blank) 0

def powerBits (w : ℕ) := RecursiveChildQuotientsConstant.bits (2^w)

theorem generated (payload offsets : ℤ → Fin 4) (p s : ℤ)
    (bs ns ws : List Bool) (w : ℕ) :
    PackedOffsetPowerHeader.output (bank payload offsets p s bs ns ws) w =
      PackedOffsetPayload.bank payload (fun _ => blank) offsets p 0 s bs (powerBits w) ns ws := by
  apply congrArg₂ Tapes.mk <;> apply List.ofFn_injective <;> rfl

theorem scratch (payload offsets : ℤ → Fin 4) (p s : ℤ) (bs ns ws : List Bool) :
    PackedOffsetPowerHeader.ScratchBlank (bank payload offsets p s bs ns ws) := by
  intro i
  fin_cases i <;> exact ⟨rfl,rfl⟩

def program := seq (seq PackedOffsetPowerHeader.program PackedOffsetPayload.program)
  PackedOffsetPowerHeader.cleanup

/-- One fixed machine uses only original B/n/w descriptors and two literal
bit words. All generated controls, the generated power header and all other
private storage are erased; both original heads and exteriors are restored. -/
theorem runs (V : List Bool) (w n B : ℕ) (hV : V.length=n*w) (hB : 0 < B)
    (f g : ℤ → Fin 4) (p s : ℤ) (hf : f (p-1)=blank) (hg : g (s-1)=blank)
    (bs ns ws : List Bool) (hb : Counter.value bs=B)
    (hn : Counter.value ns=n) (hw : Counter.value ws=w)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns)
    (cw : GrowingCounterData.Canonical ws) (a : Fin (n*(2^w*B)) → Bool) :
    HoareTime program
      (fun z => z=bank (putWord f p (List.ofFn (fun i => bitSymbol (a i))))
        (putWord g s (V.map bitSymbol)) p s bs ns ws)
      (fun z => z=bank (putWord f p (PackedOffsetPayload.result V w n B a))
        (putWord g s (V.map bitSymbol)) p s bs ns ws)
      ((FixedBasePowerDescriptor.constant 2+8)*2^w+600*(n*(2^w*B))+152) := by
  let X := putWord f p (List.ofFn (fun i => (bitSymbol (a i) : Fin 4)))
  let Y := putWord f p (PackedOffsetPayload.result V w n B a)
  let O := putWord g s (V.map bitSymbol)
  have h₀ := PackedOffsetPowerHeader.constructs_linear (bank X O p s bs ns ws) w ws hw cw
    (scratch X O p s bs ns ws) rfl rfl
  rw [generated] at h₀
  have h₁ := PackedOffsetPayload.runs V w n B hV hB f g p s hf hg bs (powerBits w) ns ws
    hb (RecursiveChildQuotientsConstant.bits_value _) hn hw cb
    (RecursiveChildQuotientsConstant.bits_canonical _) cn cw a
  have h₂ := PackedOffsetPowerHeader.cleans_linear (bank Y O p s bs ns ws) w rfl rfl
  rw [generated] at h₂
  exact ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h) (by simp only [Nat.add_mul]; omega)

end
end IntegerMultBounds.Machine.PackedOffsetPayloadOriginal
