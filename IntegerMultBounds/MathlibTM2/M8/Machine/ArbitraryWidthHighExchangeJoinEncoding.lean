module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighMovementPlacement
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighMovementSemantics
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeSemantics

/-! Concrete four-symbol encoding agrees with actual ordered high joining. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoinEncoding
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout

def encoded {n : ℕ} (x : Fin n → ZMod 2) : Fin n → Fin (prime+4) :=
  fun i => RecursiveRoleSerialization.encode (SparseRoleCircuit.encode (x i))

omit [Net] in
theorem sourceWord_eq {v : RecursiveInterchangeLayout.Descriptor}
    (x : Fin (volume prime v) → ZMod 2) :
    ArbitraryWidthHighExchangeShared.sourceWord x =
      RadixHighBlockJoinLoop.word (fun _ => blank) (encoded x) :=
  RecursiveRoleSerialization.source_eq_word _

omit [Net] in
theorem encoded_exchange (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2) :
    encoded (ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hr x) =
      ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hr (encoded x) := by
  funext z
  obtain ⟨c,rfl⟩ := (originalEquiv prime P e r G B hr).surjective z
  change RecursiveRoleSerialization.encode (SparseRoleCircuit.encode
    (ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hr x
      (originalEquiv prime P e r G B hr c))) = _
  rw [ArbitraryWidthHighExchangeSemantics.array_highSwap,ArbitraryWidthHighExchangeSemantics.array_highSwap]
  rfl

omit [Net] in
theorem join_word (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2) :
    RadixHighBlockJoinLoop.word (fun _ => blank)
      (RadixHighBlockJoinSemantics.join prime r (P*prime^r) (prime^(e-r)*G) (prime^(e-r)*B)
        (RadixHighBlockJoinSemantics.reindex
          (ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hr)
          (encoded (ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hr x)))) =
      ArbitraryWidthHighExchangeShared.sourceWord (exchangeJoin P e r G B hr x) := by
  rw [sourceWord_eq,encoded_exchange]
  have hw := RadixHighBlockJoinLoop.word_reindex
    (ArbitraryWidthHighMovementSemantics.output_volume prime P e r G B).symm
    (fun _ => blank)
    (RadixHighBlockJoinSemantics.join prime r (P*prime^r) (prime^(e-r)*G) (prime^(e-r)*B)
      (RadixHighBlockJoinSemantics.reindex
        (ArbitraryWidthHighMovementSemantics.input_volume prime P e r G B hr)
        (ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hr (encoded x))))
  rw [← hw]
  change RadixHighBlockJoinLoop.word (fun _ => blank)
    (ArbitraryWidthHighMovementSemantics.joinArray prime P e r G B hr
      (ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hr (encoded x))) = _
  rw [ArbitraryWidthHighMovementSemantics.join_after_exchange]
  rfl

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeJoinEncoding
