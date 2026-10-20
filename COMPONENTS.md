# Components

Summaries of the checked components in `IntegerMultBounds/`, grouped by directory. Each entry says what is proved and what remains open. Paths are relative to `IntegerMultBounds/`.

## Machine

- `Machine/Composition.lean` and `Machine/Hoare.lean`: a concrete sequential
  composition of finite transition tables, exact execution with one extra
  transition, preservation of all tapes and heads at the connection, and
  time-bounded contracts derived from actual runs. The existing tape scan is
  connected to this contract interface. The design draws on [complexitylib](https://github.com/SamuelSchlesinger/complexitylib)'s
  composition approach (commit `3f4b5fe`); no external machine semantics or
  runtime assumptions are imported.
- `Machine/Loop.lean`: a concrete finite-state while loop testing only scanned
  symbols, exact body-plus-two-transition iteration cost, and a telescoping
  potential rule charging variable body runtimes. It introduces no counter
  comparison scans or output rewinds. Client routines must still establish
  the invariant and pay for their actual tape execution.
- `Machine/Branch.lean`: a finite-state conditional testing only scanned
  symbols. One transition enters the selected branch with every tape and head
  preserved, and the branch's halt halts the whole machine. The contract
  charges the larger branch bound plus one.
- `Machine/Frame.lean`: finite-table tape extension and reindexing, with
  exact-step simulation and time-contract transport. Extra tape contents and
  heads are preserved literally, without parking assumptions or runtime
  overhead. Combining extension and reindexing places fixed routines in a
  larger fixed tape bank; it does not provide random access to fields on a tape.
- `Machine/Counter.lean`: executable fixed-width binary increment, its exact
  modular value, and an amortized bound of `2*n + width` bit flips from arbitrary
  initial contents.
- `Machine/Rewind.lean`: a one-state backwards scan over any finite alphabet,
  with exact runtime to a sentinel, arbitrary integer head origins, complete
  tape preservation, and a Hoare contract.
- `Machine/Alphabet.lean`: finite-alphabet encodings preserve exact execution,
  halting, and time contracts; the widening instance preserves blank, bits,
  and separator. Decoding also simulates arbitrary larger-alphabet tapes.
  That weaker observation does not itself preserve foreign marker symbols;
  their preservation requires a separate locality invariant.
  of each tape, with arbitrary larger-alphabet cells retained literally outside
  that region. Head-trajectory hypotheses establish preservation of foreign
  markers and exact runtime; halting also requires the final read in-region.
- `Machine/BitTape.lean` and `Machine/CounterTape.lean`: a three-state tape
  implementation of that increment, with exact carry and return runtimes,
  overflow handling, preservation of cells outside the bit segment, and a
  compositional time contract. A fixed four-state cyclic controller performs
  `n` increments within `8*n + 2*width` actual transitions from arbitrary initial
  contents, counting loop-control steps. This proves finite-prefix execution;
  a terminating stream scheduler remains to be built.
- `Machine/BinaryAdd.lean`: a fixed three-tape, three-state binary adder
  processes equally padded little-endian operands. The finite control stores
  carry; the exact transition count equals the output length, at most the
  input width plus one. Both entire inputs are preserved, and blank output
  initialization yields the exact sum with globally blank tails. Padding and
  output initialization are explicit preconditions.
- `Machine/BinarySub.lean`: a fixed three-tape, two-state subtractor
  takes exactly one transition per padded input bit. It preserves both
  complete source tapes and retains the final borrow in finite control.
  The modular subtraction identity, exact underflow criterion, ordinary
  nonnegative subtraction, and globally blank-tail output are proved.
- `Machine/BinaryPad.lean`: a one-state, two-tape scan physically pads two
  little-endian operands to their maximum width with high zero bits. It
  preserves both numeric values and halts in exactly that maximum width,
  with complete padded word tapes and both heads at the common end. Rewinding
  to the start for arithmetic is a separate charged operation.
- `Machine/BinaryCompare.lean`: a fixed three-tape, four-state comparator for
  LSF binary words of unequal widths, reading a missing high bit as zero and
  keeping the order so far in control. It writes one bit, whether the first
  operand is strictly smaller, at the output head and preserves both operands
  with each head parked on its own blank end; cost the larger width plus one,
  with the exact value correspondence proved.
- `Machine/ExactFrame.lean`: exact-bank forms of the extend and reindex rules
  for any alphabet, a halting empty program for conditional branches, the
  rewind to a word's origin from an arbitrary position over an arbitrary
  background, and two one-tape moves, step left and prepend a zero bit.
  multiplier by Horner's rule. The multiplier is read from its most
  significant bit down; each bit doubles the accumulator by writing a zero one
  cell left of its origin and, when set, adds the multiplicand in place and
  rewinds both heads, so the accumulator's origin moves left one cell per bit
  and no word is copied. Both operands are preserved, the accumulator holds
  the exact product with a proved width bound, and the cost is at most
  `m(5w + 2m + 18)` for a `w`-bit multiplicand and `m`-bit multiplier.
- `Machine/BinaryDecrease.lean`: a fixed two-tape, two-state in-place
  subtractor: the subtrahend is scanned together with the minuend, a missing
  high bit read as zero, each column difference written back over the minuend
  with the borrow in control, halting on the common blank. The subtrahend is
  preserved with its head parked on its end; the modular difference word, its
  exact value without underflow and the cost of the common width are proved.
- `Machine/PrependRead.lean`: a two-tape, four-state move that reads the bit
  under the first head, optionally steps that head left, and writes the bit
  or its negation one cell left of the second head, in two transitions.
- `Machine/BinaryDivide.lean`: a fixed five-tape, thirty-three-state
  restoring long divider. Each dividend bit, from the most significant down,
  is prepended to the remainder, the remainder is compared with the divisor,
  the divisor is subtracted in place when it fits, the quotient bit is
  prepended to the quotient word and the one-cell comparison flag is erased;
  remainder and quotient origins move left one cell per bit. Dividend and
  divisor are preserved, the remainder and quotient words have the exact
  values, and the cost is at most `m(4m + 6k + 27)` for an `m`-bit dividend
  and `k`-bit divisor.
- `Machine/PlacementBank.lean`: reading a replaced bank cell by cell: at an
  active slot the replacement appears, elsewhere the original bank is
  unchanged; an exact contract placed by an injective slot map yields an exact
  whole-bank contract once the banks are compared index by index.
  the compact-control instance in the radices `2^q`, `2^b`: copy the rank's
  bits from the counter into the two address words, run the guard test and
  write the membership flag at the key's origin, run the inverse packed
  program and the ideal toggle, append the destination words to the key when
  flagged, and erase every scratch word. The counter, control and constants
  are preserved, the key holds the flag word of the repair scan, every head
  returns to its origin; linear cost. The placements and frames are
  generated mechanically. Widths and digit counts are built into finite control
  through counted copies and iterated guard/packed programs; this is a proved
  program family, not the fixed runtime-driven key required by EndToEnd.

- `Machine/Execution.lean`: run composition, locality of writes, unit head
  motion, and an actual one-tape scanning program with exactly `n` transitions
  through `n` nonblank cells. The program preserves the tape and halts at the
  first blank. This is a stream primitive, not a multiplier.
- `Machine/WordTape.lean` and `Machine/Copy.lean`: finite-alphabet segment
  placement and appending, plus concrete two-tape copy and move programs with
  exactly one transition per symbol. The delimiter, complete source and
  destination tapes, and cells outside both segments are tracked in the time
  contract. Copying onto a blank tape gives the exact global blank-tail output
  representation. These routines are ingredients for record-stream processing;
  complete radix sorting is not yet implemented.

- `Machine/RadixSort.lean` and `Machine/PartitionSort.lean`: executable stable
  least-significant-bit sorting, with permutation, numeric sortedness, exact
  equal-key subsequence preservation, and a key-width-times-volume identity.
  The concrete partition's two outputs concatenate to precisely one such pass,
  with their total volume equal to its actual transition count. Full tape
  sorting is supplied separately by `TapeRadixSort`; the list traversal volume
  is not itself claimed as the machine runtime.

- `Machine/ReturnOrigin.lean`: a one-tape, three-state routine returns a head
  from the end of a blank-backed nonblank word to its origin in the word
  length plus two transitions, retaining the tape.
  radix sorter, the prefix stripper, the head return, and the alphabet-widened
  reinserter. Keyed records (key bits then the flagged record) are sorted by
  key, stripped, and reinserted into the flagged full stream; the exact-run
  contract lists every tape and head, and the cost is at most `74k + 4`
  extracted volumes plus one full-stream volume plus `k + 7`. Radix sorting
  commutes with key-preserving record maps.
  record's flag from a key tape and, when the flag is set, moves the key's
  destination bits to the extracted stream and copies the record behind them
  in the raw keyed format, erasing the key tape back to its marked blank
  state. Exact cost: the record length, plus twice the key width plus three
  when flagged.
  from the end of a word to its origin over either a blank or a marked
  background in the word length plus two transitions.
- `Machine/LoopChain.lean`: a while loop whose iterations form a chain of
  exact-tape contracts runs from the first bank to the last within the sum of
  the iteration bounds plus two control transitions each.
  exceptional-address repair on the fourteen-slot repair bank. A binary rank
  counter drives a loop whose body runs a key routine (a program parameter
  with a per-rank contract: read the counter, write the flag and destination
  bits), the flag copier, and the counter increment; two head returns and the
  sort-strip-reinsert stage follow. The complete machine has an exact-run
  contract, and its cost is the key cost plus ten per record, three stream
  volumes, `74k + 5` extracted volumes, `2k + 3` per extracted record, and
  `k + 14`.

- `Machine/RadixDigits.lean`: Fixed-radix digit alphabet, decoder and least-significant-first word value, with exact encoding/decoding and word-width bounds.
- `Machine/RadixAdd.lean`: Literal three-tape, two-state fixed-radix modular addition. Exactly one transition per padded digit, actual halting, exact output remainder and final carry, with arbitrary tape backgrounds and complete source preservation.

- `Machine/RadixUnary.lean`: Generic literal two-tape finite-table digit transducer. Exact-width execution and halting, arbitrary finite control, full source preservation and output-local writes; the finite table is fixed independently of word length.
- `Machine/RadixDivisionData.lean`: Bounded-carry prime-radix division by a fixed positive denominator below the radix. The d-state local congruence telescopes to exact integer and word-modulus division identities.

- `Machine/RadixRationalData.lean`: Arbitrary signed rational-numerator scaling in prime radix with a fixed finite signed-carry interval. The exact local congruence, interval invariant and full-word integer identity are proved; no state bound depends on width.
- `Machine/RadixRational.lean`: Literal two-tape rational-coefficient multiplication, including negative coefficients, with one transition per digit. The exact finite carry table implements the actual Swap.Modular.ratMod coefficient at every word modulus; exact runtime, halting and complete source preservation are proved.

- `Machine/CountdownData.lean`: Fixed-width binary decrement, exact borrow trace, zero detection and potential telescoping. All successful decrement/return/payload calls and terminal underflow cost at most five times the initial count plus twice the clock width plus two.
- `Machine/CountedCopy.lean`: Literal three-tape, five-state raw block transfer controlled by a binary count. Copies exactly the supplied count, even across blank payload symbols, preserves the source and destination background, and genuinely halts within the proved countdown bound. Clock preparation/reset and payload-head repositioning remain explicit caller operations.

- `Machine/CountedCopyReuse.lean`: Literal four-tape, sixteen-state reusable raw block transfer. Copies the immutable binary descriptor into a work clock, performs counted transfer, erases the clock, and returns both control heads. Exact runtime includes all joins and resets and is at most five times payload length plus seven times descriptor width plus sixteen. Descriptor construction and payload-head positioning remain explicit caller work.

- `Machine/BlockNegationData.lean`: Coordinate negation preserves block zero and reverses the remaining block order while retaining each internal payload. Exact payload indices, involution, width and volume are proved; reversing the raw tail and reversing each fixed-width pop realizes the same data recipe. Literal nested block scheduling remains separate.
- `Machine/ScalingControl.lean`: Fixed-multiplier residue control selects the unique source stream from Q modulo c and one finite output-residue state. Its transition, source reconstruction, clipped ceiling endpoints and exact piece sizes are proved, independently of word width. These are finite-control semantics; literal split/merge execution remains open.
- `Machine/BlockRotationData.lean`: Controlled cyclic block-shift semantics: split at Q-a, rejoin suffix first, preserve exact internal payload indices and total volume. Uniform-width flattening matches a literal payload cut at (Q-a)*B; per-fiber offsets preserve the entire payload permutation. These are list semantics, not a tape runtime.
- `Machine/ScalingPieces.lean`: Positive unit scaling split into quotient pieces, with unique divisibility-selected merge streams, exact source reconstruction and strictly increasing order inside each piece. The complete piece streams partition the output addresses, including multipliers above the modulus. No tape runtime is asserted.

- `Machine/Reflection.lean`: Reversing any fixed selection of tape head directions produces a literal finite transition table with exact step, run, halt and Hoare transport. Word reflection reverses its list representation; this is a simulation theorem, not a free tape reversal.
- `Machine/CountedReverse.lean`: Literal binary-counted backwards source read with forwards output and an unchanged forwards clock. Produces the exact reversed raw word, including blank payload symbols, preserving the source and destination background; the same linear countdown bound includes every real transition. The reusable variant also charges clock preparation, erasure and control-head resets. Initial source-head positioning and descriptor construction remain preconditions.

- `Machine/Placement.lean`: Generic whole-bank placement of a fixed-tape program. Active projection and replacement preserve the complete complementary tapes and heads; exact runs, real halts and Hoare contracts lift without extra transitions. Sequential exact contracts charge their connecting transition.
- `Machine/CountedSeek.lean`: Literal three-tape, sixteen-state forward and backward positioning by a binary descriptor. Proven projection of the reusable copying machine discards its irrelevant destination; every payload cell and the immutable descriptor survive, the work clock is restored, and all preparation/cleanup costs fit five times the count plus seven times descriptor width plus sixteen.

- `Machine/CountedRotate.lean`: Literal six-tape, sixty-four-state raw cyclic rotation: seek past a prefix, copy the suffix, seek backwards over the total block, and copy the prefix. The source and three immutable descriptors are preserved and the clock is restored. Exact single-fiber controlled-shift semantics follow from block payload indexing; all seeks, clock setup/cleanup and joins cost at most fifteen times volume plus descriptor-width terms. Descriptor synthesis and multi-fiber scheduling remain open.

- `Machine/CountedLoop.lean`: A fixed finite-state binary-counted body loop with a dedicated final clock tape. Actual Hoare chains with varying body costs execute in their summed costs plus at most six times the iteration count, twice the clock width and two. All decrement scans, returns, body joins and terminal underflow are charged; the clock finishes all ones. Preparation and cleanup remain explicit.

- `Machine/GrowingCounterData.lean`: Growing-width binary increment from the empty zero word, exact value increment, canonical highest-one invariant and logarithmic width. A bit-weight potential bounds all increment-and-return costs by four times the increment count plus twice initial width.
- `Machine/GrowingCounter.lean`: Literal growing binary increment writes a new high bit at the end blank and returns to its sentinel. Exact execution and halting, canonical growth from an empty marked tape and amortized costs including cycle joins are proved; no counter width is prepared in advance.

- `Machine/CountedRotateAdvance.lean`: Literal cyclic block rotation followed by a charged suffix seek, so both payload heads reach the next block. Source and descriptors survive, the reusable clock is empty, and all routines and joins cost at most fifteen times block length plus descriptor-width terms.
- `Machine/WordSegments.lean`: Exact local tape-word indexing and matching-segment replacement. A middle word of a placed concatenation is already present at its length-offset origin; these representation identities justify local stream views without asserting free tape operations.
- `Machine/FiberShift.lean`: A fixed seven-tape, eighty-five-state counted controller rotates successive uniform raw fibers by a common prepared cut. Source and prior output are preserved, both data heads advance the entire volume, and inner controls reset. Canonical prepared descriptors and nonempty fibers give actual runtime at most 177 times payload volume plus four; outer count preparation/cleanup and varying offsets remain separate.

- `Machine/CountedLoopReuse.lean`: Generic fixed counted body loop with an immutable count descriptor. Physically prepares the mutable clock, runs the counted body chain, erases the clock and resets both control heads, preserving the descriptor. All body costs plus six times the count, seven times descriptor width and sixteen bound the actual execution. Public metadata cleanup also erases any padded binary word and resets its head while preserving an immutable companion descriptor, charging both scans.

- `Machine/BlockReverseAdvance.lean`: Literal four-tape, fifty-two-state reversal of a raw block with both payload heads finishing at the next block. Two counted seeks, a backwards read-copy, two single-cell moves and all four joins cost at most fifteen times length plus twenty-one times descriptor width plus fifty-four, including empty blocks.
- `Machine/BlockReverseStream.lean`: Fixed five-tape, fifty-seven-state counted repetition reverses each uniform block while preserving block order, source and prior output. Both heads advance the full volume and inner controls reset; canonical descriptors and positive width give actual runtime at most 119 times volume plus four. The outer count remains consumed.

- `Machine/Dispatch.lean`: Literal dispatch among a fixed finite family of programs using only scanned symbols. One stationary tape-preserving transition selects the branch, and exact execution, true halt and Hoare contracts add exactly one step to the selected body cost.
- `Machine/ScalingMergeData.lean`: Sequential FIFO semantics for positive unit scaling. Prefix selection counts equal the inverse source offset within each contiguous piece; selected streams never underflow, all pieces are completely consumed and recursive head-pop merging gives the exact inverse-scaled payload. Pure semantics only; no tape runtime is asserted.

- `Machine/CountedErase.lean`: Delimiter-free scratch erasure using a literal one-cell body and reusable counted loop. Preserves all cells outside the interval and restores an initially blank scratch segment, with immutable descriptor and empty clock restored. Actual cost is at most seven times length plus seven times descriptor width plus sixteen, or fourteen times length plus twenty-three for canonical descriptors.
- `Machine/OneHot.lean`: Fixed finite residue encoding on control tapes under their current heads. Decoding reads scanned symbols only, and one literal stationary transition increments the residue modulo the fixed bank size, preserves every head and background cell and truly halts. Exact execution and Hoare contracts charge one step.

- `Machine/ScratchReset.lean`: Fully reusable raw scratch cleanup: physically rewind from the segment end, erase the exact interval, and rewind to its origin. Initially blank scratch is restored including its head, while surrounding cells and immutable length descriptor survive. All three routines and joins cost at most seventeen times length plus twenty-one times descriptor width plus fifty, or thirty-eight times length plus seventy-one with a canonical descriptor.
- `Machine/BlockReverseStreamReuse.lean`: Fixed six-tape, sixty-eight-state blockwise reversal with immutable block-count and block-width descriptors. Both inner and outer mutable clocks are prepared and cleared, control heads reset, and payload heads advance the full volume. Canonical descriptors and positive block width give actual runtime at most 124 times payload volume plus twenty-three.

- `Machine/ScalingSplit.lean`: Literal fixed-coefficient partition into contiguous source pieces on separate tapes. A fixed sequence of reusable counted copies preserves the source and all piece-length descriptors, with exact output words and final heads, including empty pieces. Cost is five times volume plus seven times the sum of descriptor widths plus seventeen times the fixed piece count, or twelve times volume plus twenty-four times piece count for canonical descriptors.
- `Machine/ScalingMerge.lean`: Literal fixed-coefficient FIFO merge via scanned-symbol dispatch, counted block copies and one-hot residue updates. Actual repeated execution writes the exact inverse-scaled payload, preserves source tapes, descriptors and modulus control, and clears both clocks. Prepared canonical descriptors and positive block width give at most fifty-one times volume plus twenty-three steps. Source heads initially at piece starts and residue banks are explicit prerequisites.
- `Machine/ScalingPieceBridge.lean`: Exact representation bridge from flat literal split pieces to contiguous block streams consumed by the merge. Proves arbitrary uniform-block interval slicing and preserves every intra-block cell, including zero-width blocks and empty pieces. This is a representation equality, not a free tape move.

- `Machine/BlockNegationReuse.lean`: Complete eight-tape, 202-state reusable coordinate negation: copy block zero, reverse the raw tail, physically rewind, reverse individual blocks with reusable controls, then erase and rewind scratch. Source/descriptors survive; both clocks and the entire initially blank scratch interval with its original head are restored. Canonical prepared descriptors and positive width give actual cost at most 210 times volume plus 219.

- `Machine/ScalingSplitRewind.lean`: Literal fixed-coefficient buffer rewinds after splitting. Each buffer physically returns to its original head using its preserved piece-length descriptor, with no data changes and full clock cleanup. The combined split-and-rewind machine writes exact contiguous pieces at merge-ready heads; canonical descriptors give actual cost at most twenty-four times volume plus forty-eight times fixed piece count plus one.

- `Machine/OneHotCount.lean`: Actual fixed-modulus residue construction from an immutable binary count. Writes zero into arbitrary control cells and performs counted literal residue advances; heads and background cells survive and the mutable clock resets. Twenty fixed states, cost seven times count plus seven times descriptor width plus eighteen, or fourteen times count plus twenty-five for canonical descriptors.
- `Machine/ScalingControlInit.lean`: Initializes both scaling residue banks from arbitrary control-cell contents: modulus becomes Q modulo fixed c, current becomes zero. One real initialization transition and reusable counted advances preserve descriptor, clock, all heads and background cells. The complete cost is linear in Q and fits the positive-width payload-volume budget.

- `Machine/ScalingExecution.lean`: Complete literal positive-unit scaling through fixed-coefficient split, physical buffer rewinds and FIFO merge. A static placement shares actual buffers; source and descriptors survive and destination block c*y modulo Q is original block y. Tape count ten plus four times fixed coefficient and state count forty-eight times coefficient plus twenty-one are independent of Q and B. Prepared canonical descriptors and residue banks give cost at most seventy-five times volume plus forty-eight times coefficient plus twenty-five.
- `Machine/ScalingBuffersReset.lean`: Literal fixed-family scratch cleanup after scaling. Each buffer is physically rewound, erased and rewound again; initially blank intervals and original heads are restored with source and control tapes preserved. Canonical piece descriptors give cost at most thirty-eight times total volume plus seventy-two times fixed piece count.

- `Machine/ScalingScatter.lean`: Literal inverse-scaling routing from a single sequential source to finitely many piece buffers, selected by actual residue control and dispatch. Buffers acquire contiguous pieces of y mapped to input at c*y modulo Q, preserving every payload block. Both clocks reset and prepared descriptors survive; canonical descriptors and positive dimensions give at most fifty-one times volume plus twenty-three steps. Physical buffer concatenation remains separate.

- `Machine/ScalingExecutionReuse.lean`: Complete reusable positive-unit scaling with actual residue-control initialization, split, physical rewinds, merge, and temporary-buffer erasure/reset. Arbitrary initial residue cells are accepted; source, canonical immutable descriptors, complete scratch backgrounds and scratch heads are preserved. Fixed ten plus four-c tapes and ninety-eight-c plus forty-two states; actual runtime at most 127 times volume plus 120 times fixed coefficient plus fifty-two. Binary descriptors remain prepared inputs.

- `Machine/ScalingConcatenate.lean`: Literal concatenation of a fixed family of raw piece buffers into one destination. Each source starts at its segment end, is physically rewound and copied, and ends at its original end position; source contents, descriptors and clock survive. Exact output is the flattened family in index order; canonical descriptors give cost at most twenty-four times total volume plus forty-eight times fixed piece count.
- `Machine/ScalingPartitionData.lean`: Contiguous quotient pieces concatenate to the complete block list, both for natural-index and Fin-indexed physical buffer families. This pure representation bridge identifies inverse-scatter concatenation with input blocks indexed by c*y modulo Q, preserving every intra-block payload cell.

- `Machine/ScalingStream.lean`: Literal repeated positive-unit scaling on uniform fibers with real control reinitialization and shared restored scratch. Exact per-fiber payload permutation, unchanged source, advanced payload heads, preserved descriptors and fully reset inner/outer clocks. Fixed twelve plus four-c tapes and ninety-eight-c plus fifty-eight states; canonical prepared descriptors give actual bound (192 plus 120 times c) times total payload volume plus twenty-three.

- `Machine/ScalingDescriptorData.lean`: Growing binary descriptor family for exact contiguous scaling-piece lengths. Selector prefix counts identify each value and final piece length; descriptors remain canonical. A telescoping family carry potential bounds all actual increment/return transitions by four times payload volume, avoiding a binary-width charge per increment.
- `Machine/ScalingDescriptors.lean`: Literal piece-length descriptor synthesis from canonical Q/B descriptors and genuinely blank derived-descriptor/work tapes. Initializes sentinels and residue controls, dispatches B counted growing increments to the selected piece for Q iterations, and restores mutable clocks. All output descriptors are exact and canonical; actual cost at most seventy times Q*B plus fifty-one for positive B. No piece-length descriptor oracle is assumed.

- `Machine/ScalingInverseExecution.lean`: Complete reusable inverse positive-unit scaling: initializes residue banks, scatters blocks to pieces, physically rewinds/concatenates them, then erases and resets all buffers. Output block y is original input block c*y modulo Q; entire source, scratch backgrounds/heads and immutable descriptors survive, all clocks reset. Fixed ten plus four-c tapes and ninety-eight-c plus forty-one states; prepared canonical descriptors give actual runtime at most 127 times volume plus 120 times fixed coefficient plus fifty-one.

- `Machine/CountedSpanSeek.lean`: Whole-fiber forward/backward positioning from separate block-width and block-count descriptors. A fixed five-tape, thirty-two-state reusable loop performs every physical move and restores both clocks/descriptors without a product-length descriptor. Canonical descriptors and positive width give rewind cost at most forty-eight times fiber volume plus twenty-three.
- `Machine/CountedSpanReset.lean`: Complete intermediate-fiber cleanup from separate width/count descriptors. Physically rewinds, erases all blocks using reusable counted loops, and rewinds again; initially blank scratch contents and original head are restored, with all other cells and both descriptors preserved. Fixed five tapes and ninety-eight states, canonical cost at most 146 times fiber volume plus seventy-one.

- `Machine/ScalingAffineBridge.lean`: Exact semantic link from literal positive/inverse scaling and block negation to ordered-affine target-coordinate updates. Proves signed numerator/denominator list composition and instantiates every actual Shared50 rational scale at all prime-power widths using proved unit recipes. Preserves intra-block payload orientation; contains no uncharged tape operation or new runtime claim.

- `Machine/ScalingPreparedExecution.lean`: Complete literal one-fiber positive-unit scaling with piece descriptors generated from blank work tapes. Static placement shares the generated descriptors and Q/B controls with the reusable scaling machine, initializes remaining sentinels physically, and preserves source plus restored scratch buffers. Only canonical Q/B descriptors are supplied; generated descriptors and explicit work-marker states remain in the final bank. Fixed eleven plus four-c tapes and 117-c plus eighty-five states; actual runtime at most 197 times volume plus 120 times fixed coefficient plus 106.

- `Machine/SignedScalingExecution.lean`: Unsigned rational scaling core, despite the broader module name: literal positive numerator scaling, physical shared-intermediate rewind, denominator inverse scaling, and complete intermediate erase/reset. Exact numerator/denominator payload semantics with source, coefficient scratch and shared intermediate restored. Fixed twenty-five plus four times the sum of coefficients tapes; cost448*volume+120*(numerator+denominator)+200. Canonical per-coefficient descriptors remain prepared, and optional sign negation is not part of unsignedProgram.

- `Machine/SignedScalingSign.lean`: Complete literal signed rational scaling with a compile-time sign choice. Positive coefficients use the unsigned numerator/denominator core; negative coefficients additionally perform real intermediate rewind, block-preserving coordinate negation and full scratch cleanup. Exact signedBlocks payload and all source/scratch/control guarantees proved. Bound is448*volume+120*(a+d)+200 for positive and852*volume+120*(a+d)+516 for negative. Canonical coefficient descriptors remain prepared; canonical tail length/count descriptors are required only in the negative branch.
- `Machine/BinaryOneInit.lean`: Literal two-transition construction of a constant-one binary descriptor from a genuinely blank tape. Writes its sentinel and one digit, leaves the head on that digit and truly halts; exact value and canonicality proved. Supports the Q-minus-one descriptor bootstrap needed by negation.

- `Machine/BinarySubReuse.lean`: Literal immutable-input binary subtraction with unequal operand widths. Reads blank operand cells as zero, writes a sentinel and padded exact Q-a output from blank work, and physically resets all three heads. Fixed three tapes and thirteen states; cost four times maximum input width plus fourteen. Output width is exactly that maximum; canonicality is deliberately not asserted.
- `Machine/TranslationProduct.lean`: Literal product-length descriptor synthesis via nested counted growing increments, with input counts on immutable tapes and a fixed selected output slot. A telescoping carry proof pays total work linearly in N*B. Output is canonical when grown from empty even if the supplied N count has padding; no input-size-dependent controller or free arithmetic is used.
- `Machine/TranslationDescriptors.lean`: Complete literal shift-length synthesis from canonical Q,a,B descriptors with a≤Q and positive B. Initializes markers, physically subtracts Q-a, then constructs canonical (Q-a)*B, a*B and Q*B descriptors by actual nested loops, preserving all inputs. Fixed ten tapes and 120 states; bound163*Q*B+92. Generated metadata is explicit at the endpoint; reuse cleanup remains separate.

- `Machine/ActualAffineScaling.lean`: Instantiates the fixed signed-scaling machine for every actual Shared50 scalar coefficient. The program depends on the rational coefficient, never on radix exponent or payload width; the chosen-prime unit recipe discharges numerator/denominator legality. Exact symbol transport matches OrderedAffine target scaling at every prime-power width, with bound (1368+120*(absolute numerator+denominator))*payload volume. Canonical descriptor and blank scratch hypotheses remain explicit.

- `Machine/TranslationDescriptorsReuse.lean`: Reusable shift-length synthesis and literal metadata cleanup. From marked empty output counters, subtraction and three products create canonical split lengths while preserving Q,a,B; fixed118-state execution costs163*Q*B+90. A fixed19-state cleanup erases all three generated counters and the padded subtraction word, resets every metadata head, and physically removes the scratch sentinel, restoring the exact next-iteration bank. Cleanup costs at most8*Q*B+30 under the supplied canonical dimension assumptions.

- `Machine/TranslationPreparedExecution.lean`: Complete literal single-fiber translation from canonical Q,a,B descriptors, with a≤Q and positive dimensions. Starts derived-work tapes blank, constructs all split lengths, and physically rotates the payload through fixed shared placement. Source is preserved, both payload heads advance Q*B, and output block y+a modulo Q retains the exact source block y, including a=0 and a=Q. Fixed twelve tapes and200states; bound199*Q*B+212. Derived metadata is retained explicitly; iteration cleanup is separate.

- `Machine/NegationDescriptors.lean`: Literal canonical tail metadata construction from supplied Q/B descriptors only. Writes its own constant one on blank tape, synthesizes (Q-1)*B and the padded difference, and uses counted multiplication by one to produce a canonical Q-1 descriptor. Preserves Q/B and leaves explicit generated metadata/control banks. Fixed eleven tapes and160states; bound216*Q*B+121 for positive Q/B.

- `Machine/FamilyPlacement.lean`: Static pairing and framing of independent tape-bank placements, with exact active/extra bank laws and charged sequential execution. Placement wires finite transition tables without assuming physical transfers.

- `Machine/SignedScalingPrepared.lean`: Constructs both numerator and denominator piece-descriptor families from canonical Q/B before executing signed rational scaling. Exact signedBlocks output and full-bank contracts; bound (1612+120*(a+d))*Q*B. Fixed 40+4*(a+d) tapes. Negative-tail descriptors and the fixed split-clock sentinel remain explicit input requirements; generated coefficient metadata is retained. Public allPrepareProgram/allPrepare_hoare expose the once-only coefficient setup independently of execution.

- `Machine/TranslationExecutionReuse.lean`: Literal split-length synthesis, rotation and complete derived-metadata cleanup in one reusable twelve-tape machine. Exact modular forward shift, immutable source and Q/a/B, and both payload heads advanced Q*B. Recurring 217-state bound 207*Q*B+241; initial 219-state program starts writable metadata blank and costs 207*Q*B+243. Changing the supplied offset between calls still requires physical preparation.

- `Machine/TranslationStream.lean`: Repeated common-offset translation with literal descriptor recomputation and cleanup on each fiber. One fixed fourteen-tape, 235-state machine initializes all writable metadata from blank, preserves the source and supplied canonical Q/a/B/n, and proves the exact full final bank, including zero fibers. Runtime at most 461 times physical payload volume plus 25 for positive Q/B. Varying-offset preparation and prefix scheduling remain separate.

- `Machine/TranslationPreparedFamily.lean`: Varying-offset translation composed with one supplied fixed physical preparation program and an actual counted loop. Exact full-bank contracts preserve payloads during preparation and preserve arbitrary preparation workspace during translation. Costs the sum of actual preparation bounds plus 462 times payload volume plus 23; fixed 14+s tapes and m+233 states. Explicitly conditional on preparation Hoare contracts, with recurring marked initial workspaces. Concrete offset arithmetic and spectator scheduling remain to be instantiated.

- `Machine/SignedScalingDimensions.lean`: Complete signed rational scaling from canonical Q/B numeric inputs, synthesizing both coefficient-piece families and negative-tail descriptors by literal machines. Exact signedBlocks destination, full-bank endpoint, restored negation scratch and explicit retained metadata. Bound (1950+120*(a+d))*Q*B; fixed 49+4*(a+d) tapes. Scratch blankness and inherited fixed sentinel layouts remain explicit; it does not claim a blank-workspace bootstrap or full stream scheduler. Public bootstrapProgram/bootstrap_hoare expose charged negative-tail setup independently of execution.

- `Machine/RadixToBinaryData.lean`: Pure radix countdown and canonical binary output semantics with borrow/carry amortization. Zero-digit potential bounds total modeled conversion work by 10*value+2*width+2, hence 12*q^width+2 for q at least two; binary output has exactly the source value. This is the data/cost lemma, not yet the literal conversion-machine correctness theorem.

- `Machine/ActualAffineScalingDimensions.lean`: Specializes dimension-based signed scaling to every rational coefficient occurring in the actual Shared50 schedules. Membership proves coefficient positivity/unit legality at every prime-power width. One fixed program per coefficient, exact full-bank and ordered-affine output contracts, restored negation scratch, and bound (1950+120*(abs numerator+denominator))*q^b*B. No derived numeric descriptors supplied; inherited fixed sentinels and scratch layouts remain explicit. This proves one fiber, not the full network scheduler.

- `Machine/BinaryReplace.lean`: Seven-state two-tape binary descriptor replacement: erases the old word, copies a physically supplied replacement and restores both heads, preserving the source exactly. Full-bank bound 2*oldWidth+2*newWidth+8 includes removal of stale longer suffixes.

- `Machine/RadixToBinary.lean`: Literal radix-to-canonical-binary converter for fixed q at least two, using three tapes, eighteen states and a q+4-symbol alphabet. Physically initializes markers, copies and rewinds source, runs amortized radix countdown with binary growth, erases work and removes the temporary source marker. Exact full-bank output, original source/head preserved, scratch blank/head restored. Bound 10*value+6*width+14, hence 16*q^width+14 and 30 times nonempty fiber volume. Handles empty words, zero and leading radix zeroes; alphabet-lifted connection to translation is separate.

- `Machine/SignedScalingStream.lean`: Actual counted iteration of the signed rational scaling machine across consecutive equal-volume fibers. Exact boundary invariant tracks advanced source/destination heads, updated physical residue cells, preserved descriptor banks and restored shared scratch. Bound (1381+120*(a+d))*totalVolume+23; fixed 40+4*(a+d) tapes. Coefficient and negative-tail descriptors are prepared inputs, with explicit marked controls; once-only dimension-based setup composition is separate.

- `Machine/SignedScalingDimensionsStream.lean`: One-time literal tail/coefficient descriptor synthesis followed by counted signed scaling across all fibers. Canonical Q/B/n numeric inputs only, exact full-bank endpoints with metadata and synthesis spares retained. Cost (1381+120*(a+d))*volume+356*Q*B+249, or (1737+120*(a+d))*volume+249 for nonempty families. Explicit inherited/outer sentinels and scratch requirements remain; fixed 51+4*(a+d) tapes.

- `Machine/ActualAffineScalingStream.lean`: Specializes dimension-based streams to each actual Shared50 scalar, proving exact output symbols at every concrete fiber offset and ordered-affine action for explicitly represented address fibers. Program depends only on coefficient; one-time setup charged, full-bank endpoint proved, nonempty linear constant 1737+120*(abs numerator+denominator). Arbitrary whole-field layout identification and full network scheduling remain separate.

- `Machine/MarkedWordCleanup.lean`: Literal marker installation, nonblank-word erasure, rewind and marker removal over arbitrary finite alphabets. One tape, six states; exact fully blank/head-zero endpoint in 2*width+6. Requires a nonblank word at cell one on otherwise blank tape.

- `Machine/BinaryDescriptorReset.lean`: Physically clears a binary descriptor including its sentinel and restores a genuinely blank output tape for reuse. Exact endpoint and charged scan bound; supports the recurring rational-to-binary pipeline.

- `Machine/RadixRationalBinary.lean`: Fixed-rational radix arithmetic followed by actual canonical binary conversion and complete radix scratch cleanup. Four tapes over q+4 symbols; marked source preserved with head one, both scratch tapes blank with heads zero. Bound 10*resultValue+10*width+27, at most47 times positive fiber volume. Modular interpretation assumes denominator less than prime q.

- `Machine/RadixRationalBinaryReuse.lean`: Recurring rational-to-binary computation erases the previous binary descriptor before recomputing. Exact marked-source preservation and blank scratch; bound 2*oldWidth+10*resultValue+10*width+32, at most54 times fiber volume for a canonical prior offset below the modulus.

- `Machine/RationalOffsetPrepare.lean`: Concrete five-tape recurring fixed-rational scalar offset computation, conversion, scratch cleanup and physical destination descriptor replacement. Both output copies are canonical and equal; marked radix source is preserved. At most67 times positive fiber volume for canonical prior descriptors below the modulus. Rational semantics require denominator below prime q; prefix scheduling and fixed linear combinations remain separate.

- `Machine/RadixCounterData.lean`: Fixed-width radix increment with exact modular value, increasing enumeration and wraparound to zero. Maximal-digit potential proves cycle cost at most6*n+2*width and at most8*q^width for a complete traversal.

- `Machine/RadixCounter.lean`: Literal three-state radix incrementer restores the digit head after carries and overflow. Four-state cyclic controller exposes exact finite-prefix runs with arbitrary payload frames preserved; complete traversal enumerates all radix values and returns the exact bank in at most8*q^width steps. The cyclic controller does not halt; counter initialization and mixed-field scheduling remain separate.

- `Machine/RationalTranslationExecution.lean`: Concrete sixteen-tape rational-controlled single-fiber translation: physical rational arithmetic, binary conversion, descriptor replacement, rotation and cleanup share the actual offset tape. Exact recurring full bank, source preserved, both payload heads advanced, marked radix control untouched. Cost274*Q*B+242, hence516*Q*B for positive B. Only active binary/payload tapes are alphabet-lifted; foreign radix cells are preserved as frames. Rational interpretation requires denominator below prime radix; multi-control combinations and prefix scheduling remain separate.

- `Machine/CountedLoopAlphabet.lean`: Binary-counted iteration of an arbitrary-alphabet body, with exact physical countdown/head-reset semantics and actual body transitions preserved. Core exact-bank cost is sum of body bounds plus6*n+2*countWidth+2; binary cleanup is supplied by the reusable wrapper.

- `Machine/CountedLoopReuseAlphabet.lean`: Reusable counted loop over arbitrary body alphabets, encoding only its two binary control tapes and framing all body symbols literally. Exact whole-bank endpoints, immutable descriptor and restored clock; sum of body costs plus6*n+7*countWidth+16 includes preparation and cleanup. Adds two tapes and sixteen states; uses the exposed CountedLoopReuse.prepare_exact contract.

- `Machine/PrefixCounterData.lean`: Multi-field radix carry semantics, exact flattened-prefix modular enumeration, width preservation and wraparound. Sum of maximal-digit potentials gives cost at most(4*c+2)*n+2*sum(widths), avoiding a spectator-width multiplier on each iteration.

- `Machine/PrefixCounter.lean`: Concrete fixed-field-count carry scheduler over separate radix tapes with physical head restoration. 3*c+1-state incrementer and 3*c+2-state cyclic controller; exact joint address enumeration and preserved arbitrary frames. Full finite traversal restores every field and payload bank within(4*c+4)*q^sum(widths). Fields have radix-power sizes q^b_i with arbitrary widths, including long spectators; arbitrary non-power ranges and initialization are not covered. Cyclic finite-prefix execution does not assert halting.

- `Machine/RationalTranslationStream.lean`: Concrete varying-offset family for one cyclic radix control: rational offset computation, translation, physical control increment and arbitrary-alphabet counted iteration. Exact recurring full-bank endpoints, cyclic control semantics and output length; bound534*physicalVolume+23 on eighteen tapes. Starts with explicit marked metadata, canonical Q/B/n and prior offset, and a marked radix control word. No derived descriptors or per-fiber preparation oracle; mixed-prefix scheduling and full field-layout identification remain separate.

- `Machine/FamilyPlacementAlphabet.lean`: Alphabet-polymorphic pairing, framing and charged sequential composition of tape banks. Uses static placement equivalences while preserving every symbol of arbitrary-alphabet frames; no physical transfer is assumed.

- `Machine/RadixAddReusable.lean`: Literal equal-width radix addition from blank-backed operands and blank output, all heads at zero. Writes/removes markers, preserves both operands and restores every head; three tapes/six states, cost2*width+5. Modular sum semantics and width preservation proved. Eighteen-state consume variant erases both temporary operands, leaving only the sum, in6*width+19. Supports reusable arithmetic for multi-control offsets.

- `Machine/RadixZeroFill.lean`: Physical zero-radix-field construction from a supplied binary width descriptor. Writes markers and placeholders by actual counted iteration, recodes backward to radix zero, and returns the field head. Three tapes, twenty-three states; bound8*n+7*descriptorWidth+21, or15*n+28 for canonical widths. Field/work tapes start blank; dimension descriptor is preserved and control scratch returns to its explicit reusable marked state.

- `Machine/PrefixCounterInit.lean`: Fixed-field-count physical initialization from canonical binary width descriptors, with all output and clock tapes initially blank. Sequential radix zero-fill constructs every field; exact full-bank endpoint and injective field projection identify the zero PrefixCounter bank. Cost15*sum(widths)+29*fieldCount; 3*fieldCount+1 tapes and23*fieldCount+1 states, including the empty family via an untouched spare. Width descriptors and explicit reusable clocks are retained; whole translation-bank assembly remains separate.

- `Machine/RadixLinearCombination.lean`: Fixed expression/list compiler executes rational leaves and modular addition nodes, physically erasing temporary operands and restoring source/scratch heads. Exact radix output equals the rational modular sum when denominators are below prime q. Coefficient-list bound(34*termCount+7)*q^b with3*termCount+2 tapes. Every leaf, including the zero seed, has a supplied marked source copy; repeated logical controls are not copied or refreshed for free. Binary endpoint and scheduler-source linkage remain separate.

- `Machine/RadixLinearCombinationBinary.lean`: Fixed rational-expression arithmetic followed by one canonical binary conversion and physical erasure of the final radix result. Exact output descriptor/head, both converter work tapes blank/head zero, and original leaf-source workspace preserved. Coefficient-list bound(34*termCount+47)*q^b with3*termCount+4 tapes; binary value is the exact modular rational sum for denominators below prime q. Supplied per-leaf copies remain explicit; source duplication/refresh and recurring binary-output replacement are separate.

- `Machine/RationalPrefixTranslationExecution.lean`: Concrete rational-controlled fiber translation followed by physical multi-field prefix increment. Selected field zero supplies the offset; a fixed nonempty duplicate-free carry order may place it anywhere, with independent spectator widths. Exact full-bank endpoint preserves spectator tapes during translation and charges actual carry/rewind transitions:516*Q*B+1+prefixStepCost. Fixed16+c tapes for c+1 prefix fields. Prepared marked inputs and equal target/selected-control radix width explicit; repeated-family and layout assembly separate.

- `Machine/RationalPrefixTranslationStream.lean`: Actual counted translation across mixed-width prefix fields, with selected field zero supplying rational offsets and a fixed nonempty duplicate-free carry order. Exact evolving bank and modular offset semantics; cost(530+4*orderLength)*volume+2*initialTotalWidth+23. Full finRange traversal restores all prefix fields and costs(536+4*c)*volume+23 on18+c tapes for c+1 fields. Spectator widths incur no per-fiber full scan. Recurring marked initial bank remains explicit; initialization and whole-array layout assembly are separate.

- `Machine/PrefixAddressData.lean`: Whole-prefix radix address semantics: flattening fastest-first field words equals reversed lexicographic field order; full-order width sum and selected-field extraction proved. Zero-start PrefixCounter enumeration yields the actual prefix rank and selected control via division/modulo, allowing arbitrary spectator widths without a supplied address-family assumption.

- `Machine/FiberLayoutData.lean`: Constructs prefix/target/suffix fibers directly from a flat Fin(P*(Q*B)) array and proves flattening returns exactly its original List.ofFn. Per-prefix rotations transport each target entry while preserving every suffix symbol and total volume. scheduled_entry connects selected-counter extraction to these concrete flat-array addresses. Pure layout/address lemmas; physical runtime integration remains separate.

- `Machine/MarkedRadixRefresh.lean`: Physical replacement of a stale marked radix word from a shared source tape. Erases the old copy, copies actual source digits and restores both heads to one, preserving the source cell-for-cell and removing stale longer suffixes. Two tapes, seven states; exact whole-bank bound2*oldWidth+2*sourceWidth+8. Wiring this primitive across all expression leaves and scheduler controls is separate.

- `Machine/SharedPlacementAlphabet.lean`: Alphabet-polymorphic placement sharing one physical tape between an active program and a retained bank. Exact complete-tape/head replacement and framed Hoare contracts use static finite wiring, without a physical copy assumption. Complete-tape replacement commutes with appending either caller bank, including exact heads.

- `Machine/RadixLinearCombinationRefresh.lean`: Concrete refresh of every expression leaf from one shared physical control bank. Fin-bounded references determine fixed tape placements; recursive erase/copy programs preserve the shared bank and synchronize all stale leaf copies, including repeated references. Exact complete-bank theorem and runtime+1 at most leafCount*(4*width+9) when source/stale widths are bounded. Actual binary arithmetic composition and recurring output reset remain separate.

- `Machine/FlatControlledShift.lean`: Complete physical controlled shift on a flat Fin(P*(Q*B)) array, with fibers constructed from the input itself. Actual prefix enumeration supplies the selected rational control; exact source List.ofFn and every destination symbol proved, preserving prefix and suffix coordinates. Full-bank Hoare theorem costs(536+4*c)*volume+23. Requires canonical B/Q/P descriptors and a prepared marked zero prefix/work bank; no assumed address family or offset oracle. Target and selected control share radix width, spectator widths arbitrary, denominator below prime radix. Physical initialization handoff remains separate.

- `Machine/RadixLinearCombinationShared.lean`: One physical program refreshes stale expression leaves from a shared bounded control bank, computes the rational expression, converts to canonical binary and restores arithmetic/converter scratch. Exact shared-control preservation and output descriptor; finite-bank wrapper needs no unbounded extra source tapes. Cost(13*leafCount+expressionConstant+40)*q^b for common new width b and stale widths at most b. Leaf sentinels/head-one remain prepared inputs and binary output starts blank; first-use bootstrap and recurring output reset separate.

- `Machine/PrefixCounterInitPlacement.lean`: Explicit static permutation hands physically initialized prefix-field tapes to a consumer while retaining all width descriptors, clocks and spare tapes as frames. initialize_then composes real initialization with a proved consumer execution and charges their join; no field copying is assumed.

- `Machine/RationalPrefixTranslationInit.lean`: Composes actual blank-prefix initialization with FlatControlledShift on the same physical tapes. Exact active-stream output and transported flat-array symbols; bound(551+4*c)*volume+29*(c+1)+24 includes prefix setup. Canonical width/B/Q/P descriptors remain supplied; prefix outputs/clocks start blank. Fixed marked translation metadata is still explicit input, so this is not yet an entirely blank-workspace bootstrap.

- `Machine/FlatAffineScaling.lean`: Concrete flat-array theorem for every actual Shared50 rational scalar. Identifies the physical source with the supplied array and proves every output symbol keeps its prefix/suffix while the target is multiplied modulo Q. Exact full-bank execution includes descriptor synthesis and bound (1737+120*(abs numerator+denominator))*volume+249. Canonical dimension descriptors and inherited sentinel/scratch conditions remain explicit; composition of successive operations is separate.

- `Machine/MarkedBinaryCleanup.lean`: Four-state physical erasure of an encoded binary descriptor and its sentinel, returning a wholly blank tape/head zero without a supplied length descriptor; exact runtime bound 2*bits.length+4.

- `Machine/RationalPrefixTranslationBootstrap.lean`: Full flat-array controlled shift from blank writable prefix and translation metadata tapes. One actual transition installs eight markers and moves the spare head, then physical prefix initialization and stream execution run. Exact complete output bank inherits the transported-symbol theorem; bound (551+4*c)*volume+29*(c+1)+26. Only canonical width/B/Q/P descriptors and payload remain supplied; dimension construction and successive-operation composition are separate.

- `Machine/CountedVolumeLoop.lean`: Three actual nested counted loops over separate canonical B/Q/P descriptors; restores all clocks and preserves arbitrary body symbols. Exact per-cell iteration contract and explicit runtime; one-step body costs at most 109*volume. No total-volume descriptor is assumed.

- `Machine/FlatArrayNormalize.lean`: Eight-tape, 150-state three-pass payload transfer: physically rewind both heads, copy old output into common input while erasing it, then rewind both again. Exact full-bank contract restores output scratch and both origins, reuses B/Q/P descriptors, and charges 327*volume+2. Placement into concrete operation banks is separate.

- `Machine/FlatControlledShiftNormalize.lean`: Composes full concrete controlled shift with physical payload normalization on the same tape bank. Actual B/Q/P descriptors and clocks are reused by static placement; exact final offset/prefix metadata is retained, both payload heads return to origin, output scratch is restored and shifted symbols are on common input tape10. Bound (863+4*c)*volume+26 includes every pass. Prepared shift input remains explicit; blank-workspace wrapper and full schedule assembly are separate.

- `Machine/FlatControlledShiftReady.lean`: Composes physical blank-workspace marker setup, prefix initialization, concrete controlled shift and payload normalization. Exact full bank retains initializer and operation metadata; transformed symbols return to common input with output scratch/head origins restored. Bound (878+4*c)*volume+29*(c+1)+29 includes every stage. Canonical width/B/Q/P descriptors remain supplied; full fixed affine schedule and dimension construction remain separate.

- `Machine/FlatControlledShiftArray.lean`: Canonical finite-array representation of the physically normalized controlled-shift output. Proves the common input tape is exactly the new List.ofFn array on the original background, eliminating the nested old-word overlay. Supports subsequent operations with a different prefix/target/suffix split without an uncharged tape conversion.

- `Machine/StaticMarkerInit.lean`: Two-state machine installs a fixed coefficient-dependent marker/head template in one actual transition. Exact raw-to-target full-bank proof, origin-zero input heads, off-origin data preservation and append lemmas. The template is part of fixed finite control, not input dimensions.

- `Machine/FlatAffineScalingBootstrap.lean`: Actual rational scaling from blank generated storage, residue banks, intermediate payloads and sign scratch, with all heads initially zero. Physically installs coefficient-dependent sentinels and runs descriptor/residue synthesis and whole-array scaling; exact source and scaled destination symbols, bound nonemptyConstant*volume+251. Only canonical B/Q/P words in fixed input slots and payload remain supplied; dimension-word construction and common-input normalization are separate.

- `Machine/InjectivePlacement.lean`: Extends fixed injective physical tape slots to a complete static placement, with exact active-slot/bank lemmas. Existing placement Hoare rules preserve every complementary tape and head literally; no runtime relabeling or tape movement is introduced.

- `Machine/FlatAffineScalingNormalize.lean`: Attaches physical three-pass payload normalization to the actual scaling output using existing B/Q/P descriptors and clocks. Exact original source/destination slots, retained complementary metadata, restored scratch and heads, and scaled symbols on common input. Full bound (2064+120*(abs numerator+denominator))*volume+252. Prepared scaling input remains explicit; blank-workspace wrapper and schedule composition separate.

- `Machine/FlatAffineScalingReady.lean`: Complete actual rational scaling from blank generated workspace through physical normalization. Exact retained bank and transported symbols on original source; destination scratch and both heads restored. Bound (2064+120*(abs numerator+denominator))*volume+254 includes marker creation, descriptor synthesis, scaling and every normalization pass. Canonical dimension words and initially blank destination interval remain explicit inputs.

- `Machine/FlatAffineScalingArray.lean`: Canonical finite array produced by initialized normalized scaling. Exact coordinate multiplication, List.ofFn representation and original-source tape equality over the original background; eliminates the old input overlay so later target-coordinate splits use the same physical word.

- `Machine/FlatCoordinateLayout.lean`: One common row-major coordinate/index bijection for all targets, including modulus one and arbitrary trailing record width. Exact target-specific volume split, identical serialized source word, physical earlier-control extraction and scale/shift destination equations for OrderedAffine.execute. Concrete fiber transport bridges eliminate abstract address-family assumptions; actual machine specialization and shared-tape schedule composition remain separate.

- `Machine/FlatCoordinateScaling.lean`: Instantiates the common-coordinate layout with actual initialized normalized network scaling. Exact returned canonical array transports every coordinate/record according to OrderedAffine.execute scale; original source tape equals that array. Actual ready-machine Hoare contract includes all setup/movement and bound (2064+120*(abs numerator+denominator))*commonVolume+254; canonical dimension descriptors remain supplied.

- `Machine/FlatCoordinateShift.lean`: Actual initialized normalized controlled shift on the common row-major coordinate layout. Constructs the counter order so the selected control is after exactly the less-significant prefix fields; proves the physical offset equation and exact OrderedAffine shift transport of every symbol. Ready-machine Hoare theorem returns the canonical common-volume array on its original source, with all initialization/normalization costs; canonical dimension words remain supplied.

- `Machine/SharedPayload.lean`: Static injection shares a stage source/destination with two permanent payload tapes, retaining all private metadata and leaving private payload slots blank/head-zero. Exact active/frame identities and placed-stage Hoare rule; no runtime copies, head resets or relabeling operations.

- `Machine/SharedPayloadPair.lean`: Literal composition of two stages on the same permanent payload pair and separate stripped metadata banks. Proved exact whole-bank handoff when first output pair equals second input pair; costs both proved runtimes plus one sequence step. Concrete scaling/shift compatibility and full fixed schedule instantiation are separate.

- `Machine/FlatControlledShiftPayload.lean`: Exact payload-pair interface for the initialized normalized controlled-shift machine. Proves distinct actual source/destination slots and identifies input as the encoded original array and output as the encoded canonical shifted array on the same heads, with destination scratch restored. Supplies concrete tape compatibility for shared-payload stage assembly.

- `Machine/RadixPowerWord.lean`: Fixed 29-state physical machine reads binary b, constructs an unmarked radix word of b zeros followed by one (value q^b), clears its clock and preserves the exponent tape. All high-digit writes, scans and marker removal charged; runtime 10*b+7*inputWidth+27.

- `Machine/RadixPowerDescriptor.lean`: Fixed four-tape, 53-state machine computes canonical binary q^b from one canonical binary b descriptor, for fixed q>=2 including b=0. Physical radix construction, conversion and cleanup compose with exact full-bank output, preserved exponent and blank scratch. Bound99*q^b; no precomputed power or arithmetic oracle. Assembly of all affine dimension descriptors remains separate.

- `Machine/FlatAffineScalingPayload.lean`: Lifts the actual initialized normalized scaler to the common radix alphabet with the same runtime. Proves distinct physical source/output slots, exact canonical encoded input/output payload pairs with blank scratch and zero heads, and full concrete lifted Hoare execution. Supplies the scaling side of actual shared-payload handoff; no duplicate data or conversion work is assumed.

- `Machine/FlatControlledShiftMetadata.lean`: Proves the entire stripped initialized-shift metadata bank is independent of the payload array. Stage metadata can be supplied using a literal blank dummy array; no initial bank needs to contain or name an uncomputed prior stage result.

- `Machine/SharedPayloadFrames.lean`: Exact blank/head-zero contracts for unused private payload slots in stripped stage banks and two-stage input/output. Confirms that only the two permanent payload tapes carry data, with no hidden per-stage copies.

- `Machine/FlatAffineScalingMetadata.lean`: Proves the entire lifted scaling private input bank, after removing the two permanent payload slots, is independent of the finite input array. Only fixed coefficients and dimension descriptors determine this metadata; later scaling stages can be prepared before their actual input is computed.

- `Machine/SharedPayloadStage.lean`: Exact stage interface bundling an actual program, canonical shared payload pair, input-independent private metadata and proved execution cost. Intended for physical finite-list assembly; actual machine constructors must discharge every contract.

- `Machine/FlatCoordinateStages.lean`: Concrete common-coordinate scale and earlier-control shift Stage constructors at the actual shared prime alphabet. Instantiates all program, payload, metadata-independence and runtime contracts from initialized normalized machines; exact transform theorems prove OrderedAffine symbol transport. Canonical dimension inputs remain explicit; finite-list assembly and uniform schedule theorem separate.

- `Machine/RadixPowerMultipleWord.lean`: Fixed-many counted passes read one preserved binary width and construct its radix power word, with restored scratch and charged initialization, rewind and cleanup. The multiplier belongs to finite control.

- `Machine/RadixPowerMultipleDescriptor.lean`: Actual four-tape constructor of canonical binary q^(k*b) from binary b, with k fixed in finite control. Preserves b and restores both scratch tapes blank; bound (24*k+75)*q^(k*b), including k=0 and b=0. Supplies prefix/suffix powers for coordinate dimension synthesis.

- `Machine/SharedPayloadStageCompose.lean`: Actual finite-list compilation of heterogeneous machine stages onto one common payload pair, preserving each private metadata bank. Proves literal final bank and folded payload semantics, with sum of stage costs plus every joining transition. Concrete coordinate schedule instantiation and runtime-independent skeleton are separate.

- `Machine/SharedPayloadStageSkeleton.lean`: Erases array types, semantic contracts and supplied descriptors to retain only finite machine data. Proves finite-stage compilation depends solely on these skeletons; transports exact bank execution and metadata independence to a previously fixed program. Concrete width-independent coordinate skeletons are established separately.

- `Machine/FlatCoordinateSchedule.lean`: Fixed rational scale/earlier-control shift operation description, canonical dimension descriptors and concrete Stage instantiation. Proves exact primitive transport, costs, and equality of entire finite-machine skeleton to one selected independently of width and record size.

- `Machine/FlatCoordinateScheduleCompile.lean`: One fixed multitape program executes every supported finite rational coordinate schedule for all widths and positive record sizes. Proves exact OrderedAffine.run symbol transport, input-independent private metadata, and explicit linear-volume runtime including all joins. Canonical dimension words remain supplied; their physical synthesis/installation and recursive interchanges are separate.

- `Machine/BinaryDescriptorCopy.lean`: Actual two-tape, five-state binary descriptor copier from a preserved source to a wholly blank destination. Installs the destination sentinel, copies every bit, restores both heads to one and proves exact whole-bank output in 2*length+5 steps; alphabet-lifted contract uses standard encodedBinary tapes.

- `Machine/Shared50NonrecursiveCoordinates.lean`: Actual Shared50 nonrecursive field operations instantiate supported fixed coordinate schedules with proven coefficient occurrence and order. Negative-one scaling support is derived from an actual preFields transform. Proves exact H/D output and one dimension-independent physical machine with linear-volume cost; canonical dimensions supplied and recursive interchange excluded.

- `Machine/BinaryDescriptorCopies.lean`: Fixed-many physical replication of one binary descriptor onto genuinely blank tapes, preserving the sole source and restoring every head. Uses n+1 tapes and 5*n+1 states, no workspace; exact whole-bank contract costs n*(2*length+6), including every join, with a canonical logarithmic bound.

- `Machine/Shared50NonrecursiveSegments.lean`: Actual nonrecursive Shared50 schedule segments compile to one fixed physical machine. Every output symbol follows the exact AffineFieldProgram.run on the embedded H/D coordinates; complete intermediate arrays need not be supplied. Explicit linear-volume bound includes all stage joins; canonical dimension descriptors remain supplied and recursive calls excluded.

- `Machine/BinaryDescriptorInstall.lean`: Places the actual five-state descriptor copier between arbitrary distinct tape slots. Exact whole-bank output replaces only the blank destination with the copied canonical descriptor at head one; source and every complementary tape/head are preserved. Runtime 2*length+5 and placement size derived from distinctness.

- `Machine/BinaryDescriptorInstallRaw.lean`: Actual copy followed by two-transition marker removal yields the marker-free descriptor at head zero required by bootstrap machines. Exact complete-bank setTape postcondition preserves source and all other tapes; fixed eight-state program costs2*length+8 including the join.

- `Machine/DimensionProductDescriptor.lean`: Physical six-tape product-descriptor constructor from two canonical binary inputs and wholly blank workspace. Installs markers, executes counted multiplication, restores scratch and preserves both inputs; exact canonical product output with bound53*N*W+28 for positive W.

- `Machine/TranslationDimensions.lean`: Actual nine-tape dimension bank from sole canonical b/W inputs. Fixed prefix/suffix counts select finite control; computes Q=q^b, P=q^(p*b), S=q^(s*b), B=S*W, preserves inputs and restores scratch. Exact canonical words and bound(24*p+24*s+333)*P*Q*B include every setup, conversion, product and join.

- `Machine/FlatCoordinateDimensions.lean`: Specializes physical dimension synthesis to an actual shared-prime coordinate target. Proves the constructed words literally match the canonical Q/P/B expected by FlatCoordinateSchedule, with common-volume runtime, preserved b/W inputs and blank initial workspace. Canonical b/Q/P/B descriptor lengths are bounded by twice common volume, charging later setup scans. Full stage-input installation remains separate.

- `Machine/PrefixWidthCopies.lean`: Replicates a sole preserved binary width into the exact physical PrefixCounterInit descriptor slots, with all fields, clocks and spare tapes initially blank. Proves full output-bank equality and runtime c*(2*length+6), including all copy joins.

- `Machine/PrefixWidthCopiesAt.lean`: Places prefix-width replication beside an arbitrary retained dimension bank, sharing its existing width source. Preserves every dimension-bank tape/head and constructs exact prefix input from blank, with no extra supplied source and unchanged copy bound.

- `Machine/FlatControlledShiftLayout.lean`: Exact complete input decomposition for the actual controlled-shift bootstrap. Exposes the prefix width bank and seventeen-tape suffix with only B/Q/P and payload supplied; every other tape/head is blank/zero. Identifies concrete descriptor slots for physical installation.

- `Machine/ControlledShiftDimensionInstall.lean`: Actual three-copy program installs B/Q/P from the retained nine-tape dimension bank into the controlled-shift suffix, starting each destination blank. Exact full-bank contract preserves dimensions and payload, with cost2*(length B+length Q+length P)+17 including joins.

- `Machine/FlatCoordinateShiftFromDimensions.lean`: Complete actual earlier-control shift from sole canonical exponent/record-width descriptors and payload, with all generated storage blank. Physically builds dimensions, installs prefix widths and B/Q/P, executes normalized shift, retains exact dimension bank and canonical transformed array. One dimension-independent machine has explicit linear common-volume bound charging all setup, scans and joins.

- `Machine/FlatCoordinateShiftInput.lean`: Exact initial common-payload contract and payload-independent private metadata for fully synthesized shift. Proves distinct physical payload slots and literal blank workspace at every slot except the sole exponent/record-width inputs and original payload. Supplies initialized-stage assembly contracts.

- `Machine/BinaryDescriptorInstallList.lean`: Compiles a fixed list of physical marker-free descriptor installations, with shared preserved sources and distinct blank destinations. Exact fold/setTape final bank, destination contents and frame preservation are proved. Costs sum(2*length+9), including cleanup and every join, with a uniform length bound.

- `Machine/FlatAffineScalingInputLayout.lean`: Fixed structural classification of every raw scaling input tape as workspace, payload or B/Q/P descriptor. Proves exact complete raw, ready and alphabet-lifted input banks, including all repeated dimensional words and blank head-zero workspace. Exposes the literal target layout for physical installation.

- `Machine/SharedBank.lean`: Actual placement of any fixed number of common tapes shared with a stage. Proves exact whole-bank execution with unchanged runtime; unused private selected slots remain literally blank frames, without implicit copying or head movement.

- `Machine/SharedBankFrames.lean`: Projection, clearing and frame lemmas for fixed shared banks, including exact empty private metadata through append/composition. Supports compiling initialized stages while keeping only permanent common inputs nonblank.

- `Machine/FlatCoordinateShiftSharedBank.lean`: Four-tape common interface for initialized shifts: payload, output scratch and original b/W headers. Proves injective physical slots, exact common input/output with preserved headers, and literally blank entire private input after stripping common tapes; enables schedules with one physical b/W pair.

- `Machine/FlatAffineScalingInstall.lean`: Physical fixed descriptor-copy list installs every marker-free B/Q/P copy in the actual scaling input. Proves source-bank preservation, exact full layout handoff from blank workspace and coefficient-dependent linear-volume copying cost.

- `Machine/FlatCoordinateScalingConstruct.lean`: Complete actual coordinate scaling from sole canonical b/W and array. One coefficient/target-dependent program constructs dimensions, installs all descriptor copies, executes and normalizes the scaler, retaining dimension bank. Exact canonical scaled payload and blank workspace contract; explicit linear-volume bound includes every setup, scan and join.

- `Machine/SharedBankPair.lean`: Actual composition of two heterogeneous machines sharing any fixed common tape bank. Exact private frames and payload handoff are preserved with one charged join; unused private common slots remain blank.

- `Machine/SharedBankStage.lean`: Concrete stage contract and physical finite-list compiler over any fixed common-bank size. Proves folded common-state semantics, exact complete output, sum of stage runtimes plus all joins, and propagation of literally blank private input storage.

- `Machine/SharedBankSkeleton.lean`: Extracts fixed machine data from shared-bank stages and proves finite compilation depends only on those skeletons. Transports exact execution to a program selected independently of runtime semantic data, including a stronger theorem with entirely blank private inputs.

- `Machine/FlatCoordinateShiftSharedStage.lean`: Fully initialized controlled shift instantiates the four-common-tape Stage contract. Payload and sole b/W headers are shared, private input is literally blank, transition table independent of runtime dimensions, and exact affine transport and linear-volume cost are proved.

- `Machine/FlatCoordinateScalingSharedBank.lean`: Four-common-tape interface for fully initialized scaling, proving unique actual source classification, injective payload/header slots, exact common input/output and entirely blank private input. The original b/W descriptors are preserved physically.

- `Machine/FlatCoordinateScalingSharedStage.lean`: Actual initialized scaling instantiates the same four-common-tape Stage contract as shifts. Proves fixed skeleton, empty private metadata, coefficient/target-dependent linear cost and exact OrderedAffine transport; no computed dimensional input is supplied.

- `Machine/SharedBankStageInput.lean`: Literal common-bank input theorem: the first common tapes contain the supplied payload and headers, all others are blank at head zero. Fixed compiled Hoare execution preserves the exact final common bank and charges all stage costs and joins.

- `Machine/FlatCoordinateInitializedSchedule.lean`: One fixed physical machine executes any supported finite mixed scaling/shift schedule from the array and sole canonical b/W inputs with blank private storage. Exact ordered-affine output, preserved headers and explicit linear-volume runtime include all dimension synthesis, descriptor installation and joins.

- `Machine/Shared50InitializedSegments.lean`: Actual nonrecursive Shared50 field-program segments execute from sole b/W and payload with all private tapes blank. The fixed machine has exact field-program symbol transport and a setup-inclusive linear-volume bound; recursive interchanges and heterogeneous spectator layouts remain separate.

- `Machine/StackPop.lean`: Fixed arbitrary-alphabet destructive stack transfer, controlled by a reusable binary clock. Heads move left together, preserving original data order and erasing exactly the popped region; all exterior cells, the immutable length descriptor and restored clock are retained. Exact whole-bank semantics and 7n+7 descriptor-length+16 time; initial head positioning and descriptor construction remain caller obligations.

- `Machine/RecursiveInterchangeLayout.lean`: Seven-factor recursive child descriptors preserve literal spectator order, exact role volume and next-depth row divisibility; physical scheduling is separate.

- `Machine/RecursiveInterchangeScaling.lean`: Actual normalized rational scaling on either H or D in an arbitrary positive seven-factor recursive layout. Exact serialized input/output and address transport preserve all rows and spectators, with a linear-volume runtime; canonical prefix/modulus/suffix descriptors remain supplied.

- `Machine/FixedControlTranslationStream.lean`: Actual counted family of rational-controlled D-fiber translations with a stationary physical H control. The middle-spectator count is arbitrary, every offset refresh/copy/join is charged, and the exact recurring endpoint preserves control. Prepared descriptors and markers remain explicit.

- `Machine/FlatFixedControlShift.lean`: Flat-array bridge for stationary-control translation across arbitrary middle spectators. Literal source word, exact destination coordinate transport, preserved physical H control and 529 times volume plus 23 runtime are proved. Outer H/prefix iteration and full bootstrap remain separate.

- `Machine/CyclicRowCopy.lean`: Arbitrary-alphabet row copy into one fixed role tape, with literal source/destination symbols, exact entire bank and reusable binary clock. No payload terminator assumptions; row count descriptor preserved.

- `Machine/CyclicRowCycle.lean`: One fixed finite cycle distributes successive equal-length rows over every fixed role tape using a shared reusable descriptor/clock. Exact role contents and all heads, with every copy and join charged. Closed state counts and proved state-index transport avoid unary kernel expansion at the actual fixed role count, retaining the execution contracts.

- `Machine/CyclicRowSplit.lean`: Runtime-counted grouping repeatedly executes a fixed role cycle. Role j receives precisely its row from every group, including arbitrary payload symbols; complete bank and restored controls, fixed tapes/states independent of runtime dimensions and explicit 74-times-volume bound. Descriptor construction and positioning are separate.

- `Machine/CyclicRowMergeCopy.lean`: One actual arbitrary-symbol row transfer from a selected role back to a common output, preserving all other roles and restoring binary loop controls.

- `Machine/CyclicRowMergeCycle.lean`: Fixed role-by-role physical merge cycle with exact output concatenation, preserved input streams and summed count/copy/join runtime. Closed state counts and proved state-index transport avoid unary kernel expansion at the actual fixed role count, retaining the execution contracts.

- `Machine/CyclicRowMerge.lean`: Runtime-counted physical merge restores cyclic row order from all role streams. Exact complete bank and advanced heads, restored controls and 74-times-volume bound; row permutation wiring, descriptor synthesis and rewinds remain caller work.

- `Machine/StackPush.lean`: Destructive arbitrary-symbol parking append via actual reflected StackPop transitions. Exact forward head displacement, preserved symbol order, source erasure and outside-region frames; reusable clock and immutable descriptor, with the same explicit length-plus-descriptor runtime.

- `Machine/CountedPosition.lean`: Fixed arbitrary-alphabet counted head motion preserves every payload cell, immutable binary descriptor and restored clock. Exact displacement for either direction, runtime 7n+7 descriptor-length+16 and canonical linear bound, including zero distance. No free seek is used.

- `Machine/RecursiveInterchangeRows.lean`: Actual cyclic split/merge instantiated for seven-factor recursive descriptors. Proves literal flat source and role serialization, original row roles*g+j, exact role descriptor addresses and 74-times-parent-volume bounds. Canonical row/group descriptors, prepositioned heads and role permutation wiring remain explicit.

- `Machine/TrackedCleanup.lean`: Actual data/tracker cleanup from a visited interval with an origin marker. Erases internally blank arbitrary data and tracker cells, restores both heads to zero, and proves a linear-radius bound without scanning parked ancestors.

- `Machine/TrackedExecution.lean`: Fixed two-transition simulation of each original transition on doubled tapes/states, same alphabet. Synchronized tracker heads and marked visited intervals preserve exact original execution and bound every private written cell; no runtime size changes the finite controller.

- `Machine/TrackedInit.lean`: Physically constructs tracker origin/initial-position marks from blank extra tapes for a fixed zero/one initial head pattern in two transitions, preserving original data.

- `Machine/TrackedHoare.lean`: Initialization plus tracked execution has exact original output, generated visited intervals, private support and 2 times original bound plus3 cost. No prebuilt trackers or runtime boundary descriptors are assumed.

- `Machine/TrackedCleanupOne.lean`: Tracker-only erasure restores its blank tape and head zero while permitting the associated common data tape and head to remain untouched.

- `Machine/TrackedCleanupAt.lean`: Physical placement of data/tracker or tracker-only cleanup in fixed bank slots with exact frame preservation and complete resulting banks.

- `Machine/TrackedCleanupList.lean`: Fixed finite list cleans every tracker and every selected private data tape, retaining designated common tapes/heads. Runtime is tapeCount times (5 times radius plus6); all runtime interval boundaries come from actual trackers.

- `Machine/CleanExecution.lean`: Generic actual composition initializes trackers, executes a fixed machine, and erases all private data/tracking storage. Exact retained output and blank workspace have explicit constant-factor time overhead.

- `Machine/FlatCoordinateCleanSchedule.lean`: One fixed initialized mixed affine schedule starts and ends with literal common array/scratch/b/W plus wholly blank private tapes and trackers. Every symbol has exact ordered-affine semantics; all initialization, execution and cleanup are linear in volume, enabling workspace reuse.

- `Machine/Shared50CleanSegments.lean`: Actual nonrecursive Shared50 field segments execute from sole canonical b/W and array, return the exact transformed canonical array and retained headers, and erase all private metadata/trackers with heads zero. Exact field-program semantics and linear-volume time; recursive heterogeneous execution remains separate.

- `Machine/CyclicRowRewind.lean`: Actual counted rewind of common and role heads preserves every arbitrary symbol. A fixed role cycle reuses the existing row/group descriptors without constructing a product count, and restores exact original heads in linear-volume time. Closed state counts and proved state-index transport avoid unary kernel expansion at the actual fixed role count, retaining the execution contracts.

- `Machine/CyclicRowNormalized.lean`: Actual cyclic split/merge followed by counted rewinds return every payload head to its original position, retain exact source and role words, and restore both binary controllers. Canonical positive dimensions give a 149-times-volume bound.

- `Machine/RecursiveInterchangeRowsNormalized.lean`: Normalized split/merge specialized to literal seven-factor recursive arrays: exact cyclic role semantics, original heads restored, preserved controls and 149-times-parent-volume time. Descriptor synthesis and full recursive dispatch remain caller obligations.

- `Machine/PointwiseBinary.lean`: Fixed finite binary symbol operation executed over a runtime-counted pair of streams. Exact source preservation and pointwise destination/frame theorem, physical head advancement, restored clock and explicit runtime. XOR specializes correctly on encoded bits; payload rewinds and full sparse-circuit assembly remain separate.

- `Machine/RepeatedControlTranslationExecution.lean`: Actual middle-spectator translation group followed by one physical H increment. Exact recurring bank and charged arithmetic/control transitions; arbitrary middle count uses binary runtime control.

- `Machine/RepeatedControlTranslationStream.lean`: Nested physical middle-spectator/H loops handle arbitrary outer prefix cardinality, preserve exact source/output streams and restore zero H after complete cycles. Fixed20-tape machine,570 times volume plus 23; canonical descriptors and prepared metadata remain explicit.

- `Machine/FlatRepeatedControlShift.lean`: Literal flat-array source and every destination symbol for heterogeneous H-controlled D shifts, including exact rational offset and zero-control restoration across arbitrary prefix cycles.

- `Machine/CountedHyperVolumeLoop.lean`: Four independently counted runtime dimensions drive actual fixed finite loops, restoring all binary loop controls and charging every countdown/copy/join. No product descriptor or unrolled runtime-dependent program is assumed.

- `Machine/FlatHyperArrayNormalize.lean`: Physical four-dimensional array normalization copies the result, erases old payload scratch and returns both payload heads, using supplied dimension descriptors with all scans charged.

- `Machine/FlatRepeatedControlNormalize.lean`: Four-dimensional normalization placed on the existing 20-tape repeated-control bank, preserving all arithmetic metadata while returning canonical payload pair.

- `Machine/FlatRepeatedControlArray.lean`: Exact canonical transformed array for the normalized heterogeneous shift, with source/scratch payload interface and full-bank runtime 1005 times volume plus 26.

- `Machine/RecursiveInterchangeShift.lean`: Actual normalized H-controlled D shift on arbitrary positive seven-factor layouts. Exact rational H offset, preserved rows/spectators, canonical input/output arrays and restored zero control, with linear-volume time. Canonical B/Q/C/N descriptors and prepared arithmetic bank remain explicit; construction/cleanup separate.

- `Machine/FiniteReturnStack.lean`: Actual fixed-width binary return-address push/pop preserves all older frames, erases popped bits and restores the stack top. Pop halts in a finite state carrying the decoded address; width/state count depend only on fixed schedule, with depth-independent exact runtime.

- `Machine/FiniteDispatch.lean`: Fixed finite family dispatcher branches from an actual front-program halt state into its selected continuation in one charged transition. Exact execution, halting state and Hoare composition; all continuation programs are fixed in the finite controller.

- `Machine/FiniteReturnDispatch.lean`: Actual binary stack pop in a selected tape slot followed by decoded return-address dispatch into a fixed continuation family. Preserves the entire other-tape frame and charges width plus 2 plus continuation time. Full cyclic recursion and descriptor frames remain separate.

- `Machine/CyclicRowPermutedMerge.lean`: Fixed tape wiring restores logical cyclic row order when network output role j occupies physical tape rho j. Actual normalized merge retains exact role data/heads and unchanged runtime; no free payload permutation is assumed.

- `Machine/PointwiseBinaryNormalized.lean`: Counted finite-symbol operations followed by real two-head rewind preserve exact pointwise arrays and return both payload heads; immutable count and clock restored, with explicit normalized runtime and encoded XOR semantics.

- `Machine/PointwiseRoleGate.lean`: Actual normalized XOR placed between arbitrary distinct fixed role tapes, sharing one preserved binary length descriptor and restored clock. Exact complete bank and all unrelated words/heads retained.

- `Machine/PointwiseRoleCircuit.lean`: Fixed list of physical role XOR gates composes with exact folded array semantics and charged gate/join runtime. The finite machine is selected independently of runtime stream length.

- `Machine/SparseRoleCircuit.lean`: Literal tape execution of existing SparseCircuit.copies lists equals their Circuit.run and pointwise sum semantics on encoded ZMod2 arrays, with normalized heads and linear-volume bounds.

- `Machine/OneSourceCircuit.lean`: Proof-carrying compiler retains actual scalar instruction lists certified as distinct-source XOR gates, supporting finite restriction/embedding/renaming and exact tape-level Circuit.run semantics.

- `Machine/Shared50XorLists.lean`: Symbolic certificates show the actual optimized DAG, sparse input/output/central lists, invocation/inverse/exchange and reused-world global program are distinct-source XOR lists without expanding enormous instruction sequences.

- `Machine/Shared50TapeInvocation.lean`: Actual optimized local sparse invocation and exchange compile into fixed tape machines with exact data-bank transformations and arbitrary dirty-scratch restoration, preserved heads/backgrounds and charged linear stream runtime.

- `Machine/Shared50TapeGlobal.lean`: Actual complete reused-world Shared50 XOR program exchanges its data banks and restores arbitrary scratch streams on one fixed machine, with explicit linear tape-transition bound from the certified gate count. Canonical stream-length descriptor supplied; framed address transforms and recursive scheduling remain separate.

- `Machine/FiniteFlow.lean`: Actual fixed finite block controller permits terminal-state-dependent cycles, back-edges and self-edges. Each real block trace yields an exact machine run with one charged tape-preserving transition per jump; states equal the fixed sum of block states, independent of runtime depth.

- `Machine/RecursiveInterchangeVolume.lean`: Along actual seven-factor child selections, proves exact row and logical-volume division by roleCount^depth, unchanged non-row volume, retained original chunk lower bound and power-width depth bound. Parked ancestors never enter logical child volume; physical recursive execution remains separate.

- `Machine/RecursiveDimensionBank.lean`: Actual 13-tape dimension arithmetic preserves six canonical seven-factor headers, computes Q and successive A*rows, A*rows*beforeH, and full H-prefix count from blank outputs and scratch. Exact canonical outputs and 258 times volume plus 87 bound; physical installation into the shift bank is separate.

- `Machine/RepeatedControlBootstrap.lean`: Actual 21-tape bootstrap constructs physical zero H and every repeated-control metadata marker from B/Q/C/N/width and payload. No precomputed offset or radix control is supplied; exact prepared output and 15 times width plus 30 cost. Dimension-bank installation remains separate.

- `Machine/DelimitedReverseCopy.lean`: Actual reverse copy scans non-delimiter data until a physical marker, preserving source and arbitrary outside regions with exact head and linear word-length contracts.

- `Machine/DescriptorStackControl.lean`: Literal descriptor-stack seek and control steps, with genuine markers and scans rather than unknown-length seek primitives.

- `Machine/BinaryDescriptorStack.lean`: Fixed eight-state push/pop store delimiter-framed reversed binary descriptors and restore original bit order. Each costs 2 times bit length plus 7, with exact source/stack frames and no supplied runtime length; empty descriptors supported.

- `Machine/BinaryDescriptorStackRoundtrip.lean`: Concrete three-tape push/pop preserves source and complete older stack/head, restoring the exact canonical descriptor on an initially blank destination in 4 times bit length plus 15. Representation matches RadixZeroFill headers.

- `Machine/RecursiveDescriptorSize.lean`: Actual child-selection paths bound recursion depth by log2 of logical child volume. Root-bounded canonical descriptor lengths are at most a fixed role-count-dependent multiple of child log-size, hence of child volume. This charges linear descriptor scans without counting parked ancestors; arbitrary polynomial descriptor algorithms and physical recursive execution are separate.

- `Machine/BinaryDescriptorInstallMarkedList.lean`: Fixed lists of physical marked binary-header copies preserve the source bank and charge all copies, markers and joins; runtime descriptor values never enter the transition table.

- `Machine/RecursiveShiftInstall.lean`: Five physical descriptor copies connect the generated recursive dimensions to a blank shift workspace, preserving original headers and payload.

- `Machine/RecursiveShiftInitialize.lean`: One fixed machine constructs all heterogeneous shift metadata from six canonical layout headers and payload, with exact prepared endpoint and linear-volume setup cost.

- `Machine/RecursiveInterchangeShiftConstruct.lean`: Complete 34-tape heterogeneous H-controlled D shift from six original headers and payload, with all private input blank. Exact seven-factor symbol transport and normalized payload cost 1288 times volume plus 186, including physical setup; generated metadata remains at output.

- `Machine/BinaryDescriptorStackAt.lean`: Places actual variable-length descriptor push/pop on any two distinct tape slots, preserving every other tape and charging exact runtime.

- `Machine/BinaryDescriptorFrames.lean`: Fixed lists of runtime binary headers push in order and pop in reverse with exact older-stack restoration. Actual same-bank roundtrip preserves source fields and writes initially blank distinct destinations, costing four times total bit length plus sixteen times field count plus one; programs are independent of descriptor lengths.

- `Machine/RecursiveInterchangeShiftClean.lean`: Clean reusable 68-tape heterogeneous controlled shift from six canonical layout headers and sole payload. Exact transformed array, retained original headers, all generated private metadata and trackers erased at head zero, with setup/execution/cleanup bound 221536 times volume plus 32370. Fixed machine independent of runtime layout.

- `Machine/Shared50OrderedPieces.lean`: Actual fixed clean machines for certified nonrecursive segments and globally wired scalar XOR gates from the ordered control. Segment semantics use equal-width coordinates; heterogeneous header construction, whole-bank joining and recursive continuations remain separate.

- `Machine/Shared50PieceSchedule.lean`: Fixed actual list of certified segments, explicit role-and-coordinate recursive calls, and scalar gates. Expansion equals the original control atom by atom, with exact improved recursive-call count. Whole-machine compilation remains separate.

- `Machine/RecursiveHeaderBounds.lean`: Every actual six-field recursive header is bounded by its layout volume and the original root volume. Canonical active or saved-ancestor headers therefore satisfy the child-volume scan bound without a separate descriptor-size assumption; parked ancestor storage is excluded.

- `Machine/FiniteReturnStackAt.lean`: Places real binary PC push and decoded dispatch on one selected tape while framing all other tapes. Exact dispatch retains the finite terminal-state result for controller composition.

- `Machine/RecursiveFrameControl.lean`: Concrete static call/body/return assembly physically saves descriptor fields and PC, restores fields, pops PC and dispatches to the decoded continuation. Exact tape and terminal-state contracts charge every join. The supplied body must establish intact saved stacks and blank restoration destinations; recursive child execution remains an explicit obligation.

- `Machine/BinaryDescriptorCleanupList.lean`: Fixed physical list of marked binary-header erasures. Every bit and marker is erased, heads return to zero and all other tapes are framed; exact cost two times total bit length plus five times field count. No runtime length enters control.

- `Machine/BinaryDescriptorFrameRestore.lean`: Actual cleanup followed by descriptor-frame pop accepts nonblank child headers, physically erases them and restores saved ancestor headers in the same slots. Exact older stack/head and spectator preservation, with cleanup, joining and pop costs explicit.

- `Machine/RecursiveHeaderRestore.lean`: Actual parent-header restoration costs at most (fieldCount*(8*(log2 roles+2)+13)+1) times logical child volume. Canonical old/current layout headers and paths discharge size assumptions; six-field bound is (48*(log2 roles+2)+79) times child volume. No free header reset.

- `Machine/RecursiveDescriptorDivision.lean`: Bounds the actual five-tape binary long-division runtime by (40*(log2 roles+2)^2+54*(log2 roles+2)) times logical child volume for canonical root-bounded input descriptors. Proves the quadratic logarithm estimate and retains exact shifted remainder/quotient output banks; canonical output normalization and caller integration remain separate.

- `Machine/RecursiveScalingDimensions.lean`: Physical 16-tape construction of heterogeneous scaling dimensions from six canonical layout headers, including required suffix or prefix products for H or D. Exact outputs, preserved headers and 364 times volume plus 145 setup cost.

- `Machine/RecursiveScalingInstall.lean`: Fixed physical marked-header installation and scaling workspace setup connects synthesized dimensions to the normalized scaler; exact canonical metadata and framed payload, with every copy and join charged.

- `Machine/RecursiveInterchangeScalingConstruct.lean`: Complete initialized H/D scaling from six original headers and payload with blank private input. Physical dimensions, installation, arithmetic and normalization give exact spectator-preserving array transport and an explicit coefficient-dependent linear-volume bound.

- `Machine/RecursiveInterchangeScalingClean.lean`: Clean reusable heterogeneous H/D scaling retains six original headers and normalized payload pair, erasing all generated metadata and trackers at head zero. Exact canonical bank independent of H/D selection and explicit setup/execution/cleanup linear-volume bound; coefficient and tape count are fixed independently of runtime layout.

- `Machine/CleanSubbank.lean`: Fixed injective placement executes a clean local machine on selected permanent tapes with blank private storage. Exact input/output payload agreement and spectator framing imply the unchanged runtime contract for the whole bank; no implicit copies or head resets.

- `Machine/CleanSubbankCompile.lean`: Finite physical composition of clean permanent-bank stages returns literal blank private input/output and charges every joining transition. Works for arbitrary permanent banks and heterogeneous layouts, with actual stage contracts supplied.

- `Machine/RecursiveShiftRoleBank.lean`: One layout-independent machine shifts a selected permanent role in any positive seven-factor layout. Shared six canonical headers, all other roles and arbitrary auxiliary tapes are preserved, private work is blank again, and exact symbol transport costs 221536 times volume plus 32370. Header updates are separate.

- `Machine/RecursiveCleanReturn.lean`: Actual header cleanup, saved-descriptor restoration and binary PC pop/dispatch composed into one return routine, with exact selected continuation terminal state. Conditional body interface allows nonblank child headers and charges all erasure and joins; recursive body implementation remains open.

- `Machine/DigitInterchangeRows.lean`: Literal serialization for width-one interchange: the first cyclic split role word equals the second split input, and transposing fixed radix-role indices gives exactly the transposed leaf words while preserving arbitrary outer, middle and suffix fields.

- `Machine/DigitInterchangePasses.lean`: Actual normalized tape contracts for both split and both merge levels of single-digit interchange. Input/output words match literally, heads and descriptors are restored, and the total pass cost including joins is at most (597+2*q) times volume. Whole-bank joining, counter synthesis and private cleanup remain separate.

- `Machine/BinaryCanonicalTrim.lean`: Actual backward erasure of high zero bits in a marked binary word followed by origin reset. Four states, exact canonical value-preserving output at head one, including empty and all-zero words.

- `Machine/BinaryQuotientNormalize.lean`: Nine-state two-tape erase-copy, zero trim and rewind normalizes a raw division quotient in two times its length plus eight transitions. Raw source is wholly blank at head zero; destination is canonical at head one.

- `Machine/RecursiveChildDimensions.lean`: Nineteen-tape physical construction of child layout powers and products from six parent headers plus explicit canonical divided-width and divided-row headers. Eight real arithmetic stages emit exact six child headers with bound (48*(m-1)+512) times child volume plus 119; no derived product oracle.

- `Machine/RecursiveChildDimensionsClean.lean`: Thirty-eight-tape clean child-header constructor retains parent and quotient headers plus required child products, erasing all intermediate powers, scratch and trackers. Exact canonical child descriptor, volume division and bound 97*(48*(m-1)+512) times child volume plus 11756. Quotient production and child-bank installation remain separate.

- `Machine/BinaryDescriptorDivisionRaw.lean`: Physical raw division and quotient normalization at cell-one origins, exposing exact shifted remainder and retained dividend/divisor banks for boundary setup and cleanup.

- `Machine/BinaryDescriptorDivisionBoundary.lean`: Actual marked-input preparation, dividend scan, division invocation and marker restoration. Every seek and boundary operation is charged; supplies fixed zero/one input heads for physical workspace tracking.

- `Machine/BinaryDescriptorDivision.lean`: Complete fixed 12-tape marked binary division from two input headers and blank workspace. Inputs preserved, canonical quotient returned at head one, and all nine other private tapes physically erased at head zero, including shifted remainder. No free input setup, quotient normalization or cleanup.

- `Machine/BinaryDescriptorReplaceList.lean`: Fixed physical replacement of occupied binary-header slots: erase old marked words, install new words from disjoint sources, preserve all other tapes. Exact bank theorem and fieldCount*(4*maxWidth+11)+1 runtime include every erased bit, copy and join.

- `Machine/RecursiveChildHeaderInstall.lean`: Fixed five-header replacement in the actual child-constructor bank, retaining A in place. Generated-output source and destination conditions are discharged; exact installed child words and (40*(log2 roles+2)+56) times child-volume bound. Parent values must be saved before destructive installation; duplicate source cleanup and full caller composition remain separate.

- `Machine/RecursiveScalingRoleBank.lean`: Layout-independent physical H/D scaling of a selected role on the same permanent bank used by recursive shifts. Retains six headers, other roles, arbitrary auxiliary data and clean private storage; exact array transport and coefficient-dependent linear-volume cost.

- `Machine/RecursiveXorRoleBank.lean`: Actual selected-role XOR on the permanent recursive bank, preserving all headers, spectators and supplied length/clock control. Exact binary addition and 14 times volume plus 14 times descriptor length plus 33 runtime; length synthesis is separate.

- `Machine/RecursiveRoleSerialization.lean`: Exact equality between canonical four-symbol shift/scaling payload words and the pointwise XOR bit-stream encoding. Mixed operations need no uncharged representation conversion.

- `Machine/RecursiveMixedSchedule.lean`: One runtime-independent fixed mixed shift/scaling/XOR program on a shared permanent bank. Exact whole-block semantics, literal blank private input/output and sum-of-stage-costs plus charged joins; explicit compile-time linear-volume coefficient. Uses one unchanged six-header view and a supplied short stream-length descriptor; paid coordinate regrouping and recursive calls remain separate.

- `Machine/RecursiveChildQuotientsConstant.lean`: Fixed compile-time divisor word is physically initialized with marker and head restoration, charging three times bit length plus six transitions. Its logarithmic binary construction is proved equal to the former increment-generated canonical word, avoiding unary expansion of large fixed constants.

- `Machine/RecursiveChildQuotients.lean`: Two clean divisions plus actual fixed-divisor initialization/erasure generate width/m and rows/roles from six parent headers. Exact 38-tape output matches the child-dimension constructor input, with no supplied divisor or quotient words.

- `Machine/RecursiveChildQuotientsBound.lean`: The actual paired quotient computation has linear logical-child-volume cost, absorbing fixed divisor lengths into its constant without assuming divisors are root-volume bounded.

- `Machine/RecursiveChildHeaderHandoff.lean`: Physically installs generated child headers and erases temporary quotient/product copies. Exact final standard six-header bank, every other tape blank at zero; bound30 times maximum header length plus82. Composes directly with dimension generation.

- `Machine/RecursiveChildPrepare.lean`: One fixed 38-tape machine starts with only six canonical parent headers and ends with only the actual six canonical child headers. Divisors, quotients, powers, products, occupied-header replacement, copy erasure and joins are all physical and charged to logical child volume. Saving parent headers and array/recursive control remain caller operations.

- `Machine/DigitInterchangeBank.lean`: One fixed bank for width-one interchange with source, role streams, radix-pair leaf streams, merge streams, clocks and four supplied counters. Exact per-pass placements and spectator preservation support the whole-bank sequence.

- `Machine/DigitInterchangeCompile.lean`: Actual same-bank sequence of two outer passes and twice-radix inner passes transposes the digit fields and overwrites the original source. Exact intermediate serialization and head restoration; cost at most (597+2*q) times volume including joins.

- `Machine/DigitInterchangeClean.lean`: Physically initializes loop markers, executes the entire single-digit interchange, then erases all temporary streams, clocks and trackers. Same canonical source/scratch bank with four retained descriptors, exact transposed payload and explicit linear-volume cost. Counter synthesis from six recursive headers remains separate.

- `Machine/RecursiveVolumeConstruct.lean`: Fixed 295-state machine physically computes full stream volume from six canonical layout headers and initializes the XOR clock. Exact canonical product and retained headers, with417 times volume plus176 setup cost.

- `Machine/RecursiveVolumeClean.lean`: Clean 34-tape volume/clock constructor retains only six original headers and the two generated controls. Every private tape and tracker blank at zero; bound36279 times volume plus15503, hence51782 times positive volume. Canonical generated word has bit length at most volume.

- `Machine/RecursiveVolumeRoleBank.lean`: Physical volume/clock initialization on the permanent recursive role bank, starting with both control tapes blank. Every role and arbitrary auxiliary tape is preserved; exact prepared endpoint and private cleanup.

- `Machine/SharedBankRawCompose.lean`: Actual fixed-skeleton composition with changing leading common banks and blank private endpoints. Proves exact input/output bank and sum of runtimes plus one joining transition, independent of semantic-stage packaging.

- `Machine/RecursiveMixedInitialized.lean`: One fixed machine initializes its own XOR clock and volume word from six canonical headers, then executes the actual mixed shift/scaling/XOR list. Exact role-array semantics and clean private endpoint, bound(51783+sum operation coefficients+operation count) times volume. Generated controls remain explicit at output; per-operation coordinate-view changes and recursive calls remain separate.

- `Machine/RecursiveChildCallSetup.lean`: Actual fixed 40-tape call entry saves six parent headers and compile-time return PC, then physically computes/installs child headers. Both saved stacks survive complete arithmetic. Exact child bank and coefficient RecursiveChildPrepare.constant+24*(log2 roles+2)+50+PCwidth times child volume; array parking and recursive body remain separate.

- `Machine/RoleArrayStackMoves.lean`: Physical counted role-array head movement and control-marker setup/erasure used by destructive parking and recovery. Arbitrary payload symbols and exact whole-bank endpoints; no delimiter-based payload scan.

- `Machine/RoleArrayStack.lean`: Actual destructive role-array push with source reset to blank/head zero and inverse pop restoring source and older stack exactly. Work clock initialized and erased physically; push14*N+14*bitLength+45, pop14*N+14*bitLength+49.

- `Machine/RoleArrayStackAt.lean`: Injective placement of the actual four-tape role-array push/pop routines into a fixed larger bank with exact spectator framing.

- `Machine/RoleArrayFrames.lean`: Fixed-list inactive role parking and reverse recovery, independent of runtime lengths. Every vacated role/work clock becomes blank/head zero; exact older stack and original roles recovered with allocated-interval blank precondition. Canonical positive volume gives88*count*N push,92*count*N pop, and(180*count+1)*N actual roundtrip.

- `Machine/RecursiveDigitLayout.lean`: Width-one recursive array view with exact full row-major serialization and digit-transpose address semantics, preserving every outer/middle/suffix spectator for arbitrary native alphabet payloads.

- `Machine/RecursiveDigitDimensions.lean`: Physical construction of all four base-case counters from six recursive layout headers: scaling suffix products plus a real outer-times-middle product. No derived counter inputs;417 times volume plus174 setup cost.

- `Machine/RecursiveDigitInstall.lean`: Four actual marked copies install generated dimensions into the single-digit interchange bank, preserving original headers and payload and charging every copy and join.

- `Machine/RecursiveDigitInterchangeConstruct.lean`: Complete width-one interchange from six original headers and sole array. Physically constructs/install counters, initializes loop markers, executes the whole-bank interchange and returns exact transposed source; explicit setup-inclusive linear-volume bound.

- `Machine/RecursiveDigitInterchangeClean.lean`: Fully initialized clean recursive base case: sole six canonical headers and array, width one, fixed q-dependent program. Exact digit-swapped array on original source with blank scratch, original headers retained, every private tape/tracker erased at zero, and explicit full linear-volume bound.

- `Machine/RoleArrayMove.lean`: Physical destructive arbitrary-symbol transfer into a blank origin tape, with source and reusable clock erased and both heads reset. Exact spectator preservation; canonical positive count gives87*N runtime.

- `Machine/RoleArrayCall.lean`: Actual inactive-role parking, active-role move into common child source, explicitly framed child execution, move back and reverse recovery. Exact whole-bank result changes only the active array under the child contract; overhead(180*roleCount+178)*N, including every join.

- `Machine/RecursiveAffineViews.lean`: Within-H, within-D and cross coordinate views preserve exact index/volume identities and literal serialized payload words.

- `Machine/RecursiveAffineDimensions.lean`: Actual four-power/four-product constructor for within-group coordinate-view headers, with all seven joins charged.

- `Machine/RecursiveAffineDimensionsBound.lean`: Every generated power and product is bounded by unchanged stream volume; physical constructor costs at most(96*m+512)*V+119.

- `Machine/RecursiveAffineDimensionsClean.lean`: Fixed output relabelling aligns generated view headers with handoff ports; physical tracked cleanup erases all private intermediates.

- `Machine/RecursiveAffinePrepare.lean`: Complete within-group view preparation from sole six canonical headers: quotient synthesis, powers/products, occupied-header replacement and source erasure, with linear unchanged-volume cost.

- `Machine/RecursiveCrossPrepare.lean`: Complete cross-group view preparation on canonical38-tape bank with preserved row count and linear volume cost, requiring no root-path hypotheses.

- `Machine/RecursiveViewRoleBank.lean`: Fixed cross/within selector places paid view changes on permanent roles/scratch/header/aux bank; exact preservation of every payload and auxiliary, all private tapes blank. Parent header save/restore and scalar semantic composition remain separate.

- `Machine/RecursiveRowsQuotient.lean`: Real constant-role initialization and clean marked division compute canonical rows/roles from parent headers. Fixed38-tape bank, preserved six headers and explicit linear parent-volume cost.

- `Machine/RecursiveRowsDimensions.lean`: Actual quotient, scaling products and row/group products construct normalized cyclic-transfer descriptors from sole six parent headers. Exact generated values, canonicality, header preservation and linear volume bound; installation, source erasure and transfer assembly remain separate.

- `Machine/RecursiveWidthGuard.lean`: Physical four-state width-one test preserves the exact bank in at most two transitions; canonical descriptor value selects actual base/recurse terminal state for finite-flow dispatch.

- `Machine/RecursiveStackAllocation.lean`: Blank suffix invariants discharge descriptor, PC and role-array free-interval premises. Actual pushes and child payload entry preserve availability at the advanced stack head; concrete saved header/PC stacks retain both free suffixes, without a recursion-depth capacity assumption.

- `Machine/RecursiveDigitRoleBank.lean`: Places the fully initialized clean digit interchange at one permanent role, with canonical six headers, exact Fin4 serialization, all spectator roles/auxiliaries preserved and complete private cleanup. Symbolic port proofs and explicit linear-volume cost.

- `Machine/RecursiveViewFrame.lean`: Fixed six-header push and occupied-header cleanup/pop on a dedicated stack, exact older-stack preservation, explicit free interval and runtime bounds independent of word lengths in control.

- `Machine/RecursiveViewFrameRoleBank.lean`: Places real six-header save/restore on the permanent role bank with a dedicated stack and clean private workspace, retaining all payloads and auxiliary tapes exactly.

- `Machine/RecursiveViewedAction.lean`: One fixed physical push/view/shift-or-scale/restore composition returns parent headers, dedicated stack and private work exactly, retaining auxiliaries and producing the transformed array in its parent-volume type. Linear coefficient is view cost plus action cost plus202; matching ordered scalar descriptions remains separate.

- `Machine/CountedBankReset.lean`: Actual simultaneous counted erasure and rewind of selected arbitrary-symbol tapes, preserving spectators and physically restoring heads; descriptor-sensitive and linear runtime bounds.

- `Machine/CountedBankResetHeader.lean`: Initializes counted bank reset from a canonical count header and two blank work tapes, including descriptor copy and clock setup with every transition charged.

- `Machine/RecursiveRowsInstall.lean`: Physically copies generated row/group headers and initializes both loop clocks for the normalized cyclic transfer bank.

- `Machine/RecursiveRowsConstruct.lean`: Composes quotient/product construction, descriptor installation and normalized split/permuted merge from sole six parent headers, with exact intermediate banks and charged setup.

- `Machine/RecursiveRowsResetCount.lean`: Physically computes common or role volume from generated row dimensions for counted payload erasure.

- `Machine/RecursiveRowsMove.lean`: Actual initialized cyclic split erases the copied common source; actual permuted merge erases every consumed role source. No supplied derived counters or free resets.

- `Machine/RecursiveRowsClean.lean`: Complete tracked workspace cleanup after initialized destructive split/merge. Same reusable bank with original six headers and output payloads, all private tapes blank and heads restored; explicit linear parent-volume cost.

- `Machine/RecursiveRowsRoleBank.lean`: Fixed injective placement of clean initialized split/permuted merge on permanent roles/scratch/six-header/auxiliary bank. Deterministic updated role payloads, exact spectators, blank consumed sources and private workspace; native arbitrary alphabet.

- `Machine/RoleArrayCallBoundary.lean`: Separate fixed physical entry park/move and return move/recover blocks expose exact entered banks without embedding a child program. Entry(88*roleCount+88)*V and return(92*roleCount+88)*V, including joins, support cyclic control edges.

- `Machine/RecursiveChildSetupRoleBank.lean`: Places actual40-tape header/PC save and child preparation on permanent role bank with fixed two-stack auxiliary suffix, preserving payloads and other auxiliaries with blank private workspace. Generic placed_hoare also lifts exact header/stack return contracts.

- `Machine/RecursiveRowsSerialization.lean`: Exact Fin4 parent-array to cyclic child-role serialization and inverse permuted merge on the permanent shared bank, inheriting the physical clean-transfer runtime. Deterministic data banks supply all frame equalities; spectator child-layout casts preserve literal tape words with parent headers retained until physical child setup.

- `Machine/SharedBankFamily.lean`: Pads a finite family of clean leading-bank machines to one fixed sum-bounded tape count, preserving each state count, every common slot, exact blank private endpoints and original runtime. No tape movement or runtime dimension enters the workspace bound.

- `Machine/Shared50RecursiveControl.lean`: Fixed finite graph over the exact Shared50 piece list: physical width guard, split/body/merge nodes, shared header restoration and real PC pop, per-call entry/recovery nodes, and a root halt sentinel. Actual call-site codes decode to their recovery nodes; root header/PC initialization is physically charged. Different fixed private banks are padded to one finite-family tape count; block implementations and recursive execution remain explicit obligations.

- `Machine/RecursiveCoordinateDigits.lean`: Exact one-field and ordered control/target decompositions of the existing MSB-first rank encoding, with literal coordinate-update identities.

- `Machine/RecursiveScalarSelection.lean`: Static compiler maps actual ordered scalar descriptions to within-H, within-D or cross paid views and exact rational shift/scaling operations, preserving reflected subtraction order.

- `Machine/RecursiveScalarCoordinates.lean`: Selected-view typed indices equal original heterogeneous positions exactly; writes to exposed H/D coordinates are writes to the original numbered fields.

- `Machine/RecursiveScalarTransport.lean`: Paid view/action/restore arrays implement the original scalar instruction on original field coordinates, preserving every other role; compile_entry and compile_other bridge actual scalar descriptions.

- `Machine/RecursiveScalarSchedule.lean`: Finite physical composition of paid varying-view scalar wrappers restores parent headers, dedicated stack and auxiliaries between stages, with exact ordered semantics and a fixed linear-volume coefficient.

- `Machine/Shared50RecursiveSegments.lean`: Instantiates every actual Shared50OrderedPieces.Segment on its original wire. Clean permanent-bank output implements exactly original AffineFieldProgram.run on heterogeneous coordinates, preserves all other roles, and costs coefficient times volume. Applicable to row-reduced role descriptors without another row division.

- `Machine/RecursiveRoleChildCallSetup.lean`: Correct recursive network call entry saves already-row-reduced parent headers and return PC, then physically installs a cross child view with divisor1. Rows remain unchanged, avoiding double division. Same permanent-bank placement; setup and matching occupied-header return have path-free linear role-volume bounds.

- `Machine/RecursiveChildCallReturn.lean`: Accepts the exact bank and savedStacks generated by actual child entry, physically erases occupied child headers and restores parent headers while retaining the pending PC frame. Exact bank compatibility, with free descriptor stack supplied by its blank-suffix invariant.

- `Machine/RecursiveChildReturnRoleBank.lean`: Places header restoration on the permanent bank independently or before actual PC pop/decode/continuation execution. Exact final continuation state survives both compositions; original roles/auxiliaries and older stacks restored. Same-root path bound is(48*(log2 roles+2)+PCwidth+82)*childVolume plus continuation cost.

- `Machine/SharedBankFamilyExact.lean`: Uniform private workspace padding preserves exact execution lengths, terminal finite states and halted configurations; finite-family members retain both bank and control endpoints.

- `Machine/Shared50RecursiveExecution.lean`: The actual uniformly padded cyclic width guard preserves the complete bank and selects the base or split block in at most three transitions, including its real finite-flow edge. Recursive body execution remains open.

- `Machine/RecursiveRowsNodeLayout.lean`: Splitting once and then creating a divisor-one child equals the original child layout; reduced-row descriptors retain positivity under divisibility.

- `Machine/RecursiveRowsNodeHeaders.lean`: Physically installs the quotient row header, erases its temporary source, and preserves the other five headers, with canonical reduced-row values and a linear-volume bound.

- `Machine/RecursiveRowsNodeRoleBank.lean`: Places paid reduced-row header construction on the permanent role bank with exact payload and auxiliary preservation and blank private workspace.

- `Machine/RecursiveRowsNode.lean`: Actual node entry saves six original headers, splits rows and installs reduced headers; exit restores occupied headers and performs permuted merge. Exact banks, linear-volume costs and nested descriptor-stack availability are proved; network execution remains separate.

- `Machine/Shared50RecursiveReturnExecution.lean`: Actual placed and uniformly padded PC pop erases the encoded frame, restores the older stack and preserves every spectator tape. Its real finite-flow jump selects the encoded recovery or root halt node in exactly k+2 transitions, retaining decoded control states throughout.

- `Machine/RecursiveCallCount.lean`: Physically generates the role volume from six canonical headers on fixed private workspace, retaining a blank loop clock and preserving all other common tapes; exact count erasure restores its slot.

- `Machine/RecursiveCountedCallBoundary.lean`: Separate payload entry and recovery machines construct their own volume count, park or recover role arrays, and erase the count. Clock and count are blank at recursive boundaries; all setup and cleanup are charged linearly in volume.

- `Machine/RecursiveCallBank.lean`: Permanent bank places role payloads, scratch, six headers, clock/count/payload stack, auxiliary spectators and descriptor/PC stacks in fixed slots; actual payload entry preserves this layout.

- `Machine/RecursiveCallProtocol.lean`: Actual child entry composes initialized payload parking/movement with same-row header and PC setup. Recovery regenerates the restored parent volume, retrieves payloads and clears controls. Exact banks and linear role-volume costs are proved; matching child execution to the recovery input and global auxiliary placement remain separate.

- `Machine/RecursiveMixedClean.lean`: Physically erases the generated mixed-operation clock and volume descriptor after execution, retaining exact original headers, payloads and auxiliaries with all private work blank; linear-volume bound includes cleanup.

- `Machine/RecursiveMixedRoleBank.lean`: Places complete initialized and cleaned mixed operations on permanent role/header banks, preserving arbitrary saved stacks and other auxiliaries without supplying any XOR controls.

- `Machine/Shared50RecursiveGates.lean`: Every literal Shared50 scalar gate has an actual fixed tape machine with complete setup/cleanup and exact original module-gate semantics on arbitrary encoded bit streams, including dirty scratch. Cost is at most 51858 times logical volume.

- `Machine/Shared50NodeSegments.lean`: Original paid nonrecursive segments run on unchanged World role indices plus a final common input/output tape. Exact field-coordinate semantics and IO preservation with fixed linear-volume costs.

- `Machine/Shared50NodeGates.lean`: Literal gates on the complete node payload bank preserve common IO and arbitrary stacks; original binary module-gate semantics, exact whole-bank endpoints and fully charged linear-volume execution.

- `Machine/Shared50RecursiveNodeLayout.lean`: Original World enumeration remains in its existing role slots, with common IO last; role count equals W and physical merge permutation is the conjugated involutive original route.

- `Machine/Shared50RecursiveNodeRows.lean`: Cyclic split and permuted merge match the exact parent H/D transpose through row and suffix packing, including within-role address swapping.

- `Machine/Shared50RecursiveNodeSemantics.lean`: Full fixed Shared50 control on binary cyclic fibers yields exactly the permuted merge input; actual node exit restores original headers and merges to parent transpose. Actual piece execution equivalence remains separate.

- `Machine/Shared50RecursiveNodeTranspose.lean`: Quotient/remainder decomposition covers every original row; transpose semantics hold at every seven-factor and complete scalar-coordinate address.

- `Machine/Shared50RecursiveNodeBinary.lean`: Actual split and fixed-control output arrays equal the node gate binary encodings with blank common IO. Flat cyclic serialization agrees with scalar-coordinate routed transpose, providing the binary induction bridge.

- `Machine/Shared50RecursiveBank.lean`: Fixed tape permutations align local common banks with the call bank without moving data or adding transitions. Distinct clock, count, payload, node-view, scalar-view, descriptor and PC slots; exact endpoint reconstruction and return-stack placement.

- `Machine/Shared50RecursiveBankNodes.lean`: Actual split/merge, scalar-segment and gate skeletons execute on the single call-compatible permanent bank. Saved node frames and blank scalar-view stacks are distinct; exact bank endpoints and original runtime costs are retained.

- `Machine/Shared50RecursiveBankReturn.lean`: Actual base interchange and ancestor-header restoration share the global bank. Exact payload/header/stack endpoints, linear role-volume return cost and literal pending-PC reset match the physical decoder.

- `Machine/Shared50PieceSemantics.lean`: The actual segment/call/gate piece list expands exactly to the original fixed interleaved control; its full routed H/D transpose semantics follow in original execution order.

- `Machine/Shared50NodePieceTransport.lean`: Actual segment/gate array folds match original scalar-coordinate fibers, preserve IO, and give routed transpose conditional on the exact selected-coordinate child interchange contract. No physical child execution is supplied by this theorem.

- `Machine/Shared50RecursiveCallLayout.lean`: Fixed parking order includes exactly the original World roles except the active stream, excludes the separate IO tape and is duplicate-free. Used by actual controller call entry/recovery.

- `Machine/Shared50RecursiveImplementation.lean`: Instantiates every Shared50 controller block with actual global-bank machines: base, node split/merge, return restoration, segments, gates and fixed-order child entry/recovery. One compile-time PC capacity, actual root header/sentinel setup and fixed cyclic graph; no runtime width/depth or supplied block implementation is a program parameter. Total recursive correctness and runtime recurrence remain unproved.

- `Machine/Shared50RecursiveBlockExecution.lean`: Clean physical block contracts lift to exact runs of the padded cyclic machine and its real next-table edge, with full bank endpoints and at most one additional transition. These trace rules support assembly; recursive traces remain to prove.

- `Machine/RecursiveScalarIndex.lean`: Every flat payload cell has an original heterogeneous scalar-coordinate address, for general field count and digit width; no fiber or row is omitted.

- `Machine/Shared50RecursiveNodeBoundary.lean`: Binary node entry yields the exact encoded World split bank and saved-stack availability; binary exit consumes encoded routed output and restores the parent transpose with symbolic linear-volume bounds.

- `Machine/Shared50RecursiveNodePieces.lean`: Actual segment/gate/child array fold equals the exact node networkData on every cell, assuming only the explicit selected-coordinate ChildSpec. Physical exit accepts this fold output and returns parent transpose. Establishing ChildSpec from actual recursive machine execution remains open.

- `Machine/Shared50RecursiveRoot.lean`: Actual root header/sentinel initialization equals the existing savedStacks call frame on the global bank. Charged setup, preserved free suffixes and linear-volume setup bound; its root composition rule still requires the graph body.

- `Machine/Shared50RecursiveBaseExecution.lean`: Complete width-one execution of the actual fixed root program: root frame setup, guard, digit interchange, occupied-header restoration, real PC decode/return edge and final halt. Exact transformed stream, all spectator banks/stacks restored and fixed-coefficient linear logical-volume runtime; recursive widths remain open.

- `Machine/Shared50RecursiveCallSemantics.lean`: Actual parking/movement leaves all original World work tapes blank and the active word on common IO; header setup has the exact canonical child bank. Source replacement commutes with entry into IO replacement, array support is derived, and the payload stack preserves an unbounded blank suffix.

- `Machine/Shared50RecursiveCallRecovery.lean`: Actual initialized count/move/reverse-parking/cleanup recovery consumes the returned IO word and restores precisely the parent array with one selected World stream updated. Source support and free intervals follow from canonical arrays and blank suffix; binary child outputs preserve all World bit encodings.

- `Machine/Shared50RecursiveChildPermutation.lean`: Full transpose of the actual cross-child layout equals exactly the selected parent H_i/D_j swap. Literal serialized input/return words match, spectators are preserved, and binary selected-coordinate ChildSpec follows, independently of row-split divisor.

- `Machine/Shared50RecursiveDepth.lean`: Positive power-width descriptors with W^depth dividing rows remain valid after exactly one split and divisor-one child preparation. Child width/depth decrease, exact parent volume/W and old/current header bounds are proved.

- `Machine/Shared50RecursiveBinaryInvariant.lean`: Binary World arrays and blank common IO are preserved by every actual piece array operation and literal schedule, using the exact selected child contract and coverage of every flat coordinate. Dirty work roles may hold arbitrary bits.

- `Machine/Shared50RecursiveCallReady.lean`: Actual call entry constructs child headers and canonical binary source bank, preserving available payload/node/descriptor/PC stack suffixes and blank scalar-view workspace. All child induction input invariants follow from parent readiness and physical entry.

- `Machine/Shared50RecursivePieceExecution.lean`: Actual segment/gate graph transitions and call entry-child-return-recovery composition execute every remaining literal schedule piece. Binary invariant-aware suffix induction charges all graph edges, exact s child calls and fixed linear logical-volume overhead; each recursive child trace remains the induction premise.

- `Machine/Shared50RecursiveBasePermutation.lean`: Width-one digit interchange equals full parent H/D transpose at every flat cell, and canonical source-bank IO updates match the exact recursive output serialization.

- `Machine/Shared50RecursiveBudget.lean`: Natural-valued recursion budget charges fixed base/node work and exactly s child budgets at logical volume parent/W. Occupied-header cleanup/return costs are bounded from actual word lengths; proving execution meets the recursive budget remains separate.

- `Machine/Shared50RecursiveInductionBase.lean`: The actual fixed graph executes canonical binary width-one input to the complete transpose and decoded caller address, preserving all stacks/spectators and meeting the same logical-volume budget used by the recursive induction.

- `Machine/Shared50RecursiveNodeExecution.lean`: Actual graph guard, physical node split, literal binary schedule, permuted merge, ancestor-header restoration and decoded return compose with exact canonical transpose output and fully charged runtime. Only the actual recursive child traces remain premises for depth induction.

- `Machine/Shared50RecursiveBudgetBound.lean`: The concrete natural-valued budget is bounded uniformly by logical volume times width to the certified exponent 1−296/10^11, including natural floor division and all fixed coefficients. This proves the analytic bound without assuming a runtime recurrence; actual recursive execution must still meet the budget.

- `Machine/Shared50RecursiveBudgetAssembly.lean`: Symbolic arithmetic absorbs all actual node controller joins, header-return costs and literal-schedule overhead into the natural recursive budget, using only positive logical volume and reduced role volume bounded by parent volume. Raw fixed coefficients avoid expanding enormous closed constants during proof checking.

- `Machine/Shared50RecursiveCallInductionBridge.lean`: Canonical binary child input and full-transpose return banks equal the actual parked call and recovery endpoints. Exact payload/node/descriptor/PC readiness bridges permit recursive induction without an assumed child trace.

- `Machine/Shared50RecursiveInduction.lean`: Depth induction proves actual fixed cyclic graph termination, exact binary full-chunk transpose, physically decoded caller return, all restored bank/stack endpoints and the natural recursive runtime budget. Every literal child trace is derived from the induction hypothesis; no abstract execution oracle remains.

- `Machine/Shared50RecursiveRootExecution.lean`: One concrete fixed root program physically sets up its sentinel and headers, executes the proved recursion, restores all stacks/spectators and genuinely halts with exact binary chunk transpose. Its actual steps obey one uniform positive constant times logical volume times width to exponent 1−296/10^11, for power widths and recursively divisible rows.

- `Machine/ArbitraryWidthPieceBudget.lean`: The sum of the completed fixed root machine budgets over the literal base-125000 piece list obeys one uniform positive constant times logical volume times full width to the certified exponent. This proves the actual call-budget sum; physical wrapper preparation, padding and tape composition must still be charged.

- `Machine/ArbitraryWidthPieces.lean`: The literal base-125000 power-piece list covers every chunk width, with certified depth/count/offset bounds. Consecutive piece swaps compose to the exact numerical full-address swap; each slice descriptor preserves total logical volume and satisfies the proved power-width Shape on common divisible rows. Its finite cost sum equals the manuscript digit-weighted sum. Physical padding and paid slice/list construction remain separate.

- `Machine/ArbitraryWidthSliceTranspose.lean`: Literal slice descriptors and serialized words implement exactly the selected MSB digit-window exchange, preserving all original seven-factor spectators and binary encodings. Generic interval-rank decomposition handles arbitrary offsets and lengths. This supplies the semantic interface for calls to the completed power-width machine; paid view construction remains open.

- `Machine/RecursiveRowPadding.lean`: Flat prefix/row/suffix zero extension and cropping are exact inverses on retained rows and commute with arbitrary within-row permutations. The original descriptor chunk transpose is exactly such a permutation, so padding/interchange/cropping yields the full original transpose. Padded logical volume is bounded by the row enlargement factor. Physical movement and generated controls remain separate.

- `Machine/BoundedProductDescriptor.lean`: One fixed forty-state six-tape machine generates a canonical binary product from bounded possibly noncanonical outer counts. All workspace markers are physically initialized and erased; original inputs remain exact and cost is at most 53 times the bounded product plus 28.

- `Machine/RowPaddingSpanCounts.lean`: One fixed nine-tape machine preserves canonical row, padded-row and suffix-length inputs and actually constructs canonical valid-span R*L and zero-padding-span (R′−R)*L, erasing subtraction and arithmetic scratch completely. Runtime is at most 112*(R′*L)+83; constructing the rounded row count R′ itself is separate.

- `Machine/CountedRawFill.lean`: Actual delimiter-free filling of an exact finite interval from an immutable binary span descriptor. Every data write, countdown setup and clock reset is charged; surrounding cells and supplied descriptor remain exact.

- `Machine/CountedRawMove.lean`: Actual delimiter-free destructive word transfer with source erasure from an immutable binary span descriptor. Exact arbitrary-symbol output, surrounding-cell preservation and all paid countdown/clock cleanup; data heads advance by precisely the span.

- `Machine/CountedPairPosition.lean`: Fixed counted motion of two payload heads with exact whole-tape preservation, reusable supplied span descriptor and charged clock preparation/reset. Supports restoring both row-padding payload origins.

- `Machine/RowPaddingBlock.lean`: Physical valid-span transfer followed by binary-zero padding, and inverse valid-span transfer plus physical padding erasure. Original span descriptors are retained and every primitive/join is paid.

- `Machine/RowPaddingStream.lean`: Actual counted prefix loop streams every original row group to its zero-padded group, or physically crops and erases padded groups. Exact flattened words and supplied span/prefix controls, with all group-loop work charged.

- `Machine/RowPaddingReset.lean`: Physical counted rewind restores both payload origins after grouped padding or cropping while preserving every tape cell and immutable span controls.

- `Machine/RowPaddingExecution.lean`: One fixed seven-tape padding or cropping program includes marker setup, every grouped transfer/fill/erase, counted origin restoration and final clock erasure. Exact full-tape endpoints with both clocks blank/head zero and linear cost at most 148*P*(N+M)+53; canonical span/count descriptors are explicit inputs.

- `Machine/RowPaddingWord.lean`: Flat descriptor arrays serialize to exactly the physical per-prefix row words and appended binary-zero spans. Padding/cropping word identities and the full transpose-after-padding output bridge connect the semantic row wrapper to the actual streamed data layout.

- `Machine/FixedBasePowerStep.lean`: One fixed binary-descriptor multiplication step retains the fixed base, replaces the old power with the canonical product, physically erases both old value and temporary product and restores every workspace tape. Cost is at most 110 times the new positive value.

- `Machine/FixedBasePowerDescriptor.lean`: One fixed eight-tape program computes B^k from a retained canonical runtime exponent for a fixed base B≥2. It physically writes the base and initial one, executes all k multiplication steps, and erases the base and countdown workspace. Exact canonical output and uniform fixed-base constant times B^k runtime.

- `Machine/RecursiveRowDivisor.lean`: Specializes the actual fixed-base power program to the fixed Shared50 World count W. The runtime depth produces canonical W^k on the unchanged finite alphabet, with preserved exponent and blank workspace; a dominating row range absorbs the complete construction cost linearly.

- `Machine/RoundedRowDescriptor.lean`: One fixed fifteen-tape program physically computes the least multiple of a positive canonical divisor that encloses a positive canonical row count. Original inputs are retained, the output is canonical and all temporary tapes are erased. Exact ceiling formula, divisibility, minimality and less-than-twice-row bound when D≤R; runtime is at most 4096 times the rounded row count.

- `Machine/RowPaddingConstructed.lean`: One fixed twelve-tape padding or cropping program generates both span descriptors from retained canonical prefix, row, rounded-row and suffix dimensions, executes the physical grouped scan and erases every generated counter. Exact serialized array endpoints, restored payload origins and entirely blank workspace; complete runtime at most 413 times padded volume.

- `Machine/SliceExponentPowers.lean`: One fixed nine-tape machine physically subtracts selected offset and width from the parent exponent, constructs both required fixed-radix powers, and erases temporary differences. Original exponent, offset and width are retained; complete runtime is linear in a dominating volume.

- `Machine/ArbitrarySliceDimensions.lean`: One fixed seventeen-tape machine constructs all three canonical arbitrary-window slice dimensions from six original headers and runtime offset/width controls. Original inputs are retained, every power/difference/intermediate product is erased, and the exact slice dimensions cost at most 700 times parent volume. Physical header installation is separate.

- `Machine/ArbitrarySliceHeaders.lean`: One fixed eighteen-tape wrapper physically saves six parent headers, constructs runtime slice dimensions, replaces occupied fields, and erases generated descriptors. Paid restoration returns the exact original headers and older frame stack. Entry costs at most 900 times volume and return at most 128 times volume; offset/width controls and all scratch endpoints are exact.

- `Machine/ArbitraryWidthSchedule.lean`: The literal power-piece schedule has computed offsets and depths and composes to the exact full chunk transpose. Each slice has an actual fixed recursive root execution contract with certified budget and exact serialized endpoints. Installed slice headers are an explicit premise; runtime schedule construction and whole driver remain open.

- `Machine/ArbitraryWidthHighRows.lean`: Computable least high-digit count Nat.clog(q*q)D exactly equals the manuscript ceiling when D=W^k. Integer-power domination, first-stop uniqueness, previous-power minimality and less-than-q-squared overshoot are proved, including the zero-exponent edge case. The physical selection loop is separate.

- `Machine/BinaryDescriptorCompare.lean`: One fixed three-tape twelve-state comparison program scans two immutable marked binary operands, writes their exact less-than flag and physically rewinds both heads. Complete cost is max width plus both operand widths plus eleven; a paid flag-clear primitive restores blank result workspace.

- `Machine/BinaryDescriptorIncrement.lean`: A fixed widened-alphabet one-tape three-state incrementer retains the marked descriptor representation, grows its highest bit as needed and returns to head one. Exact value increment, canonicality preservation and cost twice carry length, bounded by twice input width plus two.

- `Machine/RadixRangePadding.lean`: Numerical enlargement of both chunk ranges is exactly two grouped row extensions with literal flat-word regrouping. Reverse grouped crops equal direct restriction; padding, padded chunk transpose and cropping yield exactly the original chunk transpose. The enlarged volume is bounded by the square of the range factor. Whole physical two-range preparation and runtime dimension synthesis remain separate.

- `Machine/SliceHeaderPlacement.lean`: Injective generic placement shares the six actual root header tapes and appends exactly twelve offset/width/work/frame tapes. Exact active-bank and complement preservation lemmas avoid enumerating the large compiled recursive tape bank.

- `Machine/ArbitrarySliceCall.lean`: One fixed complete prepare/root/restore program executes any runtime selected power-width window. Actual slice dimensions and occupied headers are constructed, the fixed recursive root program executes, and original headers, frame stack, controls and spectators are restored. Exact window output and runtime rootBudget plus 1030 times parent volume; only canonical input, stack availability and the proved width/row shape are required.

- `Machine/FixedBasePowerUntilBound.lean`: Least stopping exponent and repeated descriptor-scan bounds for a fixed-base growing-power loop. Canonical threshold widths and all repeated comparisons are absorbed into a fixed-base constant times the final power.

- `Machine/FixedBasePowerUntilRange.lean`: The actual least-power selector has runtime linear in its positive input threshold, using strict less-than-one-base overshoot of the final power. Exact paired-digit exponent and range identities connect its output to the manuscript high-row selector.

- `Machine/FixedBasePowerUntil.lean`: One fixed nine-tape program physically initializes base/current/exponent, repeatedly compares and multiplies while below a retained runtime threshold, increments its exponent and clears each flag. It genuinely terminates at Nat.clog B D, retains canonical final power and exponent, clears all other workspace and costs at most a fixed-base constant times the final power.

- `Machine/ArbitraryWidthHighLayout.lean`: Literal finite row-major address bijections implement the manuscript high-field exchange/join and reverse separation. Exact numeric index/volume identities identify joined high digits as rows. The low recursive transpose, even with row padding and cropping, returns the original full-width transpose after separation. Physical high-field movement remains separate.

- `Machine/BinaryDescriptorAdvance.lean`: One fixed three-tape program physically advances a marked binary offset by a retained runtime count through repeated growing increments. It initializes and erases its work clock and restores the immutable count. Exact offset addition, canonicality and amortized cost 10 times count plus twice offset width plus seven times count width plus 28.

- `Machine/RadixDigitMoveRows.lean`: Moving one fixed-radix digit across an arbitrary spectator block is exactly a cyclic split into long rows followed by a cyclic merge of singleton rows. Literal source/output words and exact equal role words connect the two actual streaming primitives; head positioning and complete physical composition remain separate.

- `Machine/BinaryCanonicalData.lean`: Canonical little-endian binary descriptors have injective numerical value; a canonical zero descriptor is empty. This identifies actual normalized machine outputs with exact deterministic digit words.

- `Machine/BinaryDescriptorDivMod.lean`: One fixed fourteen-tape machine retains binary operands and returns both canonical quotient and remainder, restoring operand heads and clearing all arithmetic and tracking tapes. Exact division/modulus values and linear input-value cost for a fixed divisor.

- `Machine/ArbitraryWidthPieceCounter.lean`: A fixed-base extraction stage physically initializes the divisor, obtains canonical quotient/remainder, clears the divisor and replaces the consumed remaining width with its quotient. The remainder is the actual next base digit; every transition and cleanup is charged linearly.

- `Machine/ArbitraryWidthPieceLoop.lean`: One fixed finite outer loop repeatedly extracts actual runtime base digits until the canonical remaining width is zero, then clears all fourteen control tapes. Deterministic emitted digits match the manuscript partition. A fixed consume continuation must still implement repeated slice calls and depth/width/offset updates; no concrete whole piece driver is claimed.

- `Machine/SliceOffsetAdvance.lean`: Fixed placement advances the runtime offset in the existing twelve-tape slice tail, using its blank arithmetic work tape as the paid clock. The complete recursive root bank, saved frame and all other controls are exact spectators.

- `Machine/ArbitrarySliceStepBudget.lean`: The complete paid slice step is bounded by rootBudget plus 1087 times volume under explicit width bounds. This includes header preparation/restoration and physical offset updates; summing its literal power-piece budgets preserves the exact certified width exponent with a positive fixed constant.

- `Machine/ArbitrarySliceStep.lean`: One fixed program composes paid slice-header preparation, actual recursive root execution, original-header restoration and physical runtime offset advancement. Exact selected-window output and next offset, with every join, scan, carry and cleanup included in the cost.

- `Machine/ArbitraryWidthLevelAdvance.lean`: One fixed seven-tape program increments the canonical recursion-depth descriptor and multiplies the canonical selected width by the fixed base. Setup physically initializes the base, width one and depth zero; separate base or full cleanup is paid. Arbitrary framed data/offset controls are preserved; level advancement costs at most 120 times the new width.

- `Machine/RangePaddingDimensions.lean`: One fixed seventeen-tape constructor retains canonical prefix/chunk/gap/suffix/enlarged-range inputs and generates PN, PNG, GM and GMB by four actual product calls. All arithmetic workspace is erased. Separate paid cleanup clears the four outputs while preserving arbitrary payloads; both costs are linear in a dominating padded volume.

- `Machine/RowCropAny.lean`: The actual constructed row-cropping program works on arbitrary discarded rows, including nonzero tails. Exact arbitrary-array restriction, generated span-count cleanup, restored payload origins and linear padded-volume runtime extend the physical crop contract beyond zero-padded inputs.

- `Machine/RadixRangePaddingExecution.lean`: Complete fixed seventeen-tape padding and cropping programs generate their own grouped dimensions, execute both coordinate scans and erase every derived descriptor. Exact two-chunk pad and arbitrary crop endpoints with clean payload/workspace; each costs at most 1200 times padded volume. After the padded transpose the actual crop returns the original transpose. Runtime binary/radix range synthesis and composition with the interchange remain separate.

- `Machine/ArbitrarySliceRepeat.lean`: One fixed counted controller executes the actual paid slice-step program as many times as specified by a runtime base digit. Every slice trace is derived from the completed recursive root proof; offsets advance physically and exact repeated window swaps compose in order. Clock setup and cleanup are paid; optional consume also clears the digit descriptor. Certified digit-weighted budgets include all loop and erase costs. Whole outer dispatcher composition with level updates remains separate.

- `Machine/BinaryRadixRangePrepare.lean`: One fixed nineteen-tape program constructs both numerical ranges and the least radix exponent from the sole binary width, then physically pads both chunk coordinates. It retains original prefix/gap/suffix/width headers and exact generated metadata, with all private workspace blank. The inverse arbitrary-content crop clears all generated metadata and returns the exact original transpose after a padded transpose. Both bounds are fixed-radix constants times original volume; the intervening interchange must still be composed.

- `Machine/RadixRangeDescriptors.lean`: One fixed twelve-tape program constructs the binary chunk range 2^u, then the least enclosing fixed-radix power and its runtime exponent from the sole canonical binary width. The original width is retained, all scratch is cleared, and exact canonical outputs satisfy the range overshoot and exponent bounds. Construction and descriptor cleanup cost linearly in 2^u. Composition with the physical numerical padding scans remains separate.

- `Machine/RadixDigitMoveCore.lean`: Actual cyclic split, rewind, merge and rewind redistributes compatible literal row plans, with exact payload and role-bank endpoints.

- `Machine/RadixDigitMoveInitialized.lean`: Physical initialization of two runtime clocks and full erasure of roles, clocks and trackers around actual redistribution; four original descriptors retained.

- `Machine/RadixDigitMoveCounts.lean`: Construct and erase digit-movement dimensions from sole prefix and spectator lengths, including the constant one and prefix-times-spectator count; linear-volume cost.

- `Machine/RadixDigitMoveBlockRows.lean`: Literal digit exchange across a spectator block with an arbitrary trailing block. Exact split/merge word identity, role compatibility and mutually inverse forward/backward array permutations.

- `Machine/RadixDigitMoveBlockCounts.lean`: Construct spectator-times-suffix and prefix-times-spectator descriptors from the three original positive canonical lengths. All arithmetic workspace is cleared; construction and cleanup have linear-volume bounds.

- `Machine/RadixDigitMoveBlockPrepared.lean`: Prepared arbitrary-suffix digit movement and its actual inverse, with exact serialized endpoints, restored payload origin, erased role storage and paid linear-volume cost.

- `Machine/RadixDigitMoveBlockPlacement.lean`: Fixed tape placements share retained shape controls between block-dimension construction and the redistribution machine, preserving unrelated payload and descriptor tapes.

- `Machine/RadixDigitMoveBlockExecution.lean`: One fixed machine and its inverse exchange a radix digit across arbitrary spectator and suffix blocks, from sole prefix/spectator/suffix controls. Every derived count, clock, tracker and role tape is erased; payload is rewound. Tape count is 2Q+18 and runtime is at most (1516Q+11403) times volume. The repeated high-field joining/separation loop remains separate.

- `Machine/ArbitraryWidthHighPrepare.lean`: One fixed nineteen-tape program constructs k=clog_m(e), D=W^k, rho=clog_(q²)(D), R=q^(2rho) and the rounded multiple Rprime from the sole positive canonical runtime width. All intermediate workspace and the unused envelope are erased. Exact manuscript ceiling, divisibility and overshoot formulas are proved; construction costs constant(q) times rounded rows. Paid cleanup erases all five derived descriptors and retains only the original width.

- `Machine/FixedBaseDescriptorQuotient.lean`: One fixed fourteen-tape program replaces its sole canonical runtime descriptor by the canonical quotient by a compiled fixed base and physically erases the remainder. All thirteen private tapes are blank again. Exact divisible suffix shrinking and a fixed-base linear-input-value bound support the repeated high-digit movement controller.





- `Machine/ArbitraryWidthHighBudget.lean`: The actual high-digit selector satisfies an explicit constant times every positive width exponent, for all positive widths. The logarithmic construction cost and every fixed-coefficient per-digit movement therefore preserve the certified exponent rather than weakening it to a linear-width bound.

- `Machine/ArbitraryWidthHighExchangeControls.lean`: Actual setup writes zero offset, unit slice width and zero recursion depth, and copies the retained runtime high-digit count into the slice dispatcher. Paid cleanup erases generated offset, width and depth; count source is retained.

- `Machine/ArbitraryWidthHighExchangePlacement.lean`: Injective tape placement shares high-exchange controls with the complete recursive slice bank. Exact framed initialization and cleanup preserve every original parent descriptor, stack and payload spectator.



- `Machine/ArbitraryWidthHighGuard.lean`: The concrete integer depth and high-row selectors equal the manuscript real ceilings. High depth is positive beyond unit width and eventually below the original width, proving a fixed bounded set suffices for the elementary fallback. This proves the branch arithmetic, not the fallback machine.

- `Machine/ArbitraryWidthHighMetadataBudget.lean`: The actual rounded high-row count is uniformly bounded by a fixed multiple of the original array volume, for every width. The large-width branch uses the selected high-depth guard; the bounded fallback uses monotonicity of the runtime divisor. Thus constructing row metadata before branch selection has a paid linear-volume bound on both branches.







- `Machine/PlacedDescriptorConstruction.lean`: Exact single-output framing places power and product constructors into an arbitrary larger bank. Every tape and head outside the generated output is retained literally; no supplied runtime result is assumed.

- `Machine/RadixHighBlockJoinBank.lean`: Fixed shared bank for high-block joining and separation, retaining source, spectator size, original prefix/suffix and outer count. Mutable prefix/suffix/base and thirteen arithmetic tapes have exact descriptor and blank-workspace layouts.

- `Machine/RadixHighBlockJoinSetup.lean`: Fixed injective placements route the retained runtime exponent into actual power construction and original lengths into product construction, sharing the movement bank. Exact descriptor updates and blank-workspace views preserve every outer tape.

- `Machine/RadixHighBlockJoinInitialize.lean`: Complete actual sole-original-header setup for both ordered high-block movement directions. Physically copy one original length, write the fixed radix, construct its runtime power and enlarged length, then erase the intermediate power. Original payload, shape, count and clock are retained; a fixed-radix linear-volume bound pays every step.

- `Machine/RadixHighBlockJoinCleanup.lean`: Actual cleanup erases mutable prefix, suffix and radix descriptors after either direction, preserving payload and sole original shape/count/clock. Any canonical terminal working lengths bounded by volume satisfy the explicit fixed-radix linear cleanup cost.

- `Machine/ScanRight.lean`: One fixed single-tape sentinel scan preserves all symbols and charges exactly one transition per traversed cell, at arbitrary integer head positions.

- `Machine/BinaryDescriptorNormalize.lean`: Physically scan a marked descriptor from head one to its end, trim high zero bits and return to head one. Exact canonical output of unchanged value, including zero, with all scans and rewinds paid.

- `Machine/BinaryDescriptorDifference.lean`: One fixed three-tape finite-alphabet program subtracts arbitrary-width immutable marked operands and physically normalizes the result. Both original words and heads are preserved, the output is canonical at head one, and no padded operands or derived result are supplied. Exact runtime is bounded by six times the larger descriptor length plus21, or six times the original minuend value plus27 for canonical inputs.


- `Machine/RadixHighBlockJoinSemantics.lean`: Successive single-radix movements join an entire runtime high block in its original digit order. Exact indexed cells and equality to the whole block transpose are proved for arbitrary payload symbols and all spectators.


- `Machine/ArbitraryWidthHighBranch.lean`: One fixed fifteen-state finite controller physically compares retained high depth with width, tests positive canonical high depth, selects the exact manuscript high or fallback branch and erases its comparison flag. Both operands and every head are preserved, with exact selected terminal state and length/value/volume runtime bounds.

- `Machine/ArbitraryWidthHighBranchPlacement.lean`: Injective shared-bank placement of the actual high-width selector takes only literal canonical descriptor, head and blank flag premises. It proves the exact selected state, genuine halt and complete tape/head preservation with no supplied comparison result or active-view oracle.

- `Machine/RadixHighBlockJoinPlacement.lean`: Exact shared-bank views place the existing digit movement machine and its arithmetic tail into the ordered high-block body while preserving all other tapes.

- `Machine/RadixHighBlockJoinArithmetic.lean`: Actual prefix growth and suffix shrinking operate on the shared movement bank, preserving arbitrary payload, original headers, spectators and all framed arithmetic storage.

- `Machine/RadixHighBlockJoinBody.lean`: One fixed body physically shrinks the working suffix, executes the literal ordered radix digit movement, and grows the prefix. Both forward and inverse directions have exact serialized endpoints and fixed-radix linear-volume cost.

- `Machine/RadixHighBlockJoinLoop.lean`: A concrete runtime-counted loop executes every high digit in order from a canonical retained exponent. Its computed trace is proved step by step from the actual body; the final payload is exactly the whole-block ordered join, with paid clocks and preserved inputs.


- `Machine/RadixHighBlockSeparateSemantics.lean`: Repeated trailing-digit movement separates the joined high block in exact original digit order. Its recursive array is proved equal to the literal whole-block separation, preserving every spectator and arbitrary payload symbol.

- `Machine/RadixHighBlockSeparateLoop.lean`: The actual retained-exponent counted loop executes every inverse high-digit movement, with a computed step trace and exact whole-block separated endpoint. All clocks and shared arithmetic work are paid and restored; no callback execution oracle is supplied.


- `Machine/ArbitraryWidthHighDimensions.lean`: An actual seventeen-tape constructor takes only retained canonical P/G/B/width/high-depth headers and blank private storage. It physically computes low width by normalized immutable subtraction, both radix powers and all three high-block movement dimensions, preserving original inputs and restoring all six arithmetic tapes. Exact generated values and a fixed-radix linear original-volume runtime bound are proved.

- `Machine/ArbitraryWidthHighDimensionsCleanup.lean`: One actual finite list-erasure program clears all six generated high-layout descriptors and restores their heads to zero while retaining the original five headers and all arithmetic storage. Exact constructor-output to sole-header-input cleanup is proved, with runtime at most54 times the original positive volume.

- `Machine/RowPaddingConstructedAlphabet.lean`: The actual twelve-tape row padding/cropping machines are adapted by exact finite-alphabet simulation to the recursive interchange alphabet. Literal larger-alphabet bank endpoints preserve canonical dimensions, erase consumed source words and write exact zero-padded or cropped arrays. Both general encoded-symbol and literal bit-array contracts retain the complete413-times-padded-volume bound, including all descriptor construction and erasure.

- `Machine/ArbitraryWidthJoinedHeaders.lean`: One actual twelve-tape program copies retained prefix, rounded rows and spectator headers, writes the unit before-H header and computes the low width by immutable canonical subtraction. It produces all six literal padded-joined root headers, preserves all originals and proves their semantic Headers predicate; paid initialization costs at most83 times a dominating volume.

- `Machine/ArbitraryWidthJoinedHeadersCleanup.lean`: The actual six-header cleanup erases every generated padded-joined root descriptor and returns all target heads to zero while retaining the original six headers. Exact output-to-input restoration and a54-times-dominating-volume cost are proved.

- `Machine/ArbitraryWidthHighPaddingSuffix.lean`: The actual product constructor operates directly on retained generated high-movement lengths and produces the exact joined row suffix, preserving originals and restoring arithmetic scratch. Literal rowLength equality and original/padded-volume bounds are proved; construction and subsequent erasure cost at most81 and8 times the suffix length.

- `Machine/ArbitraryWidthHighPrefix.lean`: The three original prefix factors are physically folded into one canonical descriptor by two real products followed by intermediate erasure on eight tapes. All originals and scratch are retained/restored; construction costs at most174 times a dominating volume and final cleanup8 times it. Exact folded volume and address identities cover arbitrary original row/prefix factorizations.




- `Machine/ArbitraryWidthHighFoldSemantics.lean`: Literal finite-index folding combines all original prefix and row factors without changing any serialized cell. The full transpose of any valid original row-divisor view equals the folded row-one transpose, with exact source-word and binary-encoding identities.





- `Machine/ArbitraryWidthHighFoldHeaders.lean`: An actual sixteen-tape program folds the three retained original prefix factors, writes the two unit headers and copies width/spectators into six blank target root headers. All original six headers and arithmetic scratch are retained/restored. Exact folded Headers correctness and a224-times-dominating-volume setup bound are proved.

- `Machine/ArbitraryWidthHighFoldHeadersCleanup.lean`: The actual six-target root-header erasure restores the complete folded-header input bank while retaining every original descriptor and blank arithmetic tape. Exact lifecycle restoration and a54-times-dominating-volume cleanup bound are proved.








- `Machine/FixedHeaderBankCopy.lean`: One actual finite program copies a fixed family of retained canonical caller descriptors into appended blank target tapes, preserving every caller tape/head even when sources repeat. Exact target bank and fixed-family linear-volume construction and erasure costs are proved.

- `Machine/FixedHeaderSparseBankCopy.lean`: Actual header copying and cleanup are placed into fixed injective named slots of a larger private bank. All other private tapes remain blank, all caller storage is retained, repeated sources are supported, and both exact banks and linear-volume costs are proved.

- `Machine/ArbitraryWidthHighDimensionsShared.lean`: The actual shared dimension lifecycle first copies five original caller headers into a blank seventeen-tape bank, computes low width/radix powers/movement dimensions and later erases both generated and copied descriptors. Every caller tape/head is preserved; complete setup and cleanup have fixed-radix linear original-volume bounds. No preconstructed generated bank is supplied.



- `Machine/ArbitraryWidthHighFoldHeadersShared.lean`: Copies the six original caller descriptors into blank private storage, constructs the folded prefix and root headers, and erases the complete private bank after use. Literal caller and generated-header views and paid linear construction/cleanup bounds are proved.

- `Machine/ArbitraryWidthJoinedHeadersShared.lean`: Constructs canonical padded joined-root headers from retained caller descriptors in a wholly blank twelve-tape bank, preserving the caller and paying all copying, subtraction, unit writing and cleanup.

- `Machine/ArbitraryWidthHighDimensionsAndSuffixShared.lean`: Constructs the high movement dimensions and joined-row suffix from original caller headers in a blank seventeen-tape bank, then erases every copied and generated descriptor. Literal header values, canonicality, source slots, and linear-volume lifecycle costs are proved.


- `Machine/ArbitraryWidthExecutionPrivateHeadersAppend.lean`: Proves exact sparse header banks across appended private storage, with named slots and preserved blank complements.








- `Machine/ArbitraryWidthZeroHeaderShared.lean`: An actual fixed writer constructs the canonical-zero descriptor marker from a blank appended tape, and an actual eraser restores blank storage. Every caller tape is preserved; exact six-transition setup and four-transition cleanup are proved.

















- `Machine/BinaryRadixRangePrepareAlphabet.lean`: Executes binary-to-radix range preparation and inverse cropping on the recursive alphabet through the actual alphabet lift. Literal encoded bit and descriptor banks, exact pad/transpose/crop endpoints and unchanged paid runtime are proved.

- `Machine/BinaryRadixRootHeadersShared.lean`: Physically writes a temporary canonical one, copies six recursive root headers from the prepared binary bank, and erases the temporary one. All caller storage is retained; exact root Headers, literal copy slots, and original-binary-volume setup/cleanup bounds are proved.


- `Machine/BinaryAdjacentWidthInterchange.lean`: Proves exact rectangular transposition for binary widths differing by one as an equal-width transpose and one actual fixed-radix-two movement, with the inverse orientation using real unmovement first. Literal serialized endpoints and paid movement proofs cover arbitrary spectators and zero shorter width. Header construction and full composition with the equal-width wrapper remain separate.



- `Machine/BinaryAdjacentWidthHeadersShared.lean`: Actually writes the zero high-count control and constructs P, binary-range times G, and binary-range times B from the four original P/G/B/width headers. Named movement source slots, literal canonical values, caller preservation and reverse erasure of every generated field have linear rectangular-volume bounds.

- `Machine/BinaryAdjacentWidthMovementShared.lean`: One actual shared-source lifecycle constructs binary movement dimensions from only the original four P/G/B/width headers, physically copies the three execution headers, executes radix-two movement or inverse movement, and erases every generated and copied descriptor. All forty private tapes start and finish blank; exact movement words, arbitrary caller preservation and linear rectangular-volume runtime are proved without generated-header or preimage assumptions.



- `Machine/BinaryRadixEqualShared.lean`: Physically copies the four original caller shape/width headers into blank private storage, shares the literal payload with the complete binary interchange, and erases the copied headers afterward. Exact transpose and preservation of all other caller fields and private blank storage are proved, with the unchanged certified exponent.

- `Machine/BinaryAdjacentWidthPrefixShared.lean`: Physically writes the canonical one and constructs the doubled spectator prefix from original headers using the radix-two dimension engine. Literal doubled-prefix sources, canonical values, caller preservation, paid rectangular-volume budgets and complete eighteen-tape erasure are proved.


- `Machine/BinaryAdjacentWidthSelector.lean`: Actually compares both canonical original widths, reuses and erases a blank flag, and halts in one of three finite states: equal, longer H, or longer D. All original cells and heads are restored. Exact state/value equivalences, adjacent-width consequences and a linear original-volume comparison budget cover zero-width cases.

- `Machine/BinaryAdjacentWidthSelectorDispatch.lean`: A real finite-flow composition connects the physical three-way selector to the selected supplied branch program and its genuine halt. Conditional branch contracts and all selector/jump/branch costs are proved. Instantiating the final concrete equal/adjacent machine is separate.

- `Machine/BinaryInterchangeRun.lean`: A fixed concrete binary rectangular interchange machine reads the original five canonical headers, physically selects equal or adjacent-width branches, returns the exact transpose, and preserves all other caller tapes while restoring every private tape and head. Covers zero widths with no branch callbacks or derived-header inputs.

- `Machine/BinaryInterchangeBudget.lean`: Proves one positive uniform coefficient bounds the actual comparison, dispatch and selected concrete branch runtime by original rectangular volume times max-one maximum width to the certified exponent 1−296/10^11.

- `Machine/CompactGadgetReservationCapacity.lean`: Exact existing front2H/backH ceiling-chunk capacities, bounded slack and complete dirty-field allocation; no compact field is inserted into the row index.

- `Machine/CompactGadgetReservationShape.lean`: Concrete row/front-temporary/front-control/active/back/payload bit geometry, disjoint reserved slots, bit-count conservation and exact temp/control rectangular factorizations including slack.

- `Machine/CompactGlobalRowPadding.lean`: Original row axes dominate the full runtime recursive divisor; one global pad costs at most twice the original volume and supplies inherited depth divisibility, no per-node re-padding and exact role volumes.

- `Machine/CompactGlobalReservation.lean`: Original global axis counts determine the complete compact shape; row and within-row bits sum to D*K, original volume is retained, padded volume doubles at most and every node compact field fits.

- `Machine/CompactScalarAllowances.lean`: The actual multiplier choices d,K,p derive complete D*K+3 cubic repair sizing and selected-count bounds; the actual dyadic precision log fits K eventually, and literal polynomial-record bits eventually pay padded address width. No independent cubic-width or sufficiently-large-guard premise is assumed.

- `Machine/CompactGuardGrowth.lean`: The actual precision logarithm is little-o of the actual chunk width, with arbitrary positive eventual coefficients.

- `Machine/CompactReservationGrowth.lean`: Actual original row-axis ceilings and front/back reservation rounding yield total reserved axes little-o of actual dimension; all choices are the multiplier scalar parameters.

- `Machine/CompactComplexActualCallFrameEdge.lean`: The actual schema-chosen residual coordinates, in their original call order, factor the named original complex frame edge. Each coordinate retains its own positive or negative fourth-root weight and the edge orientation; the actual child inverse flag realizes that signed weight. The original all-column frame instruction equals the product over these same call kernels. Physical coordinate-tensor correspondence, basis alignment and complete recursive execution remain open.

- `Machine/CompactComplexActualCallLoweredNetwork.lean`: The complete original lowered network now has a factor certificate from the same occurrence-indexed actual child call list used by the recursive controller. Signed directions and edge operators are proved for this literal family, without selecting an unrelated existential factorization. Its full array execution retains original scalar gates and every dirty scratch incidence, and its exact factor count is the original rank sum. This is complete array semantics; physical aligned recursive execution remains open. Original edge occurrence order is public and proved through a generic attached-list lemma, keeping the fixed circuit symbolic during guarded verification.

## Compact

Compact packed controls, repair, and density bounds.

- `Compact/Ideal.lean` and `Compact/ExactRepair.lean`: a packed ideal toggle
  permutation, preservation of the actual guard predicate, and executable
  destination repair connected to both concrete packed programs. Correctness
  holds for every address, including saturated temporary digits and failed
  guards. These prove address semantics. Tape partition and reinsertion
  primitives are proved separately; computing record keys, full sorting, and
  assembling the complete repair pipeline remain open.
- `Compact/Permutations.lean`: modular rotations as actual permutations,
  restoration of an arbitrary back field by swap/load/swap, and invertibility
  of both packed programs on every address, including bad addresses. The
  permutations are proved to agree with the integer implementations.
- `Compact/RepairBounds.lean`: the uniform rational exceptional-density bound
  under the stated dyadic cutoff, and the inequality reducing the written
  repair-cost expression to three logical volumes. The sorting implementation
  still needs a proof.
- `Compact/Counting.lean` and `Compact/Density.lean`: exact good- and bad-address
  counts for both concrete repair predicates, using a restricted radix
  bijection. These establish the common exceptional fraction bound capped by
  one, and its uniform bound `5 / (128*p^3)` under the dyadic cutoff. The density
  is derived from actual address cardinalities rather than assumed. Extracting,
  sorting, and reinserting the counted records on tapes remains open.
- `Compact/RepairPipeline.lean`: the assembled exceptional-address repair at
  the list level. On the rank-ordered stream of the actual program's output,
  flag the exceptional addresses, extract those records with their
  destination ranks `e (T (S⁻¹ q))`, radix sort them by destination with the
  stable passes of `RadixSort`, and reinsert them into the flagged holes with
  `fill`; the result is the stream of the ideal map everywhere, for
  any `S`, `T`, exceptional set with the agreement and preservation
  properties, and in particular for both packed programs. The extracted
  records are exactly the exceptional addresses, so their count is the
  exceptional fraction times the volume, the radix passes traverse
  `k · |ℬ| · w` cells, and the written cost expression is at most three
  volumes under the density bound. Tape execution of the scan is not here.
  their destination ranks in binary, are the keyed records of the fixed
  eleven-tape stage machine `Machine/RepairStage`; on them and the flagged
  actual output stream it halts with the ideal stream on its output tape,
  within `74k + 4` extracted volumes, one full-stream volume, and `k + 7`,
  the extracted volume being at most `|ℬ|·(k + 2 + w)`. The flagging scan and
  the destination-rank arithmetic that produce the keyed records remain open.
  on the unflagged actual output stream, with the scan's flags and keys being
  membership and the destination rank `e (T (S⁻¹ q))` of the rank's address,
  halts with the ideal stream on the output slot, within the key cost plus
  ten per record, three stream volumes, `74k + 5` extracted volumes,
  `2k + 3` per exceptional address, and `k + 14`. The key routine's tape
  arithmetic is a program parameter; the concrete legacy instance still depends
  on runtime dimensions in finite control, so uniform key compilation remains open.
  power-of-two radix: a word of `n·q` bits is the packed integer whose
  base-`2^q` digits are its `q`-bit block values, the gather gadget's word is
  the packing of its digit words, and the per-digit forms of the compact
  control arithmetic, a masked shifted block, a block's parity, a toggled
  parity, have their stated values.
  computes `packedEarly` in the radices `2^q` and `2^b`: each gathered offset
  word packs as the corresponding integer offset (masked shifted blocks,
  controls, parities, toggled parities), each modular transduction is the
  corresponding modular update, and the signed third line is the difference
  of two packings; the final words are exactly the packed program's output
  integers.
  computes the packed permutation's inverse: `packedEarly` applied to the
  integers of its recovered words returns the integers of its input words,
  each forward line cancelling the corresponding inverse line modulo the
  radix power, so by injectivity the recovered address is the preimage.
  is exclusive or with the control mask, the control bits at stride `q`
  (which is the controls gather); it flips the lowest bit of each block
  exactly when its control is set and packs as `toggleList` of the block
  digits.
  the exceptional set: with the constants `2B`, `L - 2B - 1` and `B - 2` as
  words of the block widths, some flag is set exactly when the address fails
  `earlyGood` in the radices `2^q` and `2^b`, the upper bits of a block
  being its digit halved.
  key data for the concrete early instance with ranks in lexicographic
  order: the fixed-width counter's word at rank `j` has value `j` and splits
  into the address words, the guard flags are the membership flag of the
  rank's address, the inverse program's words are the packed permutation's
  preimage, the exclusive or with the control mask is the ideal map, and the
  appended words are the binary expansion of the destination rank.
  bank (key at slot twelve, counter at thirteen, scratch from fourteen) meets
  the scan's key contract for the concrete early instance: the scan's counter
  tape is the counter word over the separator, the active bank is the
  routine's input, and the replaced bank is the scan bank with the key word
  written. With it, `repair_instance` is the complete repair machine: scan
  with the key routine, sort, strip and reinsert, carrying the unflagged
  actual stream to the ideal stream within the pipeline's bound. Its placed key
  still depends on q, b and the control count in finite control; replacing it
  with one runtime-driven machine remains open.
- `Compact/Layout.lean`: reversible whole-row splitting, preservation and
  completeness of every suffix, exact role volumes, padding to a multiple
  within twice the original volume, and ceiling-based reservation capacities.
- `Compact/Radix.lean`: bounded radix packing and decoding, injectivity, signed
  packed additions without carries, and preservation of lower/upper spectators.
- `Compact/PackedControl.lean`: executable modular arithmetic implementations
  of the earlier- and later-source gadgets, proved correct for arbitrarily many
  guarded digits. Offsets decode the current packed fields. The target parities
  are toggled and dirty temporary fields restored exactly. Embedding these
  segments in the complete physical slot, compiling the operations to tapes,
  and bounding their tape costs remain open.
- `Compact/DirtyControl.lean`: the four-update identity, restoration of an
  arbitrary dirty integer temporary, parity and guard invariance, the
  later-source identity, and guarded intermediate ranges. These are universal
  integer statements, used by the guarded packed modular refinement above.
- `Compact/Repair.lean`: for any two permutations agreeing outside an invariant
  exceptional set, the actual map preserves that set and destination repair
  gives exactly the ideal map. `ExactRepair.lean` now instantiates this result
  with both verified packed programs. Implementing repair within the tape cost
  remains necessary.

## Networks

- `Networks/AffineFieldBijective.lean`: Legal finite field programs are bijections, including reflected subtraction and literal coordinate interchange, validating original inverse-function address semantics.

Bit and complex networks.

- `Networks/Scalar.lean`: the eight-step arbitrary-scratch cancellation
  schedule, three-stage signed exchange, bit and complex triple-intersection
  coefficients, the resulting complex bank identity at any finite ground size,
  and the common-frame linear-gate identity. Sparse network realization,
  residual bases, endpoint corrections, and tape compilation remain open.

- `Networks/Circuit.lean`: executable finite linear register updates and matrix
  blocks, the full eight-row dirty-scratch schedule, its reversed inverse, and
  exact instruction counts. Arbitrary scratch and spectator registers are
  restored. A register update may read many terms: these instruction counts
  are neither sparse wire counts nor tape runtimes.
- `Networks/CircuitTriples.lean`: explicit copy, injection, gather, and scatter
  matrices for the complex motif, with neighboring-pair coefficient identities
  and the resulting executable shear over rational scalars. Finite wire
  enumerations and injective three-element labels parameterize the construction;
  concrete cardinalities, residual rank savings, Gaussian-dyadic values, and
  tape compilation remain open.

- `Networks/CircuitRouting.lean`: semantics-preserving register renaming and
  the three executable dirty-scratch stages implementing signed bank exchange.
  The middle stage uses the reversed inverse schedule with bank roles exchanged;
  all scratch and spectators are restored. Exact instruction counts and the
  neighboring-pair rational motif instance are proved. Tape movement, sparse
  wire counts, and residual spaces remain separate obligations.

- `Networks/CircuitBits.lean`: explicit binary motif matrices over `ZMod 2`,
  with intersection-one side pairs and coordinate-only central sums. Actual
  matrix coefficients reconstruct the source, proving executable dirty-scratch
  shear and true bank exchange with full scratch restoration. Elementary
  instruction counts are proved; grouped-gate topology and tape costs are not.

- `Networks/Labels.lean`: the degree-one rational and binary bilinear label
  spaces, their nondegeneracy, triple-indicator pairing formulas, orthogonality
  of neighboring triples, and nondegeneracy of each triple line. The rational
  form is nondegenerate whenever the ground size differs from nine. These
  label fields differ from the circuit scalar rings; tensor-cube labels,
  nested gate labels, and total residual-rank savings remain open.

- `Networks/NeighborCounts.lean`: an explicit intersection/outside splitting
  equivalence proves the generic fixed-size-subset intersection census. It
  yields exact triple-bank, bit-neighbor, complex-neighbor, and ordered-pair
  cardinalities, including 161700 triples, 13968 bit neighbors per triple,
  and 147731 complex neighbors at ground size 100. Enumeration transport
  connects these counts to the finite-index circuit side-wire predicates.
- `Networks/Wires.lean`: named roles for both data banks and every stage's
  separate invocation scratch, with exact cardinalities. The ground-size-100
  counts match both manuscript wire totals. Compiling the global gate schedule
  on these roles and attaching nested labels remain open; this is a layout
  cardinality proof, not yet the complete rank-saving network theorem.

- `Networks/TensorLabels.lean`: tensor products of finite nondegenerate
  bilinear forms are proved nondegenerate using their Kronecker matrices.
  The actual tensor-cube label spaces have dimension `h^3`; pure triple
  tensors have rational self-pairing eight or binary self-pairing one.
  Their terminal lines and orthogonal complements give nondegenerate direct
  decompositions with dimensions one and `h^3 - 1`. Intermediate gate labels
  and the complete residual budget still need construction.
- `Networks/FramedCircuit.lean`: explicit edge-frame instructions and finite
  circuit compilation prove the full common-frame identity, including all
  scratch and spectator wires. At every address the logical circuit is the
  existing executable scalar circuit. Intermediate frames cancel exactly;
  approximate frame implementations, grouped motif topology, and tape costs
  remain separate obligations.

- `Networks/ProjectionRank.lean`: actual orthogonal projectors on finite
  nondegenerate labels, their commutation along nested labels, and the exact
  range of their difference as the larger label intersected with the smaller
  orthogonal complement. This residual is nondegenerate, and the projector
  difference has rank equal to the label-dimension difference. Complementary
  projections also verify the routed endpoint identity with the required negative
  source projection, whose rank is exactly the source-label dimension. The network
  must still construct its comparable gate labels and sum these edge ranks.

- `Networks/GlobalCircuit.lean` and `Networks/GlobalCircuitBits.lean`: the
  full three-coordinate scalar schedule runs on the actual named wire layout,
  with separate arbitrary scratch for every invocation in every stage. Finite
  gate embedding and complete invocation enumeration prove global signed
  exchange over rational values and true exchange over binary values, with all
  scratch restored and exact elementary instruction counts. The dense row
  lists prove scalar semantics; grouped sparse incidence topology, Gaussian-
  dyadic scalar extension, and labeled rank/tape bounds remain separate.

- `Networks/ShearFrame.lean`: exact address-shear permutations and linear
  frames on arrays, with independent address and value rings. Composition
  adds matrices, edge changes subtract matrices, and the routed complementary
  projector endpoints give the full identity-matrix shear. Finite-radix
  encoding, denominator reduction, and rank-dependent tape execution remain
  open.

- `Networks/BinaryOrthonormal.lean`: every finite-dimensional symmetric,
  nondegenerate, nonalternating form over the binary field has an orthonormal
  basis indexed by its dimension. Explicit absorption of a hyperbolic plane
  into a unit line supports dimension induction. Concrete residual spaces
  still need their nonalternation witnesses.

- `Networks/GroupedCircuit.lean`: sparse simultaneous groups with read/write
  separation refine to elementary circuits, with exact nonzero wire supports.
  The eight motif rows use source-owned copy groups, target-owned injections,
  and single central groups; their bit and rational dirty-shear semantics and
  group count are proved. Framed compilation aligns each group once. Full
  grouped exchange topology and the labeled rank budget remain separate.

- `Networks/GroupedRouting.lean`: the inverse grouped motif and local
  three-stage exchange refine the existing bit swap and rational signed
  exchange, preserving dirty scratch. Renaming transports sparse supports
  exactly; the grouped gate count and threefold incidence count are proved.
  The global grouped embedding and labeled rank sum remain separate.

- `Networks/NeighborResidual.lean`: orthogonal anisotropic pairs span a
  nondegenerate plane, and their complement is the side residual with dimension
  two less than the ambient space. For neighboring rational and binary triples
  this gives the actual degree-one residual. Binary coordinate vectors outside
  supports prove norm-one witnesses for triple, pair, square-tensor, and
  cube-tensor complements; triple and neighbor complements have orthonormal
  bases. The full nested tensor gate labels remain to be assembled.

- `Networks/GlobalGrouped.lean`: actual grouped three-coordinate schedules
  on the existing global wire layout, with distinct scratch per invocation.
  Injective placement transports sparse supports exactly; the middle reversed
  inverse retains physical side orientation. The complete bit swap and rational
  signed exchange refine the scalar circuits, with exact grouped and incidence
  counts. Nested labels and total rank bounds remain separate.

- `Networks/BinaryPhase.lean`: exact rank-one decomposition of nested
  projection differences, indexed by the residual dimension. Actual Hamming
  weight modulo four is additive on orthogonal vectors, giving a diagonal
  edge factorization into one phase per orthonormal residual direction; unit
  directions have quarter-turn phases. Walsh conjugation, binary tensor
  coordinate identification, and tape execution remain separate.

- `Networks/TensorSubspace.lean`: actual embedded tensor subspaces, with
  monotonicity, distribution over sums, multiplicative dimensions, restricted
  bilinear pairing, and proved preservation of nondegeneracy and orthogonality.
  These support the nested labels of the network schedule.

- `Networks/TensorCoordinates.lean`: the actual binary tensor cube has an
  explicit coordinate tensor basis with identity Gram matrix, giving a linear
  isometry onto exactly `h^3` binary coordinates. This connects tensor labels
  to the concrete dot-product and Hamming-weight phase formulas.

- `Networks/LabelTransport.lean`: linear isometries transport actual label
  subspaces, nondegeneracy, orthogonal residuals, dimensions, and projection
  operators. Thus the coordinate bridge preserves the mathematical edge
  operators as well as their ranks. No tape coordinate-conversion cost is claimed.

- `Networks/BinaryWalsh.lean`: an explicit finite Walsh transform with
  checked orthogonality and inverse normalization conjugates the diagonal
  phase factors to actual address translations. Increasing and decreasing
  edges run exactly one forward/inverse manuscript kernel per residual
  dimension, given the proved local geometric premises. Multi-column lifting,
  Gaussian-dyadic closure, and tape execution remain separate.

- `Networks/MotifLabels.lean`: the actual eight-row local tensor-label table,
  with all labels nondegenerate and all data/neighbor-side paths increasing.
  The central return is the unique decrease and removes exactly the past line
  tensored with the current space. Tensoring by the future line preserves
  dimensions and comparability, including scratch source/sink edges. Global
  attachment and interstage coordinate identification remain separate.

- `Networks/RankTrace.lean`: finite wire-label update histories record the
  actual source/target subspaces. For comparable nondegenerate labels, the
  true projection-rank sum plus source dimensions equals sink dimensions
  plus twice the total dimension loss. Concrete schedule attachment and
  enumeration of decreasing edges must still establish the network budget.

- `Networks/GroupedFrames.lean`: the full common-frame compiler preserves
  actual multi-output group boundaries, tracks each wire’s last label, and
  appends all sink edges. Its exact array identity uses the original scalar
  grouped program; its complete label history feeds the checked projection-rank
  balance. The rational negative-source sign change has its actual rank proved
  in `ProjectionRank.lean`. Global loss enumeration remains separate.

- `Networks/StageLabels.lean`: actual tensor associator/unit isometries
  embed all three local motif geometries into the common tensor cube. X/Y
  output labels equal the next-stage input labels, and terminal labels are
  exactly the tensor line/zero and full space/orthogonal line complement.
  Attaching these subspaces to the global physical group history remains separate.

- `Networks/MotifSupport.lean`: actual sparse support lemmas identify each
  side wire with its unique copy/injection owner. Both concrete motifs have
  nonzero injection coefficients precisely at the owning target; central
  incidence tests and invariance under coefficient negation are also proved.

- `Networks/BinaryColumns.lean`: concrete slice operators on arrays indexed
  by multiple binary columns. Distinct-column operations commute, and the
  finite product regroups each forward/reverse edge into exactly one
  all-column factor per residual direction. The factor count is the actual
  dimension difference. Residual witnesses and arithmetic closure are supplied
  by separate modules; attachment to physical edges and tape implementation remain.

- `Networks/MotifResiduals.lean`: exact orthogonal residual formulas for the
  local data, side, and central label comparisons. Residuals tensor with the
  future line, and the final scratch residual is exactly the full earlier
  space tensored with the future-line complement.

- `Networks/BinaryMotifResiduals.lean`: all thirteen listed local comparisons
  have zero residual or an actual norm-one vector, including the future
  factor and scratch sink. Concrete witnesses discharge the earlier and
  future premises at each of the three stages for ground size above six.
  Isometries transport these witnesses. Matching every physical sparse-history
  edge to these comparisons remains part of global attachment.

- `Networks/GaussianDyadic.lean`: exact Gaussian-integer numerators on a common
  binary scale, closed under addition, subtraction, multiplication and halving.
  Actual binary translation kernels consume at most one binary place each;
  all-column factors consume at most the column count. Both directions of a
  nested projection edge have precision bounded by the actual residual
  dimension times the column count, with the zero-or-unit premise explicit.

- `Networks/LabeledMotif.lean`: literal labeled forward, inverse, and opposite
  grouped motifs erase to the actual scalar schedules. Every physical wire
  history is derived from sparse incidence. Edge comparability, nondegenerate
  labels, and total loss bounded by central-wire count times current dimension
  are proved, including sink alignment and skipped intermediate labels.

- `Networks/SignedProjection.lean`: the first rational edge from a negative
  source projection to any containing label has rank equal to that containing
  label's dimension. The correction over ordinary edge rank is exactly the
  source dimension, even when sparse support skips an initial repeated label.

- `Networks/GlobalLabels.lean` and `Networks/GlobalLabelsNondegenerate.lean`:
  actual tensor labels attached to every physically embedded invocation of
  the three-stage schedule. Erasing labels returns precisely `GlobalGrouped`;
  source/sink and interstage identities refer to the same physical addresses.
  Every attached label is nondegenerate after future lift and transport.

- `Networks/GlobalLabelsResiduals.lean`: explicit binary norm-one witnesses
  cover the three extra comparisons created by missing sparse incidences,
  including their actual future-line lifts. Thus skipped intermediate labels
  do not require an assumed nonalternation property.

- `Networks/GlobalRank.lean`: actual local histories, losses, and comparable
  edges transport through tensor-stage maps and physical embeddings. Each
  real invocation loses at most the central-wire count times current dimension,
  also when prior sparse histories leave labels below the canonical input.
  Wires outside the invocation remain unchanged.

- `Networks/GlobalRankStages.lean`: disjoint physical invocation induction
  assembles the complete three-stage loss bound and comparable label edges.
  Sparse predecessors may leave weaker inputs; the invariant handles them.
  Actual terminal alignment adds no loss. No stage-loss premise is assumed.

- `Networks/ProjectionTrace.lean`: nondegeneracy propagates through actual
  sequential label updates. The sum of genuine projector-difference ranks
  equals dimension variation and telescopes with exactly twice the trace loss.

- `Networks/GlobalProjectionRank.lean`: all labels in the actual physical
  trace are nondegenerate; its projector ranks balance the actual terminal
  dimensions. The full loss theorem gives a global rank upper bound without
  supplying an assumed rank or loss budget.

- `Networks/ComplexRank25.lean`: instantiates the actual rational-scalar
  complex circuit at ground size twenty-five, its binary labels, sparse
  injection support, neighbor orthogonality, and complete terminal list.
  Its actual projection-rank sum is at most 916333630984500000 and meets the
  selected complex branching exponent. Binary edge-factor coverage is supplied
  by `GlobalBinaryResiduals` and `ComplexPhaseBudget`; tape costs remain open.

- `Networks/GlobalBinaryResiduals.lean`: complete norm-one-or-zero residual
  coverage for the actual binary-labeled global trace. Certified growth
  survives sparse skipped incidences and weaker stage inputs; disjoint
  invocation induction handles every stage and terminal edge. No global
  residual-unit premise replaces this concrete coverage proof.

- `Networks/BinaryRankFactors.lean`: genuine projector ranks count exact
  all-column binary vector factors in either edge direction. Isometric
  coordinate transport preserves the rank and the coordinate-label operator.
  One fixed kernel list works for every column count. Ordered trace lists
  retain each edge identity and the aggregate rank count; scalar-kernel or
  tape costs and physical instruction placement are separate.

- `Networks/ComplexPhaseBudget.lean`: the actual h=25 complex-network edge
  list has one finite family of binary kernel directions valid for every
  column count. Every edge operator is factored and total vector-factor count
  equals its actual rank sum, hence meets the concrete budget and exponent.
  Whole framed execution is supplied by `ComplexFramedExecution`; tape
  compilation remains open.

- `Networks/BinaryColumnFrame.lean`: actual invertible columnwise frames
  have the proved forward and inverse operators for every column count.
  Rational scalar restriction preserves the complex-array functions and
  identifies their exact frame changes with the rank-factor edge operators.

- `Networks/GroupedModuleFrames.lean`: the same grouped compiler acts on
  any module over its scalar ring. Whole-run identities and exact ordered
  instruction-edge extraction preserve the physical label history. Scalar
  circuit equalities, including signed routing, lift by proved coefficient
  rows to arbitrary module values without a freeness assumption.

- `Networks/FramedFactorExecution.lean`: replaces each actual frame-change
  instruction by its certified linear factors on the original physical wire.
  Reversed list execution matches operator product order; whole state runs
  agree and every scalar gate retains its position relative to the others.
  Exact factor count and total length include the fixed scalar gate list.
  These are finite linear-operation instructions, not tape transitions.

- `Networks/ComplexFramedExecution.lean`: instantiates the complete physical
  h=25 rational-scalar network on complex arrays. A fixed family of binary
  directions works at every column count; its placed vector factors execute
  exactly the signed bank exchange conjugated by the actual endpoint frames.
  Total array-instruction length is the rank total plus the fixed scalar-row
  count, and executed vector-factor count meets the budget and exponent.
  Scratch has its prescribed output frame; `ComplexEndpoints` simplifies the
  endpoint corrections to the desired transform. Tape compilation remains open.

- `Networks/TensorTerminalWeight.lean`: tensor coordinates of the actual
  terminal vector are the Cartesian-product indicator of its triple labels,
  so its binary Hamming weight is exactly twenty-seven.

- `Networks/ComplexEndpoints.lean`: explicit input/output character corrections,
  the terminal phase, and signed bank rerouting turn the actual h=25 physical
  network into the full product of forward coordinate kernels on every input,
  including dirty scratch. The lowered instruction run has the same transform
  and a uniform internal vector-factor budget. `ComplexCorrections` supplies
  the correction instructions and kernel expansion; literal tape execution is
  a separate obligation.

- `Networks/NetworkBudget.lean`: sums dimensions of actual physical source
  and sink subspaces, including the empty-data case. At complex ground size
  twenty-five, their totals and the actual role count match the numerical
  parameter certificate. Given the full trace balance and global loss bound,
  the exact rank budget meets the selected complex branching exponent;
  those trace premises are not assumed globally.

- `Networks/SharedPointLabels.lean`: every source span generated by triples
  sharing one point is nondegenerate for the rational form. Its quadratic form
  is exactly the sum of coordinate squares away from that point; the shared
  linear relation proves positive definiteness. Support inclusion gives nested
  spans. These supply frame lemmas for the optimized bit graph; its circuit,
  sharing counts, and frame transfer are separate.

- `Networks/SharedPointMap.lean`: an exact bijection between excluded pairs
  and triples sharing one point proves that the three partial outputs equal
  the original bit-side matrix. Their actual source spans are nondegenerate
  and orthogonal to the target line. Optimized DAG construction is separate.

- `Networks/SharedPointKey.lean`: the upstream common-vertex/vertex-union
  key determines the exact triple support whenever at least two common
  vertices remain. Any sharing between distinct common-point copies lies
  in this branch, so the compressed key cannot merge unequal sums.

- `Networks/DisjointPruning.lean`: an executable backwards ancestor pass
  computes the least parent-closed set containing requested outputs. The
  instrumented run skips inactive additions and preserves every output of
  a valid DAG, with an exact marked-addition count. It retains index
  placeholders; compact physical role allocation and tape costs are open.

- `Networks/DisjointCircuit.lean`: executable addition DAGs carry checked
  disjoint input supports. Structural validation proves actual evaluation is
  the support sum; equal-support interning preserves values and validity.
  The list implementation is reference semantics, without tape-cost claims.

- `Networks/DisjointBuilder.lean`: executable zero-eliding, support-interning
  addition and list totals preserve validity, old references, and values.
  Pairwise-disjoint totals construct the exact support union with at most
  one fewer new nodes than operands, including empty and singleton cases.

- `Networks/DisjointBalanced.lean`: the upstream balanced total with literal
  floor-half splitting and left-before-right DAG construction. Zero elision,
  support interning, exact sums and preservation are verified with at most
  one fewer new nodes than operands. Construction order matches the source.

- `Networks/DisjointExclusion.lean`: executable prefix/suffix sharing builds
  all leave-one-out sums. Each output has exactly the support and value of
  the original list with that position removed; all old references survive.
  The constructed DAG adds at most three nodes per input. This variant does
  not certify the upstream allocation order or optimized certificate count.

- `Networks/DisjointPaired.lean`: a shared DAG batch builder using balanced totals computes the
  weighted paired-exclusion base-case queries: total, all single omissions,
  and all pair omissions. Ordered output values and supports, old-reference
  preservation and a sum-of-query-lengths node bound are proved. Recursive
  coarse-graph assembly and exact optimized counts remain separate.

- `Networks/PairedPartition.lean`: actual weighted-graph source supports
  partition into coarse vertex weights, crossing edges and remaining-vertex
  strips. Single, same-pair and cross-pair exclusions reconstruct by disjoint
  unions; finite-sum identities match the script's addition grouping.
  These justify recursive builder additions, without assuming partitions.

- `Networks/PairGrouping.lean`: literal consecutive-pair slicing has exact
  ceiling-half length, covers the original list, and gives nonempty disjoint
  groups of size at most two for distinct inputs. The coarse recursive call
  strictly decreases after the size-four base case.

- `Networks/SupportInterpretation.lean`: expanding weighted source atoms
  into original input supports preserves disjoint partitions and finite sums,
  including empty weights required by initial graph vertices.

- `Networks/PairedCircuit.lean`: full executable upstream paired-exclusion
  recursion, with the literal balanced-total, prefix/suffix, coarse graph,
  strip, and reconstruction order. Two sums the script builds but never uses
  are skipped: a strip's carry omission (and its suffix total), and the
  small-case total from scratch, which is now assembled last from the last
  vertex's single exclusion. Every used sum is unchanged. Termination follows
  from actual pair grouping. `PairedBlockCorrect` proves its complete
  recursive semantics; optimized counts remain separate.

- `Networks/PairedVectorCorrect.lean`: the literal prefix-first, suffix-second
  vector builder preserves the DAG and produces the exact total and each
  omission over arbitrary commutative additive monoids. It adds at most
  three nodes per operand and preserves prior values. The strip variant
  `vectorTail` omits the carry's own omission and has the same guarantees
  for every later omission.

- `Networks/PairedGraphSpec.lean`: ordered graph/table invariants and a
  semantic contract for recursive results, including exact query supports
  and preserved references. The literal small-block branch satisfies the
  complete contract; state-threaded balanced query loops are verified.

- `Networks/PairedCoarseSupport.lean`: actual paired groups classify fine
  sources into disjoint coarse vertex/edge cells that cover the graph.
  Excluding coarse indices excludes exactly their fine vertices, with
  domain validity and looplessness proved from the actual ordered keys.

- `Networks/PairedCoarseCorrect.lean`: both literal coarse construction
  passes establish the full recursive input invariant, with valid disjoint
  DAG references and exact interpreted source-cell supports. Canonical
  lookups, crossing queries, internal weights and persistence are proved.

- `Networks/PairedQuerySupport.lean`: actual table-filter queries equal
  interpreted fine sources avoiding the removed vertices. The source
  domain is loopless and contained in its vertex set; crossing queries and
  the weighted reconstruction partitions have their required disjointness.

- `Networks/PairedCoarseQuery.lean`: actual coarse table queries contract
  to fine-source exclusions. A correct recursive call supplies exactly the
  fine total, outside and far references needed for reconstruction, with
  the original graph invariant preserved at its returned DAG.

- `Networks/PairedStripCorrect.lean`: literal carry, balanced edge totals,
  prefix/suffix omissions and the entire strip loop are valid DAG extensions.
  Exact total and keyed omission supports are anchored in original operands;
  executable strip lookup retains those semantics after later extensions.

- `Networks/PairedStripSupport.lean`: the original graph invariant supplies
  every strip operand's validity and disjointness. Actual full and omitted
  strip queries expand to precisely the source strips used by reconstruction,
  with the remaining vertex weight retained and the selected group excluded.

- `Networks/PairedCircuitCorrect.lean`: literal single-output and nested
  cross-pair loops preserve the shared DAG and produce exact keyed support
  tables. The left partial sum is allocated once and shared through the
  inner loop, retaining the upstream constructor order.

- `Networks/PairedReconstructionSupport.lean`: the actual fine graph and
  contracted coarse outputs discharge all local reconstruction requirements.
  Executable strip lookups, single exclusions, reused within-group outputs
  and cross-pair loops give exactly the original graph's query supports.

- `Networks/PairedReconstructionKeys.lean`: literal group-member enumeration
  returns the original vertices, and internal pairs followed by cross pairs
  are a permutation of all original pairs. These list identities require no
  sortedness assumption and account for the actual output table order.

- `Networks/PairedBlockCorrect.lean`: full correctness of the literal weighted
  paired-exclusion recursion by strong induction, with no assumed recursive
  result or checker acceptance. Every total, single and pair output has its
  exact support and weighted value; the DAG remains valid and every prior
  reference retains its value. Optimized node counts and tape costs are open.

- `Networks/PairedInitialGraph.lean`: concrete singleton pair inputs in literal
  enumeration order, indexed edge references and zero vertex weights establish
  the full input invariant. The resulting circuit has exact surviving-pair
  output sums for all ordered vertex lists; the actual 49-vertex local circuit
  is unconditionally correct with exactly 1,176 inputs and outputs. Active
  addition, global sharing and physical role counts remain separate.

- `Networks/DisjointUnique.lean`: exact lookup absence, interning allocation
  branches and support uniqueness through smart addition and balanced totals.
  Valid DAG supports are nonempty; nonzero disjoint additions contain at least
  two sources, and equal supports identify valid references in a unique DAG.

- `Networks/DuplicateBudget.lean`: deleting one endpoint of each disjoint
  equal-support match preserves represented supports and saves a node. A
  nontrivial triple sum has at most two common vertices. Concrete domain and
  witness counts are required to instantiate the optimized numerical bound.

- `Networks/SharedPointMatching.lean`: in actual common-point copy families,
  a genuine ordered equal-support pair has exactly its two owners as common
  vertices. Per-copy uniqueness forces distinct discarded endpoints and
  excludes left/right overlap, discharging those counting prerequisites.

- `Networks/MaskDAG.lean`: fixed-width bitmask decoding of source supports,
  with bitwise union, intersection and singleton masks.

- `Networks/MaskSignature.lean`: common and covered vertex summaries of a
  source support; additions intersect cores and union covered vertices.

- `Networks/PairMask.lean`: canonical pair indexing and incident/exclusion
  bitmasks encode exactly the original pairs avoiding specified vertices.
  Decoded masks and weighted sums agree with actual canonical pair queries;
  the 49-vertex specialization supplies the certificate output interface.

- `Networks/DAGAllocator.lean`: literal active-node consumer order and role
  allocation, sharing the first input pivot with the first output, retiring
  other inputs and allocating remaining outputs fresh. The local transition
  produces a valid reversible fanout layout from its live-slot invariant.

- `Networks/DAGAllocatorCount.lean`: actual backward marking gives every
  active node a consumer. Counting real ports proves the executable allocator
  uses exactly active additions plus requested outputs, including repetitions.

- `Networks/DAGAllocatorFrontier.lean`: each real allocation preserves unique
  bounded live slots and consumer keys, with exact creation and retirement.
  This is the invariant used by the complete compiler scan.

- `Networks/DAGConsumers.lean`: actual consumer keys are unique, every active
  addition reads earlier producers, and inactive nodes have no scheduled ports.
  These facts discharge the compiler's scheduling requirements from the DAG.

- `Networks/DAGAllocatorRun.lean`: whole-loop frontier propagation produces
  valid layouts for actual emitted gates. Their scalar instruction lists have
  an executable reverse on arbitrary dirty registers, with no assumed layout
  or externally supplied allocator result.

- `Networks/DAGCompileCorrect.lean`: the complete actual compiler has valid
  shared-pivot gates, all intermediate slots within its role count, distinct
  bounded requested-output slots, and no pending gate-input ports. DAG-value
  transfer is proved in DAGValueTransfer; support-frame nesting remains open.

- `Networks/DAGAllocatorBudget.lean`: pruning cannot increase the number of
  additions, so the actual compiler's roles are bounded by all certificate
  additions plus requested outputs, without requiring a liveness certificate.

- `Networks/DAGValueTransfer.lean`: the actual emitted scalar program computes
  every requested DAG support sum when its distinct physical source slots are
  loaded from input labels and all other roles start zero. Proved by induction
  over the allocator, including pending values, future source initialization,
  source provenance and distinctness; repeated semantic input labels work.
- `Networks/DAGInstructionCount.lean`: exact scalar instruction accounting
  for the actual compiler: instructions plus source slots equal twice active
  additions plus requested outputs. This gives bounds from total additions
  or actual allocated roles, including repeated output requests.
- `Networks/PairedBasePruning.lean`, `Networks/PairedIndexedPruning.lean`: the
  literal recursive 49-vertex constructor, pruned to the ancestors of its
  outputs, has at most 9,813 live additions: the allocation count less the
  unused single exclusions, top strip totals and five dead base sums.
- `Networks/PairedStarCount.lean`, `Networks/PairedStarMatch.lean`: star leaf
  families per local center; a kernel merge of sorted lifted leaf masks counts
  40,256 common stars between copies `c < c'`, with bit-level proofs that equal
  lifted masks are equal lifted leaf sets.
- `Networks/PairedStarPresence.lean`, `Networks/PairedTopStars.lean`,
  `Networks/PairedHubStars.lean`, `Networks/PairedStarFamily.lean`: every
  counted star is stored by the constructor: top strip values, prefixes,
  suffixes, omissions and right cross sums, and at vertex 48 the coarse edges
  of every level and three base single exclusions.
- `Networks/PairedStarNodes.lean`, `Networks/PairedStarShared.lean`,
  `Networks/PairedSharedBound.lean`, `Networks/DAGCompactSource.lean`: the 102
  credited dead additions, star nodes and their endpoint summaries, the 40,256
  genuine duplicate witnesses, and the bound of 450,394 distinct supports for
  the pruned circuit used by replay. Stated for arbitrary circuits and
  specialized at the end, so no concrete circuit is evaluated.

- `Networks/ReversibleFanout.lean`: literal binary gate lists gather a sum
  into a pivot and fan it out. Full dirty-state semantics, reverse-list
  inversion, spectator preservation, exact instruction counts and support
  are proved. The singleton identity correctly has empty instruction support.

- `Networks/SharedPointLift.lean`: injective local pair-to-triple lifting under
  the actual omitted-point embedding; exact common/covered vertex formulas,
  preservation of support cardinality and cross-copy equality from verified
  endpoint signatures. Includes the canonical 49-vertex pair payload.
- `Networks/SharedPointFamily.lean`: the actual fifty-copy family formed from
  the structural local addition nodes has at most 490,650 members before
  sharing. Nontrivial supports, common points and per-copy uniqueness discharge
  the matching theorem's structural hypotheses; the duplicate count is proved
  in PairedSharedBound, with global construction in SharedPointReplay.

- `Networks/DAGReplay.lean`: executable topological import into an existing
  DAG under injective source renaming, interning by exact support. Validity,
  original-node reference alignment, evaluation, support uniqueness and
  addition provenance are proved through the actual scan.
- `Networks/DAGReplayBudget.lean`: for support-unique DAGs the addition count
  equals the cardinality of actual addition supports; replayed additions are
  bounded by the union of old and renamed source supports.
- `Networks/SharedPointOutputMap.lean`: canonical pair inputs cover every
  triple containing a fixed common point, and each lifted local exclusion
  support is exactly the triples intersecting its target in that common point.
- `Networks/SharedPointReplay.lean`: actual fifty-copy global DAG with exact
  58,800 output keys and values, valid references, unique supports and every
  addition support in the structural local family. The support-image bound of
  450,394 implies at most 509,194 compiled roles and 959,588 XOR updates;
  the premise is discharged in Shared50Certificate.

- `Networks/SharedPointExecution.lean`: actual compiled binary scalar program
  computes every common-point partial sum for every target triple containing
  that point. Output coverage, distinct bounded physical output slots and an
  executable inverse on arbitrary states are proved; numerical global bounds
  are discharged by Shared50Certificate and Shared50Finite.

- `Networks/SharedPointOutputIndex.lean`: direct arithmetic index for each
  common-point/pair output, proved to select its actual output record and
  compiled partial sum; no output-list search is needed.
- `Networks/BoundedCircuit.lean`: converts every bounded scalar instruction
  to an actual finite register type, preserving forward/reverse execution
  under restriction and preserving instruction count.
- `Networks/DAGFiniteCompile.lean`: the actual allocator bounds every scalar
  target/source; its finite-register program has exactly the same execution,
  output values and length, with a proved inverse on arbitrary finite states.
- `Networks/Shared50Certificate.lean`: the structural duplicate count discharges
  every finite-count premise: actual additions at most 450,394, compiled roles at
  most 509,194, and at most 959,588 scalar XOR instructions in the same program
  that computes all common-point partial sums.
- `Networks/Shared50Finite.lean`: concrete program on `Fin 509194` with the
  certified instruction bound, exact partial sums at explicit distinct output
  registers, and executable reverse on arbitrary finite register states.
  Global rank-frame assembly and literal tape costs remain open.

- `Networks/DAGFramedExecution.lean`: actual interleaved frame alignments and
  unchanged scalar instructions telescope to initial decoding, literal module
  execution and final trace encoding on arbitrary stored module states.
  Erasing only frame changes recovers the compiler's exact scalar program.
- `Networks/FanoutFrames.lean`: literal fanout alignment and scalar execution
  in a common frame, including identity pivots; support-derived increasing
  labels, nondegenerate endpoints and exact projection-difference ranks.
- `Networks/DAGSupportTrace.lean`: support events erase to the actual compiler
  gates; source initialization and allocator invariants prove every event
  ready, output supports exact, and the forward label trace increasing with
  zero dimension loss. Common-point nodes give nondegenerate edge endpoints.
- `Networks/SharedPointOutputLabels.lean`: lifted exclusion supports have
  exactly the partial-output span, nondegenerate and orthogonal to the target.
- `Networks/Shared50Frames.lean`: the actual shared fifty-copy DAG satisfies
  all forward support-trace premises; exact output labels hold at arithmetic
  output slots. Inverse/complement labels and global rank assembly remain open.

- `Networks/DirtyLinearCircuit.lean`: actual embedded compute/read/uncompute/
  inject schedule restores arbitrary scratch; its shear is the actual linear
  computation on the injected input. Additivity is proved from instructions.
- `Networks/Shared50Dirty.lean`: actual finite source loading and three-output
  readout recover the intersection-one neighbor map; the shared circuit's
  concrete dirty wrapper restores every scratch register. Dense matrix
  wrappers establish semantics, without sparse operation or tape-cost bounds.
- `Networks/Shared50Invocation.lean`: literal twelve-block optimized schedule
  combines the actual shared circuit with the fifty central sums. It performs
  the full identity shear and restores arbitrary side and central scratch,
  retaining spectators. Global stage reuse and frame/rank costs remain open.

- `Networks/DAGComplementTrace.lean`: reverse each actual label assignment
  and complement both endpoints, retaining repeated incidences. Exact endpoint
  restoration, increasing reverse edges, zero loss and nondegenerate complements
  are proved; scalar event reversal equals the compiler's reversed program.
- `Networks/DAGComplementExecution.lean`: physical complementary inverse
  execution retains gate boundaries and identity pivots. Its exact label trace
  is the proved reversed-complement trace, its scalar erasure is the literal
  reverse program, and its frame identity holds on arbitrary module states.
- `Networks/Shared50Exchange.lean`: explicit inverse of the optimized twelve
  blocks, opposite data orientation, and three-invocation local bank exchange,
  all restoring arbitrary side/central scratch and spectators. Inverse matrix
  blocks retain their internal row order; full global placement is separate.

- `Networks/TripleNeighborPermutation.lean`: double counting proves Hall's
  condition for positive regular relations; the exact triple-neighbor degree
  supplies a fixed bijection at h=50 pairing every triple with a neighbor.
  This uses classical finite choice, not the upstream paired-point generator.
- `Networks/Shared50ReuseLabels.lean`: actual stage-one and stage-three tensor
  boundary labels at the selected reuse pairs are nested and nondegenerate.
  The join has zero downward loss and its actual projector rank saves exactly
  125,000 against separate terminal edges. The reused scalar schedule is proved
  in Shared50GlobalCircuit; its complete rank trace remains separate.

- `Networks/DAGSourceRoles.lean`: each actual source entry has a certified
  finite role and actual input-node label, with no fallback value. Repeated
  semantic labels retain their separate physical source locations.
- `Networks/Shared50InitialLabels.lean`: every actual source role starts at
  its source triple's indicator line; nonsource roles start at bottom. The
  complementary reverse ends at the source line's orthogonal complement.
- `Networks/Shared50OutputRoles.lean`: equal partial-output slots identify
  both target and common point; physical slots have their exact arithmetic
  output index, final partial-output span and target-line orthogonality.
- `Networks/Shared50ComplementFrames.lean`: the actual fifty-copy circuit
  has increasing nondegenerate complementary inverse edges, zero reverse loss,
  exact endpoints and the target-line inclusion at every original output.
- `Networks/Shared50StageFrames.lean`: lifts actual forward/complementary
  inverse traces into the stage geometry and future tensor line. Exact edges,
  endpoints, nesting, nondegeneracy, zero loss and physical source/output
  attachments are proved; whole-invocation and global assembly remain separate.
- `Networks/Shared50FiniteTrace.lean`: every actual declared label incidence,
  including identity pivots, fits the certified 509,194-register bank. Finite
  restriction preserves the complete ordered edge list and exact endpoints
  under any stage label lift, without filtering any update.

- `Networks/SparseCircuit.lean`: actual one-source XOR lists between disjoint
  banks, with exact accumulation semantics, instruction count and incidences.
- `Networks/Shared50SparseIO.lean`: copies only actual allocated source slots
  and reads each target's three physical partial outputs. Proves arbitrary-state
  equivalence to the dense matrices, unique source roles, exact gate incidences,
  nonsource preservation and source/readout counts; no zero terms are emitted.
- `Networks/Shared50SparseCentral.lean`: literal gather/scatter incidences are
  precisely each triple's three coordinates. Both lists have 3n XORs and exact
  central-matrix semantics on arbitrary scratch with spectators preserved.
- `Networks/Shared50SparseInvocation.lean`: actual sparse twelve-block program,
  inverse blocks, opposite orientation and three-invocation exchange, restoring
  arbitrary scratch. Exact counts give at most 5,209,540 scalar instructions per
  invocation and 15,628,620 per local exchange at h=50. These are not tape costs.

- `Networks/Shared50GlobalBudget.lean`: explicit padded world with two
  auxiliary banks and 406,321,422,080,000 roles; embeds all certified local
  roles, defines actual rational terminal labels, and proves their total
  dimensions. The existing three-bank world has a different count. Corrected
  rank and branching corollaries explicitly require actual trace balance and
  loss bounds; this file does not prove the reused schedule's rank estimate.

- `Networks/Shared50GlobalCircuit.lean`: actual three-coordinate sparse
  program on the optimized two-bank world. The outer stages share matching
  side and center slots via the neighbor permutation; each stage's placements
  are injective and the middle bank is separate. Every invocation, full stage
  and fixed global program swaps/shears as specified, restoring arbitrary dirty
  scratch. Exact list accounting gives at most 3 × 19,600² × 5,209,540 scalar
  instructions. Projector-rank history and tape costs remain separate.

- `Networks/FramedEmbedding.lean`: injective placement preserves actual
  frame/scalar instructions, scalar erasure and complete module execution.
  Full-register frame identities include exact preservation of all spectators.
- `Networks/BoundedFramedCircuit.lean`: checked restriction of physical
  frame-edge and scalar instructions to a finite bank, preserving module
  execution, scalar erasure and full decode/execute/encode identities.
- `Networks/Shared50FiniteFramed.lean`: actual finite forward and complementary
  inverse physical schedules on 509,194 registers. Every declared incidence,
  including scalar-empty pivots, has a proved bound; scalar erasure is exactly
  the certified finite program or its reverse. Identities hold on arbitrary
  module contents with no initialized-scratch premise.
- `Networks/Shared50FiniteReverseTrace.lean`: complementary reverse updates
  introduce no new roles; finite restriction after any stage-label lift retains
  the exact endpoints and complete ordered edge list without filtering.

- `Networks/Shared50LabeledInvocation.lean`: concrete forward sparse-block
  boundary profiles and unique physical readout owners. Every source/readout
  attachment and all profile nondegeneracy facts are proved, including reused
  scratch entering at the stage-common label.
- `Networks/Shared50InvocationRank.lean`: complete finite forward label
  history includes boundary alignments and every actual middle DAG incidence.
  Exact endpoints, nested nondegenerate edges and loss exactly 2,500 are proved,
  for bottom or common auxiliary input. Physical linkage is proved in Shared50InvocationPhysicalEdges.
- `Networks/Shared50OppositeLabels.lean`: concrete opposite-inverse profiles
  use actual complemented final spans for injection and complemented initial
  source lines for draining; common-frame attachments and nondegeneracy proved.
- `Networks/Shared50OppositeRank.lean`: complete opposite history, including
  the actual finite complementary inverse trace. Common-input endpoints,
  nested nondegenerate edges and exact loss 2,500 are proved; physical linkage
  is proved in Shared50FramedOpposite; global rank assembly remains separate.

- `Networks/FramedBlocks.lean`: Whole-bank frame alignment and scalar-block lifting with exact execution and erasure laws.
- `Networks/FramedEdgeTrace.lean`: Extracts every ordered physical frame change, preserving identity edges and repetitions; extraction commutes with finite restriction and injective placement.
- `Networks/Shared50BlockFrames.lean`: Every actual forward sparse block uses a common frame at its concrete invocation boundary profile.
- `Networks/Shared50FramedInvocation.lean`: Complete physical forward wrapper around the actual finite shared DAG. Exact sparse scalar erasure and frame identity on arbitrary module contents, including dirty scratch.
- `Networks/Shared50PhysicalEdges.lean`: Actual finite forward and complementary inverse middle frame changes equal the ordered support-label traces.
- `Networks/Shared50InvocationPhysicalEdges.lean`: Every frame change of the complete physical forward wrapper equals the corresponding edge of its proved local rank history.
- `Networks/Shared50OppositeBlockFrames.lean`: Common-frame proofs for every actual opposite-inverse sparse block at its concrete boundary profile.
- `Networks/Shared50FramedOpposite.lean`: Complete physical opposite wrapper with literal complementary inverse middle, exact sparse scalar erasure, arbitrary-module frame identity and exact equality to its local rank edges.

- `Networks/Shared50InvocationProjectionRank.lean`: Genuine rational projector-difference matrices certify every actual forward/opposite physical frame change in order. Their actual range ranks telescope with the proved local loss of 2,500, without assumed edge costs.
- `Networks/Shared50GlobalTrace.lean`: Concrete source, stage and sink profiles on the actual reused two-bank world. All four boundary attachments have exact endpoints, nondegenerate increasing edges and zero loss; the reused stage-one/stage-three join uses the actual scratch key.

- `Networks/Shared50GlobalTracePlacement.lean`: Places the actual three local histories on the two-bank physical world, preserving exact local endpoints, edge order, loss 2,500 and nesting; different same-stage placements are disjoint.
- `Networks/Shared50GlobalTraceNondegenerate.lean`: Transports nondegeneracy of every actual forward/opposite local edge through the three tensor coordinate isometries into the common rational cube.
- `Networks/Shared50GlobalTraceStages.lean`: Complete chronological reused-world trace: four boundaries and all three actual invocation stages. Proves exact source/sink endpoints, nested nondegenerate edges and total loss 2,881,200,000,000, with no global trace hypotheses.
- `Networks/Shared50GlobalProjectionRank.lean`: Genuine projector-difference operators for the complete optimized global trace. Their actual range ranks satisfy exact balance, and adding the source correction gives exactly 50,790,175,992,864,000,000 and the strict chosen branching inequality. Signed physical realization is proved in Shared50GlobalShear.

- `Networks/Shared50GlobalFramed.lean`: Literal three-stage physical execution on the actual reused two-bank world. Exact scalar erasure, arbitrary-module frame identity and equality of every ordered physical frame change with the complete global rank trace.
- `Networks/Shared50SignedBoundary.lean`: Actual negative-source first-boundary shear matrices and physical instructions in exact wire order. Their genuine range-rank sum equals the ordinary boundary rank plus the exact source dimension total.
- `Networks/Shared50ShearEndpoints.lean`: Exact global scalar and arbitrary-module routing, plus the actual sink-minus-negative-source projector identity on both data banks and all scratch. Every routed array receives the same full address shear.
- `Networks/Shared50GlobalShear.lean`: Complete signed physical optimized network on arbitrary binary arrays over rational address pairs. Exact scalar erasure and uniform full address shear after data exchange, including dirty scratch; every physical edge has its actual matrix certificate, whose total range rank is exactly the improved budget and satisfies the strict branching inequality. Finite-radix realization and tape costs remain separate.

- `Networks/Shared50OperatorPairs.lean`: Retains both rational operator endpoints of every actual signed physical frame edge. Their ordered differences are exactly the already-counted operator list, and their shear frames are exactly the physical frame pairs.
- `Networks/Shared50ModularOperators.lean`: Chooses a 125,000-coordinate basis for the actual tensor ambient, proves matrix rank equals operator range rank, and applies the existing modular-shear construction to the concrete ordered operators with exact total interchange count.
- `Networks/ModularFrameSchedule.lean`: One good prime simultaneously protects every ordered frame endpoint, difference factorization and extra endpoint matrix. At every prime-power modulus, the actual reduced-frame differences have ordered shear programs with exact rational-rank interchange totals; reduction is through the coprime-denominator subring.
- `Networks/ModularProgramShape.lean`: Each modular edge program reduces one fixed rational instruction list. Operation order and pivots are independent of width, with exactly three times the rank plus four field operations per edge. These counts are not tape steps.
- `Networks/Shared50ModularSchedule.lean`: Instantiates the shared-prime construction with the exact signed physical matrix pairs and all source/sink matrices. One prime works at every radix exponent, the routed endpoint difference remains the identity, and the ordered edge programs have exactly the improved interchange budget. Full modular physical execution is proved in Shared50ModularExecution.

- `Networks/Shared50SignedFramed.lean`: Generic signed first-boundary physical wrapper for any module and initial frame profile. Exact scalar erasure, stored-state routing and ordered physical pairs; the rational wrapper is a definitional specialization.
- `Networks/Shared50ModularExecution.lean`: Full physical optimized network on finite prime-power address arrays, for every exponent at one fixed odd prime. Exact routed full shear on arbitrary data and dirty scratch arrays, exact scalar erasure, and ordered per-edge field programs realizing the actual physical array movements with exactly the improved interchange budget. Tape execution and runtime remain open.
- `Networks/Shared50ModularControl.lean`: Canonical edge-control lists use one chosen prime and fixed rational factorizations, with no new program choices per width. Exact interchange and total field-operation counts, fixed rational instruction shape, admissible endpoints and lower-triangular transform matrices are proved.

- `Networks/Shared50FiniteInterchange.lean`: complete finite address-chunk interchange using the actual optimized modular network between literal pre/post field programs. Every routed array, including arbitrary scratch, exchanges its two coordinate groups; all physical edges have ordered field-program certificates, exactly the improved recursive interchange count, and a fixed rational instruction shape across widths. Pre/post add no recursive interchanges. Tape execution and runtime remain separate.

- `Networks/Shared50CoefficientMachines.lean`: Every transform coefficient in the actual fixed rational interchange schedule has denominator below its chosen prime, derived from actual factorization membership including inverse factors and the negative-identity boundary. Each coefficient therefore has a literal two-tape arithmetic kernel with exact width runtime, halting, source preservation and output equal to the actual reduced matrix entry times the input. Matrix sweeps and payload permutations remain separate.

- `Networks/OrderedAffine.lean`: Refines each lower-triangular matrix transform into descending target rows, with a diagonal scaling followed by individual shifts controlled only by earlier coordinates. Exact execution equals matrix multiplication; invertibility supplies diagonal units, coefficient specialization preserves the fixed operation order, and no new coefficients are introduced. Literal ordered-affine tape routines remain separate.

- `Networks/AffineFieldProgram.lean`: Compiles whole-group triangular transforms to scalar ordered-affine steps while retaining explicit cross-group primitives. Exact run semantics, legality, unchanged recursive interchange counts and specialization by arbitrary coefficient maps are proved; the compiler introduces no extra recursive calls.
- `Networks/Shared50AffineControl.lean`: The actual complete optimized interchange has fixed rational scalar-affine schedules, specialized at every width. Protected inverse factors prove every diagonal scaling is a unit; exact execution realizes every physical edge in its original order and retains exactly the improved recursive interchange budget. Literal tape runtime remains open.

- `Networks/Shared50AffineCoefficients.lean`: Every actual scalar-affine coefficient originates in protected matrix entries or cross-group signs, giving its denominator bound and exact literal arithmetic kernel. Actual scale legality at the chosen prime proves numerator coprimality; the fixed signed numerator/denominator recipe is valid at every prime-power width. No numerator-size assumption or tape-permutation runtime is introduced.

- `Networks/AffineFieldCoordinates.lean`: H-before-D coordinate embedding and exact expansion of nonrecursive field operations to ordered scalar operations, including reflected subtraction as negative-one scaling then earlier-control shift. Proves operation/segment semantics and coefficient-map commutation; recursive interchange excluded.

- `Networks/AffineFieldSegments.lean`: Splits field programs into nonrecursive runs separated by explicit recursive interchange boundaries. Exact flattening and run semantics, original membership and nonrecursive hypotheses for each run, exact recursive-call count, and number of runs are proved. Enables segment compilation without concealing recursive-call obligations.

- `Networks/BinaryRowProgram.lean`: Every invertible binary matrix and genuine binary coordinate equivalence yields a literal finite chronological word of distinct source/target row additions, with exact matrix and basis-change execution; reversing the same word restores coordinates.

- `Networks/BinaryPhaseBasisExtension.lean`: An actual nondegenerate phase-subspace basis extends to a full binary address basis with its original vectors in literal first slots. The generated row-addition word computes the exact bilinear controls, and the original projector phase equals the diagonal phase on those computed coordinates.

- `Networks/BinaryPhaseResidualRowProgram.lean`: Nested nondegenerate binary labels with the existing zero-or-unit residual witness determine their own orthonormal basis and full ambient row-addition word. Its literal first residual-dimension coordinates compute the exact controls, and its diagonal phase equals the original nested projector phase difference; no basis or word decomposition is supplied.

- `Networks/ComplexPhaseRowSchedule.lean`: Every actual fixed complex25 edge internally supplies orientation, transported nondegeneracy, comparable labels and its zero-or-unit residual witness, generating its own ambient row-addition word; the original phase difference retains descending-edge sign and original edge order.

- `Networks/ComplexRecursiveCallSchema.lean`: The actual complex update trace determines occurrence-indexed child calls with original wire roles, ordered residual slots and coordinate-weighted inverse flags, preserving repeated equal edge sites. Each actual chosen residual basis weight combines with the original edge orientation to select the proved signed child transform. Its exact child count equals the proved rank sum and its integer stop predicate matches the manuscript; physical child-header updates, role/return stack and stop-test execution remain separate.

- `Networks/FramedControlSchedule.lean`: Role-preserving zipper attaches field programs to framed edges while retaining every scalar gate and original instruction order, with exact execution under edge realization.

- `Networks/FramedControlShape.lean`: Exact shape forgets only frame operators, retaining edge roles and scalar gates; equal shapes imply identical attached controls, including restriction and renaming.

- `Networks/DAGFramedShape.lean`: Frame-independent instruction shape for forward and complementary DAG schedules, including finite-bank restriction.

- `Networks/Shared50OrderedControl.lean`: Actual Shared50 interleaved rational control with exact routed transpose semantics, original scalar program, exact recursive-call count and certified nonrecursive segments.

- `Networks/Shared50FramedShape.lean`: All actual Shared50 role names, edges and scalar-gate positions are independent of frame realization, proved symbolically without evaluating the huge circuit.

- `Networks/Shared50FixedControl.lean`: One literal rational control list for all runtime widths. Exact schedule equality preserves role names, scalar-gate order, routed transpose semantics and the improved recursive-call count.

## NLogN

Transform, fixed-point, Kronecker and Gaussian resampling mathematics used by the main proof. The Harvey–van der Hoeven recursion itself is not needed: the main proof's packed products only require a multiplier within `m log m (log log m)^c`, which the cost table absorbs, so Schönhage–Strassen (`Schoenhage/`) replaces it. Its 28 recursion-only files (step contract, recurrence, cost model, moduli, power-of-two transforms) were removed; restore them with `git checkout 834ad45 -- IntegerMultBounds/NLogN/CRTMulti.lean IntegerMultBounds/NLogN/Capstone.lean IntegerMultBounds/NLogN/Contract.lean IntegerMultBounds/NLogN/ContractFinal.lean IntegerMultBounds/NLogN/ContractPrep.lean IntegerMultBounds/NLogN/ContractSqrt.lean IntegerMultBounds/NLogN/CostBound.lean IntegerMultBounds/NLogN/CostFinal.lean IntegerMultBounds/NLogN/CostModel.lean IntegerMultBounds/NLogN/ExpCostBound.lean IntegerMultBounds/NLogN/ExpEval.lean IntegerMultBounds/NLogN/JointRecurrence.lean IntegerMultBounds/NLogN/MainParams.lean IntegerMultBounds/NLogN/MainRecurrence.lean IntegerMultBounds/NLogN/MainStep.lean IntegerMultBounds/NLogN/MainTransform.lean IntegerMultBounds/NLogN/ModuliConstruction.lean IntegerMultBounds/NLogN/PowerOfTwoContract.lean IntegerMultBounds/NLogN/PowerOfTwoExact.lean IntegerMultBounds/NLogN/PowerOfTwoExactD.lean IntegerMultBounds/NLogN/PowerOfTwoNumeric.lean IntegerMultBounds/NLogN/PowerOfTwoNumericD.lean IntegerMultBounds/NLogN/PrecisionCheck.lean IntegerMultBounds/NLogN/PrimeSelection.lean IntegerMultBounds/NLogN/Recurrence.lean IntegerMultBounds/NLogN/RecurrenceParams.lean IntegerMultBounds/NLogN/ResamplingOps.lean IntegerMultBounds/NLogN/SmallMultiplierCost.lean` and re-add their imports to `IntegerMultBounds.lean`.

- `NLogN/DFT.lean`: the discrete Fourier transform over an integral domain
  with a primitive root of unity, its linearity, the cyclic convolution
  theorem, orthogonality, double-transform inversion up to the factor `N`, and
  injectivity. This is the algebra behind every FFT multiplier, including the
  `O(n log n)` subroutine; no fast algorithm or rounding analysis is here.
- `NLogN/FFT.lean`: the radix-2 Cooley-Tukey transform as an executable
  recursion on `Fin (2^n)`, proved equal to the naive transform for any `ω`
  with `ω^(2^n) = 1`, with an exact count of `n * 2^(n+1)` ring multiplications
  and additions, i.e. `2 N log₂ N`. Twiddle powers are taken as given and the
  count is of ring operations, not tape steps.
- `NLogN/Kronecker.lean`: the reduction of integer multiplication to digit
  convolution. Acyclic convolution of digit lists evaluates to the product,
  with a coefficient bound; a cyclic convolution of sufficient length equals
  the zero-padded acyclic one; bit strings chunk into base `2^k` digits with
  each chunk below `2^k`, connected to the machine's `binaryValue`. Carry
  propagation of the convolved digits back to bits is not yet implemented.
- `NLogN/FixedPoint.lean`: the radix-2 transform over `ℂ` with an arbitrary
  per-step error of size at most `ε` deviates from the exact transform by at
  most `(2^n - 1) ε`, the exact transform grows by at most `2^n`, a complex
  value within `1/2` of an integer rounds to it exactly, and the product error
  bound. The forward, pointwise, inverse error budget is not yet assembled.
- `NLogN/Carry.lean`: carry propagation from unnormalized convolution digits
  to proper base-`B` digits preserving the value, fixed-width truncation, and
  packing of base `2^k` digits into a most-significant-first bit string of
  exactly `k * L` bits whose `Machine.binaryValue` is the digit value. This is
  the output side of `Machine.outputCorrect`, at the list level only.
- `NLogN/Multidim.lean`: convolution transports along any additive group
  isomorphism, so by the Chinese remainder map a cyclic convolution of coprime
  composite length is a two-dimensional one; the two-dimensional transform
  factors into row and column transforms and satisfies the convolution
  theorem. Higher dimensions follow by iterating; the `d`-fold form is not
  stated.
- `NLogN/ErrorBudget.lean`: the total error of the perturbed forward,
  pointwise, inverse pipeline against the exact one, an explicit envelope
  `5 * 4^n * A * ε`, and the precision statement: `2n + 4 + log₂ A` fixed-point
  bits make the rounded perturbed pipeline return the exact integer vector
  whenever the exact pipeline is integral.
- `NLogN/Pipeline.lean`: the complex FFT multiplier as a function on
  `Fin (2^n)`: inversion of the naive transform, the convolution theorem on
  `Fin`, and the proof that forward transform, pointwise product, inverse
  transform, division by `2^n`, and rounding return exactly the product of two
  digit lists. Exact arithmetic over `ℂ`; the fixed-point version is covered by
  the error budget, and nothing is compiled to tapes.
- `NLogN/Gaussian.lean`: summability of Gaussians over the integers, an
  explicit geometric tail bound, the periodized Gaussian with its periodicity
  and explicit uniform upper and lower bounds, and the Poisson summation
  identity for Gaussians re-exported from mathlib. These are the analytic
  inputs to Gaussian resampling; the resampling map itself is not yet defined.
- `NLogN/MultidimD.lean`: the `d`-dimensional transform on a product of
  cyclic groups, its convolution theorem, orthogonality, inversion up to the
  product of the lengths, and the splitting of the first coordinate into a
  one-dimensional transform of lower-dimensional transforms.
- `NLogN/Multiplier.lean`: the assembled fixed-point FFT multiplier on bit
  strings. With chunk size `k`, transform length `2^m`, and `2m + 4 + k` bits
  of precision, the rounded perturbed pipeline followed by carry propagation
  returns the exact `2n`-bit product for every pair of `n`-bit inputs; the
  parameter choice `m = ⌈log₂ 2L⌉` fits, and the count is `6 m 2^m + 2^m`
  fixed-point complex operations. Chunking, rounding, carries, twiddles, and
  tape steps are not counted.
- `NLogN/Neumann.lean`: the linear-algebra skeleton of the resampling
  inversion. A map `1 + E` with `‖E‖ < 1` has an inverse of norm at most
  `1/(1 - ‖E‖)`; given the resampling identity and a normalized square
  subsystem, the source transform factors as `B ∘ (target transform) ∘ A`
  with explicit norm bounds, and after scaling as `2^γ B F A` with
  `‖A‖, ‖B‖ ≤ 1`; diagonal and coordinate-selection maps have the expected
  operator norms. The analytic hypotheses are not yet discharged.
- `NLogN/Bluestein.lean`: Bluestein's chirp identity for even lengths, in one
  and `d` dimensions: the transform is a chirp multiplication, a cyclic
  convolution with the chirp, and another chirp multiplication, so a
  power-of-two transform reduces to a convolution.
- `NLogN/Approx.lean`: the fixed-point approximation framework. Rounding
  toward zero at `p` bits with its norm bounds, the scaled error of vector and
  map approximations as predicates, error propagation through a map of norm
  at most one, through compositions, through bilinear maps, through rounded
  products, and through slice-wise application in a tensor factor.
- `NLogN/Resampling.lean`: the Gaussian resampling identity, Theorem 4.2 of
  the paper, for all positive lengths `s`, `t` and every `α > 0`: the
  Gaussian-weighted resampling maps `S` and `T` intertwine the length-`s` and
  length-`t` transforms up to the two index permutations. Proved from shifted
  Poisson summation, derived from mathlib's Jacobi theta functional equation.
  Norm bounds on the resampling maps and the inversion of `T` are not here.
- `NLogN/MainReduction.lean`: steps one and three of the paper's recursive
  step. An `n`-bit product is the length-`S` cyclic convolution of its
  `b`-bit digit vectors, with product digits below `2^(3b)`; the scaled
  convolution `w = (u ∗ v)/S` of the `2^(-b)`-scaled digit vectors is
  recovered exactly by rounding `2^(2b) S w'` from any approximation within
  `1/(2 · 2^(2b) S)`, and the rounded list evaluates to the product.
- `NLogN/NormFFT.lean`: the normalized radix-2 transform with abstract
  isometric twiddles over any normed space, its norm bound, linearity, and
  the fixed-point error bound of `n ε` after `n` levels; the complex instance
  equals `2^(-n)` times the plain FFT and packages as an approximation of the
  normalized transform with scaled error `n = log₂ N`, the paper's Lemma 3.2
  over `ℂ`. The synthetic-ring instance is not yet connected.
- `NLogN/FixedOps.lean`: the elementary fixed-point operations. Fixed-point
  numbers at `p` bits are closed under sums and integer scaling and are fixed
  by rounding; a rounded half-sum or half-difference adds at most one unit of
  scaled error, integer scaling multiplies the error, and rounded products
  add two units; the negacyclic product of coefficient vectors satisfies
  `‖ab‖ ≤ r ‖a‖ ‖b‖`, and multiplication by a power of `y` is a signed shift
  of norm one. Bit costs and the bridge to the synthetic ring quotient are
  not here.
- `NLogN/ResamplingNorm.lean`: Lemma 4.5 of the paper in its sharp form: the
  periodized Gaussian is at most `1 + √(π/a)` by comparison with the Gaussian
  integral, so the resampling map `S` has sup-norm at most `1 + 1/α`,
  uniformly in the lengths.
- `NLogN/TensorApprox.lean`: the two-factor case of the paper's tensor
  lemma: slice-wise application along either factor preserves approximation
  error and unit norm, the composed tensor approximation has the sum of the
  errors, and the normalized two-dimensional transform is exactly the tensor
  of the two normalized one-dimensional transforms. The `d`-fold version is
  not written.
- `NLogN/BluesteinApprox.lean`: the error bookkeeping of the paper's
  Theorem 3.1 in one and `d` dimensions: with an approximate chirp of scaled
  error `εa`, an approximate normalized convolution of scaled error `εM`, and
  rounded pointwise products, the Bluestein pipeline approximates the
  normalized transform with scaled error at most `εM + 3 εa + 4`. The
  normalized convolution is bounded and bilinear on unit balls.
- `NLogN/Section5Approx.lean`: the error bookkeeping of the paper's
  Propositions 5.2 and 5.3: a three-fold composition of unit-norm maps has
  the sum of the errors, scaling by a natural number scales the error, so a
  transform factored as `2^γ B F A` is approximated with error
  `2^γ (εB + εF + εA)`; and the forward, rounded pointwise, inverse
  convolution has error `εI + 2 εF + 2`, scaled by the length.
- `NLogN/ResamplingInverse.lean`: Section 4.2 of the paper. The row
  selection `C`, the square subsystem `T′ = C T` with its explicit series,
  the diagonal normalization `D` with `1 ≤ d_ℓ ≤ e^(πα²/4)`, the identity
  `N = T′ D = 1 + E`, and Lemma 4.6: under `α²θ ≥ 1` every entry of `E u`
  is at most `2.01 e^(−πα²θ/2) ≤ 1/2` on the unit ball. The operator-norm
  packaging and the assembly `D N⁻¹ C` are not here.
- `NLogN/TensorApproxD.lean`: the paper's tensor lemma with `d` factors:
  applying approximations coordinate by coordinate preserves unit balls, has
  operator norm at most one, and accumulates the sum of the errors; and the
  normalized `d`-dimensional transform is exactly the tensor of the
  normalized one-dimensional transforms.
- `NLogN/SynthFFT.lean`: the synthetic transform in coefficient form.
  Multiplication by `y^e` in `ℂ[y]/(y^r + 1)` is a signed cyclic shift of
  norm one with the semigroup law and period `2r`; the normalized radix-2
  recursion with shift twiddles computes the synthetic transform exactly,
  is a contraction, and has fixed-point error at most `n ε` after `n`
  levels, the paper's Lemma 3.2 for the synthetic ring.
- `NLogN/ResamplingCLM.lean`: the normalized transform, the two index
  permutations, and the resampling maps `S` and `T` as continuous linear
  operators with `‖F‖, ‖P‖ ≤ 1` and `‖S‖ ≤ 1 + 1/α`; `P_s` is invertible
  for coprime lengths with contractive inverse; the resampling identity as an
  operator equation; and fixed-point approximability of any vector to two
  scaled units.
- `NLogN/NeumannApprox.lean`: the paper's Lemma 4.12. The truncated Neumann
  series of `(1 + E)⁻¹` with `‖E‖ ≤ 1/2` is within `2 · 2^(−K)` of the
  inverse; Horner evaluation with an approximate `E` and per-step rounding
  has scaled error `2(εE + ρ)` uniformly in the number of steps, so `p` steps
  approximate the inverse with scaled error `2(εE + ρ) + 1`.
- `NLogN/ResamplingApprox.lean`: the paper's Lemma 4.9. Restricting the
  resampling series of `S` to the `2m + 1` terms nearest the row centre
  loses at most `(2/α)` times a Gaussian tail, which is below `3/(α 2^p)`
  once `m² ≥ p α²` and `α² ≤ p`; summing per-term fixed-point approximations
  of scaled error `c` gives total scaled error `c (2m + 1) + 3`. The
  per-term evaluation cost is not modeled.
- `NLogN/ResamplingAssembly.lean`: Proposition 4.7(i) of the paper. The row
  selection, diagonal normalization, and off-diagonal part are operators
  with `C T D = 1 + E` and `‖E‖ ≤ 1/2`; any left inverse of `1 + E` has
  norm at most two; and for `s < t` coprime, `α ≥ 1`, and `α²θ ≥ 1`, the
  length-`s` transform factors as `2^(2⌈α²⌉ + 2) · B ∘ F_t ∘ A` with explicit
  `A = S/2`, `B = P_s⁻¹ D J C P_t / 2^(γ−1)`, and `‖A‖, ‖B‖ ≤ 1`.
- `NLogN/SynthConv.lean`: the synthetic ring in coefficient form is an
  associative, commutative, unital algebra on which powers of `y` act by
  shifts; the synthetic transform of a cyclic convolution of ring-valued
  vectors is `t` times the pointwise negacyclic product of the transforms,
  for any `t ∣ 2r`; and for `t` a power of two the inverse transform
  recovers the input up to `1/t`, by the half-period cancellation.
- `NLogN/OffDiagApprox.lean`: the paper's Lemmas 4.11 and 4.8. Restricting
  the off-diagonal series `E` to the `2m` terms with `0 < |h| ≤ m` loses at
  most a geometric tail, below `3/2^p` once `9m ≥ p`; summing per-term
  fixed-point approximations of scaled error `c` gives total `2mc + 3`; and
  a rounded diagonal entry in `[0, 1]` times a unit-ball value has scaled
  error at most four.
- `NLogN/SynthEmbed.lean`: Section 3.2 of the paper. Twisting the last
  coordinate by the `2r`-th roots of unity turns complex cyclic convolution
  of length `r` into the negacyclic product, the twist is an isometry with an
  inverse, and a cyclic convolution on `G × Fin r` for any finite group `G`
  is the `R`-valued convolution on `G` of the twisted slices, which covers
  the `d`-dimensional case.
- `NLogN/SynthConvApprox.lean`: the paper's Proposition 3.4 in one
  dimension over the synthetic ring: the normalized convolution equals
  `t r` times the inverse transform of the `1/r`-scaled pointwise products of
  the forward transforms; the inverse transform is the forward one at the
  negated index; and the pipeline computed with per-level error oracles and
  rounded products has scaled error at most `4n + 2` for `n ≤ 2^p`.
- `NLogN/ResamplingMulti.lean`: Theorem 4.1 of the paper. Rectangular
  tensor products of operators on sup-normed coordinate spaces are defined
  through matrix entries, compose and scale factorwise, and are contractions
  when the factors are; the normalized `d`-dimensional transform is the
  tensor of the one-dimensional ones; hence for coordinatewise coprime
  `s_i < t_i`, `α ≥ 1`, and `α²θ_i ≥ 1`, `F_s = 2^(dγ) · B ∘ F_t ∘ A` with
  `‖A‖, ‖B‖ ≤ 1`.
- `NLogN/SynthMultiD.lean`: the `d`-dimensional synthetic transform over
  the coefficient-form synthetic ring: coordinate splitting into a
  one-dimensional transform of lower-dimensional ones, the convolution
  theorem for any lengths dividing `2r`, orthogonality and inversion up to
  `1/∏ N_i` for power-of-two lengths, and contraction bounds for both
  directions.
- `NLogN/TensorApproxV.lean`: the `d`-fold tensor lemma for arrays with
  values in any normed space, indexed by `Fin`, in square and rectangular
  form: coordinatewise approximations preserve balls, have norm at most one,
  and accumulate the sum of the errors. The rectangular composition law is
  not proved here.
- `NLogN/ResamplingNumeric.lean`: Proposition 4.7(ii) of the paper. The
  numerical `Ã` from truncated Gaussian sums and the numerical `B̃` from the
  permutations, rounded diagonal, Horner-evaluated Neumann inverse with a
  truncated off-diagonal part, and row selection are approximations of
  `A` and `B` with explicit scaled errors, both below `p²` for the paper's
  per-term error seven. The per-term Gaussian evaluations and the clamping of
  the off-diagonal approximation into the unit ball are hypotheses.
- `NLogN/ResamplingMultiNumeric.lean`: the numerical half of Theorem 4.1.
  The rectangular coordinatewise tensor on Chinese-remainder grids preserves
  balls, accumulates the sum of the errors, and agrees with the matrix-defined
  tensor; hence the tensors of the one-dimensional numerical maps approximate
  `A` and `B` with scaled errors `d εA` and `d εB`, alongside the exact
  factorization.
- `NLogN/SynthConvApproxD.lean`: Propositions 3.3 and 3.4 of the paper in
  `d` dimensions. The `d`-dimensional synthetic transform is the tensor of
  the one-dimensional ones, so its coordinatewise numerical version has
  scaled error `∑ log₂ t_i`; the inverse is the forward transform at the
  negated index; and the convolution pipeline with rounded `1/r`-scaled
  products has scaled error exactly `3 log₂ T′ + 2` before the final scaling
  by `T′ r`. Unit-ball preservation of each one-dimensional FFT is a
  hypothesis.
- `NLogN/Clamp.lean`: the radial clamp of a complex number to the unit
  disk, applied coordinatewise, is nonexpansive against every point of the
  ball, so any approximation of a contraction can be clamped into the unit
  ball at no cost in scaled error; with a radius-`R` version. This supplies
  the unit-ball side conditions the composition lemmas require.
- `NLogN/ExplicitNumeric.lean`: the numerical maps with every side
  condition discharged: per-term Gaussian weights rounded to `p` bits and
  multiplied with rounding, the off-diagonal part clamped into the unit
  ball, the Neumann inverse and `B̃` built from them, the synthetic FFTs
  clamped, and the `d`-dimensional synthetic pipeline restated with the
  clamped transforms; the multidimensional resampling tensors then
  approximate `A` and `B` with explicit errors below `d p²` and no
  hypotheses beyond the parameter ranges and the inverse identities.
- `NLogN/OffDiagApproxSqrt.lean`: the paper's Lemma 4.11 window. Under
  `α²θ ≥ 1` the off-diagonal terms decay like `e^(−2π(|h| − 1/2)²)`, so
  truncating to `|h| ≤ m` with `9 m² ≥ p` loses at most `3/2^p`; the clamped
  off-diagonal part, the Neumann inverse, and `B̃` keep their error bounds at
  the window `⌊√p⌋ + 1`, still below `p²`. This window is what makes the
  resampling maps cost `O(T p^(3/2+δ))`.
- `NLogN/NeumannHalved.lean`: the manuscript's Neumann evaluation with no
  clamp. Under `α²θ ≥ 1`, `‖E‖ ≤ 2.01 e^(−π/2) ≤ 0.46`
  (`opNorm_offDiagCLM_le_unit`); halving and rounding the input first keeps
  every rounded Horner iterate in the unit disk when the scaled error of `Ẽ`
  is at most `2^p/25` (`hornerNeumannR_err_unit`, `inverse_approx_unit`), so
  `J̃'` (`resampJNumH`) approximates `J(v/2)` and `B̃₀ = D̃' J̃' C`
  (`resampB₀NumH`) approximates `B₀` with error `24m + 27`, stays in the unit
  disk, and with the window `⌊√p⌋ + 1` has error below `p²` for `p ≥ 13`
  (`approxMap_resampB₀NumH_sqrt`, `errB₀H_sqrt_lt_sq`). This is the form the
  tape machines implement.
- `NLogN/ResamplingManuscript.lean`: Lemma 7.1 with the manuscript's
  numerical maps and no clamps. For `α ≥ 2`, `‖A‖ ≤ 3/4`
  (`opNorm_resampA_le_three_quarters`), so any approximation with scaled
  error at most `2^p/4` stays in the unit disk (`ball_of_approx`);
  `permuted_numeric_manuscript` gives the permutation-left identity with the
  unclamped window sums `Ã` and the clamp-free `B̃₀`, errors below `p²`, and
  both maps sending the unit disk to itself.

## Resampling

- `Resampling/RowSelect.lean`: the row indices of the row-selecting map `C`
  of the resampling interface: `q s t j = [tj/s] = rowIndexNat s t j`
  (`rowIndexNat_eq`), strictly increasing and below `t` (`q_strictMono`,
  `q_lt`), and filtering `range t` by them enumerates them in order
  (`filter_range_eq_map`).

- `Resampling/WindowSum.lean`: the window sums of the machine are the
  numerical map `Ã`: rounding toward zero of a dyadic rational is the
  truncated division (`rho0_div_pow`), one fixed-point term has the
  truncated products as parts (`term_parts`), the truncated window reindexes
  to a range (`sum_Icc_eq_range`, `floor_centre`), and `accumulators_eq`
  shows `resampANum s t m (resampTermNum p s t α) u k` has parts
  `signed accR / 2^(p+1)` and `signed accI / 2^(p+1)` when the weight words
  hold `ρ(2^p·w)` and the input words the numerators of `u`, cyclically
  extended by `m` records.

- `Resampling/OffDiagSum.lean`: the same machine computes the off-diagonal
  map `Ẽ` of the Neumann iteration. With stride one (`s` outputs over `s`
  inputs, `centre_self`) and a zero weight word at each window centre, the
  excluded term `h = 0` contributes nothing (`offDiag_sum_range`), each
  rounded term has the machine's truncated products as parts
  (`round_term_parts`, `term_eq`), and `accumulators_eq` shows
  `offDiagNum m (offDiagTermNum p s t α) u ℓ` has parts `signed accR / 2^p`
  and `signed accI / 2^p`. The line machine now only needs `s ≤ t`.

- `Resampling/TabledMaps.lean`: the numerical maps with supplied weight
  tables. Exact rounding of an exponential cannot be computed in a provable
  time, so the machines use integer tables within two units of `2^p` times
  the weights; each term keeps its error (`termW_err`, `offTermW_err`,
  `diagW_err`), and `permuted_numeric_tabled` gives Lemma 7.1 for `Ã` and
  the clamp-free `B̃₀` built from any such tables (`resampB₀NumW`), errors
  below `p²` and the unit disk preserved. `accumulators_eq_W` and
  `B0Value.b0_value_W` connect the tape machines fed integer tables to these
  maps.

- `Resampling/PiApprox.lean`, `Resampling/ExpApprox.lean`: certified integer
  approximations for the weight tables. `piApprox q K` sums Machin's series
  with exact floored terms `⌊2^q/((2k+1) m^(2k+1))⌋` and is within
  `20K + 40·2^q·5^-(2K+1)` of `2^q π` (`piApprox_err`, from
  `arctan_tail` and Mathlib's `four_mul_arctan_inv_5_sub_arctan_inv_239`).
  `expApprox X q N` sums Taylor terms each obtained by one multiplication and
  one truncated division, within `N e^|x| + 2^q |x|^N/N! e^|x|` of
  `2^q e^x`, `x = X/2^q` (`expTerm_err`, `exp_tail`, `expApprox_err`).

- `Resampling/WeightTable.lean`: the integer weight tables. `expPi` computes
  `2^p exp (∓π a/b)` from `piQ ≈ 2^(5p) π`, `Y = ⌊P a / b⌋`, a `7p`-term
  Taylor sum and a `4p`-bit shift, with a shortcut to zero when the negative
  exponent is below `-p`; it is within `3/2` (`expPi_neg_err`,
  `expPi_pos_err`, `p ≥ 13`). `tableA`, `tableE`, `tableD` (with `rr`, the
  integer form of `s β`) are within two units of `2^p` times the Gaussian,
  off-diagonal and `D'` weights, and `tableD ∈ [0, 2^p]` (`tables_ok`, for
  natural `α ≥ 2`, `α² ≤ p`).

- `Resampling/WeightNat.lean`: the weight routine in natural numbers, as the
  tape machines compute it. The Taylor terms are `±M_n` with
  `M_{n+1} = ⌊M_n Y/(2^q (n+1))⌋` (`expTerm_neg`, `expTerm_pos`); below the
  shortcut the alternating sum stays positive (`E_close`, `odd_le_even`), so
  `expPi` equals the natural `expPiNat` (even minus odd partial sums, shifted)
  and the three tables equal `tableANat`, `tableENat`, `tableDNat`.

- `Resampling/PiNat.lean`: Machin's sums in natural numbers, as the tape
  machine computes them: iterated quotients `dSeq` (`⌊2^q/m^(2k+1)⌋`),
  nonincreasing terms, even and odd partial sums whose difference is
  nonnegative (`od_le_ev`), and `piN p = 16 A₅ - 4 A₂₃₉` (`piN_eq`).

- `Resampling/TableIdx.lean`: sign-free formulas for the table numerators:
  `(sk − tj)²` with `j = ⌊sk/t⌋ − m + i` splits at `i = m` (`gauss_num`), and
  `rr x = s β(x)` is the centered residue of `t x mod s` (`rr_eq`) with square
  `min(u, s − u)²` (`rr_sq`).

## Swap

Faster interchange of address chunks (§4).

- `Swap/Recurrence.lean`: the arithmetic of the chunk-interchange recurrence.
  A normalized cost satisfying `F (k+1) ≤ a F k + C` with `a ≤ m^τ` is bounded
  by an explicit constant times `(m^k)^τ`, with no case split on the ratio.
  The base-`m` digit pieces of a general width `n ≥ m^k` cost
  `O(n^τ)` in total, with the digit expansion `n = Σ (n / m^j % m) m^j`
  proved. Row padding to a multiple of `W^k ≤ R` stays below `2R`; the
  row-range digit count `⌈k log W / (2 log q)⌉` gives `q^(2ρ) ≥ W^k` and is
  eventually below the width; the least radix-`q` width covering `[2^u]` is
  at most `u` and inflates the range by less than `q`. The lower triangular
  factorization, the rational matrix shear, and the interchange procedure
  itself are separate obligations.
- `Swap/Shear.lean`: the algebra of the rational matrix shear. Field
  programs on two groups `H`, `D` consist of later-field updates `D_j ← D_j +
  H_i`, `D_j ← H_i - D_j`, interchanges of `H_i` with `D_j`, and within-group
  matrix transformations. One interchange and two later-field updates realize
  `H_i ← H_i + D_j`; a pivot list adds `Π D` to `H` for the matrix `Π` with a
  one at each listed position; with `E₁ E₁' = 1` and `E₂' E₂ = 1` the program
  transform `D` by `E₂`, `H` by `E₁'`, pivot, `H` by `E₁`, `D` by `E₂'`
  computes `H ← H + E₁ Π E₂ D` with exactly as many interchanges as pivots.
  A lower triangular transformation equals the strictly descending sequence of
  its coordinate updates, each reading only the original values, and each row
  reads only its own and earlier coordinates. Identities over any commutative
  ring; the modulus choice, the factorization, and tape costs are separate.
- `Swap/LowerTriangular.lean`: Lemma 4.1. Every matrix over a field, square or
  rectangular, is `E₁ Π E₂` with `E₁`, `E₂` lower triangular with explicit
  lower triangular two-sided inverses and `Π` the pivot matrix of a list with
  distinct rows and distinct columns. The elimination keeps finite active row
  and column sets: the topmost nonzero active row and its rightmost nonzero
  entry give the pivot, a square-zero lower triangular column operation clears
  the pivot row, a square-zero lower triangular row operation clears the pivot
  column, the pivot is scaled to one and subtracted, and strong induction on
  the number of active indices finishes. Factors act as the identity outside
  the active sets, which makes the pivot commute with the residual factors.
  The identification of the pivot count with the rank is in `PivotRank`.
- `Swap/PivotRank.lean`: the pivot count of a factorization is the rank. A
  pivot matrix `Π` with distinct rows and distinct columns has entries given
  by list membership, `Πᵀ Π` is the diagonal indicator `D` of its columns, and
  `Π D = Π`, so `rank Π = rank D` equals the number of pivots over any field;
  the invertible triangular factors do not change the rank. Lemma 4.1 is thus
  complete: every matrix over a field factors with exactly `rank A` pivots.
- `Swap/Modular.lean`: Lemma 4.2, the specialization to `ℤ/q^bℤ`. Rationals
  with denominator prime to `m` form a subring of `ℚ`, and `num · den⁻¹` is a
  ring homomorphism from it to `ZMod m`, proved through the integer identities
  behind fraction addition and multiplication and cancellation of coprime
  denominators. Entrywise reduction of admissible matrices preserves products,
  the identity, inverse pairs, lower triangularity, and pivot matrices, so a
  rational factorization reduces to one over `ZMod m` with the same pivots.
  For a finite collection of rational matrices there is an odd prime `q`
  beyond every denominator of the chosen factorizations, and modulo every
  `q^b` each matrix `A` has a shear program computing `H ← H + A D` with
  exactly `rank A` interchanges, all other operations being lower triangular
  transformations and later-field updates. The `O(V)` tape cost of those
  operations is a separate obligation.
- `Swap/Interchange.lean`: the mathematics of Proposition 4.3. The three
  steps `D ← D - H`, `H ← H + D`, `D ← H - D` interchange the two chunks. The
  field programs of `Shear` realize the address permutation `Φ_M` of
  `ShearFrame` for the reduced matrix, so modulo every power of a suitable
  prime every matrix of a finite collection, and every edge of a labeled
  schedule, has a program with exactly its rank in interchanges, the schedule
  total being the sum of the edge ranks. Under the finite shear contract
  `M_out (ρ w) - M_in w = I` and a logical circuit routing role `w` to `ρ w`,
  the framed circuit's physical output at `ρ w` is the full shear of the input
  at `w`, for every wire including scratch roles. The recursion
  `time (k+1) V ≤ s · time k (V / W) + C V` with `s / W ≤ m^τ` gives
  `time k V ≤ K (m^k)^τ V` with an explicit constant. The role-stream split,
  the depth-first fixed-tape schedule, and descriptor processing are tape
  obligations.
- `NLogN/ResamplingPermuted.lean`: §7, resampling with the permutations left
  in the transform. From the explicit factorization `F_s = 2^γ B F_t A` with
  `B = P_s⁻¹ D J C P_t`, moving `P_s` to the left gives the exact identity
  `P_s F_s = 2^γ B₀ P_t F_t A` with `B₀ = D J C / 2^(γ-1)` and `‖B₀‖ ≤ 1`, so
  neither coordinate permutation is executed. The retained frequency
  permutation `Q : j ↦ (-sᵢ jᵢ)ᵢ` of the `d`-dimensional even-length transform
  is a chirp identity with the weighted chirp `exp(π i Σ sᵢ jᵢ² / tᵢ)`, and
  the retained source permutation `R` by coordinatewise units satisfies
  `F R = R⁻¹ F` for any roots, so `R F [(R F u)·(R F v)] = (∏ Nᵢ) (u ∗ v)(-k)`
  in the unnormalized convention. Costs are not here.
- `NLogN/ResamplingPermutedNumeric.lean`: §7, Lemmas 7.1 and 7.2 with their
  numerical maps. Tensoring the permutation-left identity gives
  `R F_s = 2^γ ℬ₀ Q F_t 𝒜` in `d` dimensions with `R = ⊗ P_{sᵢ}`,
  `Q = ⊗ P_{tᵢ}`, `𝒜 = ⊗ Aᵢ`, `ℬ₀ = ⊗ B₀ᵢ`, both tensors contractions. The
  numerical `B̃₀ = D̃' J̃ C / 2` uses the explicit clamped `Ẽ` and no
  permutation; the clamped explicit `Ã` and `B̃₀` approximate `A` and `B₀`
  with scaled errors `(8m+7)/2` and `(24m+23)/2`, below `p²` for `m ≤ p`,
  `p ≥ 13`, and the linewise tensors have errors `d` times these. Costs are
  not here.

## Schoenhage

Schönhage–Strassen multiplication, the fast multiplier used for the packed products.

- `Schoenhage/Transform.lean`: the twisted transform over any commutative
  ring, on lists whose halves stay contiguous as on a tape. A forward layer
  maps a list modulo `X^(2K) - ζ²` to its residues `a₀ + ζ a₁` modulo
  `X^K - ζ` and `a₀ - ζ a₁` modulo `X^K + ζ`, the roots being powers of one
  `ψ` with `ψ^H = -1`; the inverse layer recombines without halving.
  `inv_fwd_mul`: the inverse of the pointwise product of two forward
  transforms is `2^k` times the product modulo `X^(2^k) - ψ^e`.
- `Schoenhage/Level.lean`: one level modulo `2^n + 1` with `n = 2^k M`.
  Operands are cut into `2^k` pieces of `M` bits (the top piece keeps the
  possible bit `2^n`), transformed in `ℤ/(2^N + 1)` with `ψ = 2^(N/2^k)`,
  multiplied pointwise, inverted, divided by `2^k` (a multiplication by
  `2^(2N-k)`), lifted to signed representatives and evaluated at `2^M`.
  `level_correct`: the result is `x y` modulo `2^n + 1` whenever `2^k ∣ N`
  and `2M + k + 1 ≤ N`; the pointwise products are left abstract.
- `Schoenhage/FMachine.lean`: machines whose control is any finite type
  compile to literal programs by numbering states; runs correspond step for
  step, so contracts transfer with the same bound.
- `Schoenhage/Words.lean`: tapes holding lists of binary words, each followed
  by a separator, laid out from cell zero; the abstract tape is a zipper with
  the head at a word boundary. Reading lemmas and writing words at the end.

- `Schoenhage/Stream.lean`: the generic streaming machine. Tape `0` drives:
  for each bit of its current word a finite rule reads that bit and the
  current bit of every other input (or that its word has ended), emits at
  most one symbol and chooses which inputs advance; the other inputs then skip
  to their separators, the rule's flush is emitted, and all inputs step past
  their words. `stream_run`: exact final tapes and heads in exactly
  `time R w ws` transitions; extend mode overwrites the output's last separator.
- `Schoenhage/StreamPrim.lean`: the streaming machine as a word-program
  primitive: inputs step past their current words and the emitted words are
  appended to the output tape (continuing its last word in extend mode).
- `Schoenhage/Cmd.lean`: word programs. Verified primitives placed on chosen
  tapes, sequencing, loops while a tape has a current word, and branches on a
  leading one bit; big-step executions with costs, and `compile_correct`: each
  execution is a run of the compiled literal program within its cost.
- `Schoenhage/Moves.lean`: one-tape primitives with exact runs: rewind to the
  first word, step back over the previous word, erase the whole tape, and
  append fixed words.

- `Schoenhage/Rules.lean`: streaming rules for word arithmetic, least
  significant bit first: copy, constant fill, fit to a width, drop a prefix,
  ripple-carry addition, ripple-borrow subtraction (borrow as its own word),
  halving a unary word, and a delayed marker, each with its exact output and
  value lemmas (`bval`, `bits`).
- `Schoenhage/Ops.lean`: word-program commands on named tapes (streams with
  zero, one or two extra inputs; rewind, back, clear, emit), their exact
  effects, and `Runs` combinators for sequencing, branches and counted loops.
- `Schoenhage/Wp.lean`: weakest preconditions for word programs; `wp_sound`
  and `wp_of_runs` let straight-line correctness proofs unfold symbolically.
- `Schoenhage/Alu.lean`: residue arithmetic modulo `2^N + 1` on a fixed
  64-tape bank: `runs_subMod`, `runs_addMod`, `runs_mulPow2` (`t ≤ N`), each
  from registers into a register with all scratch returned empty and an
  `O(N)` step bound.

- `Schoenhage/Schedule.lean`: the level schedule (`kOf N ≈ (log N − log log N)/2`,
  `nextN N` the multiple of `2^k` above `2M + k + 1`, base case below `2^2047`):
  divisibility propagates down the recursion (`dvd_chain`), the level
  hypotheses hold (`next_facts`), total size grows by `2 + O(1/s)` per level
  (`growth`), the cost recurrence is `O(N log N log log N)` (`cost_le`), and
  `topN m ∈ (2m, 4m]` is a valid top-level size (`topN_facts`, `cost_topN`).
- `Schoenhage/Lists.lean`: word-list fragments on arbitrary tapes (copy,
  skip, append all, copy as many words as a tick tape holds) and register
  moves, with exact effects and linear step bounds.
- `Schoenhage/Butterfly.lean`: the forward butterfly on the 64-tape bank:
  `u` and `v` from the half-block tapes give `u + 2^t v` and `u − 2^t v`
  modulo `2^N + 1` on the output tapes (`runs_bflyF`), within `O(N)` steps.

- `Schoenhage/Iter.lean`: the transform as the tape computes it, layer by
  layer over residues with one unary shift per block (`layerF`, `layerI`,
  `kids`, `shiftsAt`, `fwdIter`, `invIter`).
- `Schoenhage/IterCorrect.lean`: the iterated layers equal the recursive
  transform over `ZMod (2^N + 1)` with `ψ = 2^(N/K)` (`fwdIter_eq_fwd`,
  `invIter_eq_inv`), with value bounds and lengths.
- `Schoenhage/Layers.lean`: the forward pair loop, block split, collection,
  children's shifts and block loop on the 64-tape bank; one whole forward
  layer computes `layerF` and `kids` exactly (`runs_blocksF`).

- `Schoenhage/Recursive.lean`: the whole recursion as a function, step for
  step as the tapes compute it (`ssMul`), and `ssMul_correct`: the result is
  `x y mod 2^N + 1` whenever `2^(kOf N) ∣ N` and `x, y < 2^N + 1`; one level
  with correct pointwise products is `levelOut_correct`.

- `Schoenhage/InvLayers.lean`: the inverse pair loop, complementary shift
  `N - t`, inverse blocks, the shift recomputation from the root (`kids`
  rounds, geometric cost) and the whole inverse transform `invIter` on the
  64-tape bank (`runs_invLoop`).

- `Schoenhage/Split.lean`: a streaming rule that cuts a word into its
  padded pieces as spelled by a ruler word (`output_split_ruler`).
- `Schoenhage/Recomb.lean`: the up-sweep as the tapes compute it, two
  nonnegative shifted sums reduced from their halves, equal to `levelOut`
  (`levelTape_eq`).
- `Schoenhage/LevelTape.lean`: cutting into pieces, the windowed shifted
  sum and the reduction modulo `2^N + 1` on the 64-tape bank.

- `Schoenhage/LevelUp.lean`: one group's up-sweep on tapes, from the `K`
  pointwise products to the level's output word (`runs_upGroup_level`).

- `Schoenhage/LevelDown.lean`: one pair's down-sweep on tapes, both operands
  cut and transformed and the results interleaved into the next batch
  (`runs_downPair`).

- `Schoenhage/Batch.lean`: a whole level's batch on tapes, the down-sweep
  over all pairs and the up-sweep over all groups of `K` products.

- `Schoenhage/BatchMath.lean`: the batched recursion computes `ssMul` pair by
  pair (`upList_nextBatch`).
- `Schoenhage/BaseCase.lean`: schoolbook multiplication modulo `2^N + 1` on
  tapes, for one pair and for a whole batch (`runs_baseBatch`).

- `Schoenhage/Params.lean`: the schedule's parameters in unary on tapes:
  bit length by halving (`runs_sizeLoop`), repeated halving and doubling,
  and the ruler word (`runs_rulerBuild`).

- `Schoenhage/LevelParams.lean`: a level's registers from the unary outer size:
  `kOf N` (`runs_mkK`), the piece size, `2^k` and `nextN N` (`runs_mkMK`).

- `Schoenhage/LevelMk.lean`: all of a level's registers on tapes from
  `pN = ones N` (`runs_mkLevel`): exponent, sizes, ticks, half constant, the
  unit for the inner modulus and the ruler.

- `Schoenhage/Driver.lean`: the level driver's resting state and one full
  level of the down-sweep from rest to rest (`runs_downLevel`), and the whole
  down-sweep over all levels along the size trajectory (`runs_downLoop`).

- `Schoenhage/DriverUp.lean`: the driver's up-sweep: popping a saved size and
  one full level up from rest to rest (`runs_upLevel`), and the up-sweep
  over all saved levels (`runs_upLoop`).

- `Schoenhage/SSMath.lean`: the driver's trajectory computes `ssMul`
  (`upFold_traj`), ends below the threshold with enough fuel (`traj_lt`), and
  satisfies the up-sweep's side conditions (`UpOK_traj`).

- `Schoenhage/SSMain.lean`: the whole multiplier on the 64-tape bank, from
  the operands modulo `2^N + 1` to their product (`runs_ssMain`), with its
  cost along the size trajectory (`ssCost`).

- `Schoenhage/SSCost.lean`: the multiplier's cost within the schedule's
  recurrence (`ssCost_le`) and its `O(N log N log log N)` runtime
  (`runs_ssMain_bound`); exact products below `2^m` (`runs_ssExact`).

- `Schoenhage/Relabel.lean`: word programs moved into a larger bank by an
  injective map of tape names, with the same cost and every other tape
  untouched (`Runs.map`).
- `Schoenhage/SSClean.lean`: the multiplier's final state tape by tape (a
  decidable check shows the tapes it never names are unchanged) and a wipe,
  so it ends with the product alone on its input tape (`runs_ssClean`).
- `Schoenhage/RingBank.lean`, `RingMul.lean`, `RingAlu.lean`: the 91-tape
  bank of the ring product; one product modulo `2^N + 1` between registers of
  its own (`runs_mulStep`); the residue unit switched on and off around
  modular subtraction and addition (`runs_aluOp`).
- `Schoenhage/RingMath.lean`, `RingWords.lean`, `RingDigit.lean`: evaluation
  at `X = 2^W` turns negacyclic products into products modulo `2^(W r) + 1`
  (`ev_ncMul`); offset digits pack signed coefficients and recover them
  (`encode_res`, `decode_pieces`); signed words and truncation toward zero.
- `Schoenhage/RingPack.lean`, `RingUnpack.lean`: one component of a
  polynomial to its residue (`runs_pack`); a residue to truncated output words
  (`runs_unpack`, `outWord_eq`).
- `Schoenhage/RingProduct.lean`, `RingSpec.lean`, `RingProgram.lean`: the whole
  ring product (`runs_ringProd`), its output equal to the truncated
  negacyclic Gaussian product (`outs_eq`), as a literal 91-tape program
  (`ringProgram_spec`) within `O(N log N log log N)` steps (`ringCost_le`).

- `Spec/SignedRingProduct.lean`: the exact statement of the paper's
  `lem:signed-ring-product` on the literal machine model: the `Γ` header code,
  the most-significant-first two's-complement component format, disk grid
  numerators, `Q_p(fg/r)` as output, and the targets `paperTarget` and
  `polylogTarget k`. Definitions only.
- `Spec/SignedRingProductFacts.lean`: the formats mean what they say: `Γ` is
  self-delimiting and the header reads back as `(p, r, w)` (`header_read`);
  component words round-trip and disk grid numerators fit in `w ≥ p + 2`
  bits (`DiskGrid.fits`); disk grid coefficients have modulus at most one.

- `Spec/PointwiseProducts.lean`: the statement of the pointwise-product step
  of `prop:synthetic-convolution` in the paper's formats: the transform header
  (read back by `transformHeader_read`), arrays of contiguous records in the
  retained order, and `Q_p(fᵢ gᵢ / r)` for each pair (`MeetsPointwise`), with
  the paper's and the polylogarithmic time targets. Definitions only.

- `Schoenhage/Reverse.lean`: a two-tape primitive that copies the current
  word reversed as a new word on another tape (`runs_revw`), turning
  most-significant-first words into the multiplier's convention.
- `Schoenhage/RingConst.lean`: every constant register of the ring product
  built on tapes from `p`, `ℓ` and `w` in unary: digit width
  `W = 2^(size (2p + ℓ + 2w))`, size `W 2^ℓ`, ruler, offset words, half and
  rounding words (`runs_constAll`), in `O(W 2^ℓ)` steps.

- `Schoenhage/RingHeader.lean`: the `Γ` header decoded on tapes: a streaming
  rule counts a code's leading zeros, `take` and `drop` cut its digits, and a
  doubling loop turns them into unary (`runs_decodeOne`); the transform header
  gives `p`, `log₂ r` and `w` (`runs_decodeHeader`).

- `Schoenhage/Chunk.lean`: a three-tape primitive cutting the current word
  into pieces of a register's width (`runs_chunkw`).
- `Schoenhage/Seal.lean`: literal one-tape programs turning a raw bit string
  into a sealed word tape and back, placed on any tape of a bank
  (`sealAt_hoare`, `unsealAt_hoare`).
- `Schoenhage/RingBridgeMath.lean`: the ring product's least-significant-first
  output words, reversed, are the paper's record of `Q_p(fg/r)` for disk grid
  operands (`ringOut_records`).
- `Schoenhage/RingRecord.lean`: the loop over record pairs: each record's
  words move in reversed, the ring product runs, its words come back reversed
  onto one output string (`runs_recStep`, `runs_recLoop`).

- `Schoenhage/RingPointwise.lean`: the pointwise-product step on word tapes:
  decode the header, build the constants, cut both arrays into their words,
  multiply record by record and clean up; the output string is the array of
  `Q_p(fᵢ gᵢ / r)` records (`runs_pwCore`), within `pwCost` steps.

- `Schoenhage/RingPointwiseProgram.lean`: the pointwise-product step as a
  literal program in the paper's formats: seal, run the compiled word program,
  unseal, data tapes relabelled to 0–3; it meets the statement
  (`pointwise_meets`) within `pointwiseTime`.

- `Schoenhage/RingPointwiseBound.lean`, `RingPointwiseTarget.lean`: the
  pointwise program's time is `O(T p log (r p) log log (r p))` plus the header
  (`pointwiseTime_le`), so the step meets `pointwisePolylogTarget 1`
  (`pointwise_polylog`).

- `Schoenhage/RingLemmaHeader.lean`, `RingLemma.lean`: the signed ring product
  lemma on its own interface: a decoder for `Γ(p)Γ(r)Γ(w)` within the same
  header bound, the pointwise program's core generalized over its decoder
  (`runs_pwCoreWith`, `pwProg91With_hoare`) and run on one record; it meets
  `Meets` (`ring_meets`) and `polylogTarget 1` (`ring_polylog`).

- `Spec/SyntheticTransform.lean`: the statement of the paper's synthetic
  transforms in its formats: exact counterparts `L B F⁻` and `F⁺ B⁻¹ L⁻¹`,
  per-coefficient error `√2 ℓ 2^(-p)`, disk grid outputs, the paper's cost
  (`MeetsForward`, `MeetsOpposite`, `transformTarget`). Definitions only.
- `Spec/SyntheticTransformFacts.lean`: the conventions are consistent:
  mixed-radix addresses and per-axis bit reversal are bijections, `F⁺F⁻ = I/M`
  (`oppT_fwdT`), and the opposite exact map undoes the forward one in the
  stored order for every layout (`oppExact_fwdExact`).
- `Spec/SyntheticConvolution.lean`: the statement of the paper's synthetic
  convolution: the normalized convolution `ℳ_r(f, g) = (f * g)/(r M)` with cyclic
  address subtraction, error `√2 M (3ℓ + 1) 2^(-p)`, output width `w + log₂ M`
  with `Γ(w_M)` on a descriptor tape, the paper's cost (`MeetsConvolution`,
  `convolutionTarget`). Definitions only.

## MathlibTM2 integration

- `MathlibTM2/Node/CompactSwap.lean`, `Cost/CompactSwap.lean`: Prepared two-field interchange on actual host bit streams, with arbitrary dirty compact fields, preserved spectators and exact register restoration. Runtime is bounded in compact width and total bit volume, with bank-size assumptions explicit. Header production and conversion from the live layer encoding remain separate.
- `MathlibTM2/Node/CompactRotParity.lean`: Seven-register host scanner packs the low bit of each runtime-width block into padded output blocks, preserves the source and parameter registers, and restores scratch with an exact linear step count. This builds an offset word; it does not execute a full compact toggle. `CompactControlCheck.lean` audits the new primitive contracts.
- `MathlibTM2/Theorem.lean`: Unconditional `MathlibTM2.statement` proves that one fixed finite Mathlib machine multiplies every input pair in worst-case time below n log n. The complete host program and actual cost bound are supplied internally, with positive saving `2^-66`. This is the completed route in plan C; the original compact-control target uses the larger saving `83/10^12`.
- `MathlibTM2/Cost/MatchSynLoop.lean`, `Cost/Total.lean`: Assemble the implemented parameter distribution, synthetic transforms and full multiplier, discharge the last transform-loop cost premise, and prove the total-time bound. `Fast/MainCorrect.mn_hostMul_ge` supplies large-input correctness; the finite dispatcher covers short inputs. `CompletedProofCheck.lean` checks the final theorem's three-standard-axiom dependency set.
- `MathlibTM2/Layer/LayerZ.lean`, `NodeZ.lean`, `TopZ.lean`: The contributed scaled Gaussian recursion has unconditional mathematical correctness by induction over children; the normalized top-level function includes phases, padding, piece composition and final truncation. This is a different representation from the native event schedule and its ledger.
- `MathlibTM2/Layer/Recurrence.lean`, `MathlibTM2/Node/Body.lean`, `MathlibTM2/Node/LayerProc.lean`, `MathlibTM2/Node/TopProc.lean`: The recurrence solution and node-body execution now have concrete recursive factor procedures and complete layer/top programs, proved by induction with actual execution costs. The host route is complete; reconciling its parameter choices with the stronger compact-control witness is a separate target.

## Removed modules

Modules the proof does not use, removed after commit `4f27086`; restore with `git checkout 4f27086 -- <file>`.

The 669 modules that neither `MathlibTM2/Theorem.lean` nor any audit or check file imports (old exact chains, native-machine `Machine/` work, `Schoenhage/`, unused `Resampling/` and `NLogN/` pieces) were removed after commit `8fb31454`; restore with `git checkout 8fb31454 -- <file>`.

- Adjacent-interchange axis rotation in `Resampling/AxisRounds.lean`, `ScriptSem.lean` and `Script.lean` (restore from `cb57fa81`): `rot_eq_tr2` (moving the innermost field outward by adjacent interchanges is one block transpose), `rotIn`/`rotOut` with `rotIn_flatten`/`rotOut_flatten`, `swapList_mul`, and the `O(d²)`-interchange script `tScript` with `tScript_spec`; replaced by the linear schedule `Sandwich.sScript`.

- `Machine/BinaryArithmetic.lean`: a fixed three-tape, seven-state adder accepts unequal-width raw words, physically pads and rewinds both operands, then runs binary addition.
- `Machine/BinaryDivideQuotient.lean`: Six-tape physical division followed by quotient normalization.
- `Machine/BlockNegation.lean`: Complete literal seven-tape, 141-state single-fiber coordinate negation.
- `Machine/FiberShiftAddress.lean`: Instantiates the reusable fiber machine as actual forward target-coordinate translation modulo Q on arbitrarily many Q-by-B fibers, preserving every intra-block payload position.
- `Machine/FiberShiftReuse.lean`: Fixed eight-tape, ninety-six-state common-offset fiber shifts with full inner and outer clock cleanup.
- `Machine/FlatCoordinateScheduleSupport.lean`: The verified initialized mixed schedule has private heads and nonblank private cells within its explicit linear-volume runtime interval.
- `Machine/FlatCoordinateShiftInitializedStage.lean`: Fully synthesized controlled shift instantiates the original two-payload Stage interface with exact transform, private input independence and charged setup-inclusive linear cost.
- `Machine/FlatMultiControlTranslation.lean`: Complete physical flat-array translation by a fixed rational expression over actual prefix coordinates.
- `Machine/FlatScaleShiftPair.lean`: Concrete actual-network rational scale followed by controlled shift on the same two physical payload tapes.
- `Machine/MultiControlPrefixTranslationBootstrap.lean`: Complete equal-width multi-control prefix stream from wholly blank writable arithmetic, translation and outer-clock workspace.
- `Machine/MultiControlPrefixTranslationExecution.lean`: Physically evaluates shared-control expression, translates a fiber and advances the actual common prefix fields; old leaf copies and binary result remain explicitly stale until next evaluation.
- `Machine/MultiControlPrefixTranslationInit.lean`: Physically generates every shared radix control field from blank storage using canonical width descriptors, then runs blank-workspace initialization and the complete multi-control prefix stream.
- `Machine/MultiControlPrefixTranslationStream.lean`: Real counted stream of multi-control translations with physical carry scheduling and exact current/stale-field invariant.
- `Machine/MultiControlTranslationBootstrap.lean`: First-use physical shared-source expression evaluation and translation starts all writable arithmetic/translation scratch blank at head zero.
- `Machine/MultiControlTranslationExecution.lean`: Actual shared-source expression evaluation composes with fiber translation using the same physical binary offset tape through static placement.
- `Machine/NegationStream.lean`: Fixed ten-tape, 218-state repeated coordinate negation on uniform fibers.
- `Machine/OffsetPreparationCost.lean`: Every fixed polynomial in radix width is little-o of q^width for q at least two.
- `Machine/RadixDigitMoveExecution.lean`: Complete suffix-one digit movement from sole canonical prefix/spectator descriptors and arbitrary payload.
- `Machine/RadixDigitMovePlacement.lean`: Fixed injective placements compose count synthesis and redistribution while preserving original descriptors and spectator tapes.
- `Machine/RadixDigitMovePrepared.lean`: Exact forward and inverse fixed-radix digit permutation for prepared canonical controls, with physically rewound payload and erased private storage.
- `Machine/RadixDivide.lean`: Literal two-tape fixed-denominator modular division using RadixUnary, with exactly d carry states and one transition per digit.
- `Machine/RadixFieldReadList.lean`: Physically reads literal delimited role fields into their private marked arithmetic controls, retains source symbols, advances every real separator and proves the exact control bank and runtime.
- `Machine/RadixLinearCombinationReuse.lean`: Recurring shared-bank expression evaluation physically erases the old binary output and refreshes all stale leaf copies.
- `Machine/RadixScale.lean`: Literal two-tape fixed-coefficient modular scaling using RadixUnary.
- `Machine/RadixScaleData.lean`: Fixed-natural-coefficient scaling with coefficient+1 bounded carry states.
- `Machine/RadixSub.lean`: Literal three-tape, two-state fixed-radix subtraction.
- `Machine/RecursiveBaseBranch.lean`: Actual digit-role base machine bound into the physical width controller.
- `Machine/RecursiveCleanDescriptorDivision.lean`: The complete clean descriptor divider has runtime at most (1280*A^2+1920*A+710) times logical child volume for canonical root-bounded inputs, A=log2 roles+2.
- `Machine/RecursiveDescriptorFrames.lean`: Actual fixed-list descriptor push/pop and same-bank roundtrip charged to logical child volume using canonical root-bounded header lengths.
- `Machine/RecursiveDescriptorStack.lean`: Connects the actual delimiter-based binary push/pop roundtrip to the recursive descriptor-size theorem.
- `Machine/RecursiveQuotientDivision.lean`: Physical division-plus-normalization runtime bounded by (40*A^2+58*A+9) times logical child volume, where A=log2 roles+2, for canonical root-bounded descriptors.
- `Machine/RecursiveWidthBranch.lean`: Actual fixed three-block finite flow selects supplied base or recursive block from the physical guard, with at most three charged transitions.
- `Machine/RunSupport.lean`: Actual transition induction bounds head displacement and changed cells by elapsed transitions, with exact preservation of all exterior cells.
- `Machine/ScalingInverseStream.lean`: Actual repeated inverse-unit scaling over uniform fibers with fixed control and shared restored scratch.
- `Machine/ScalingPreparedStream.lean`: Once-only piece-descriptor synthesis from blank work followed by actual repeated positive-unit scaling.
- `Machine/StreamedFiberTranslationInitializedAlphabet.lean`: Executes the complete blank-private-storage streamed rotation on any larger finite alphabet with literal input/output banks and unchanged483-volume-plus35 cost.
- `Machine/TranslationOffsetReplace.lean`: Places literal descriptor replacement on the translation offset tape and a physical scheduler-output tape, preserving arbitrary additional workspace.
- `NLogN/NegacyclicKronecker.lean`: the paper's Lemma 2.5 in exact arithmetic.
- `NLogN/Synthetic.lean`: principal roots of unity, transform inversion over an arbitrary commutative ring from the principal-root property alone, the synthetic ring `ℂ[y]/(y^r + 1)` with `y^(2r/t)` a principal `t`-th root for every power of two 
- `Networks/ComplexCorrections.lean`: the endpoint corrections as literal single-wire instructions around the lowered h=25 factor program.
- `Networks/Paired49Execution.lean`: the checked local witness's emitted program computes all 1,176 pair-exclusion sums with at most 10,989 scalar roles; superseded by `SharedPointExecution`.
- `Networks/PairedReconstruct.lean`: the script's actual three smart additions reconstruct a cross-pair exclusion from concrete far, strip and cross supports; one smart addition reconstructs a single exclusion.
- `Networks/PairedUnique.lean`: every literal paired constructor and the full recursive block preserve support uniqueness.
- `Networks/SharedPointIntern.lean`: executable compressed-key lookup among addition nodes and conditional interning preserve DAG validity and exact values over any commutative additive monoid.
- `Swap/ArbitraryWidth.lean`: the cost assembly of Lemma 4.4.

## Top-level

Parameters and asymptotics.

- `Asymptotics.lean`: logarithmic powers are little-o of every strictly larger
  real power, specialized to all seven assembly margins; a finite-depth,
  volume-normalized recurrence bound with explicit leaf and overhead costs.
- `Parameters.lean`: every stated rational parameter slack, all seven assembly
  margins, their attained minimum and strict absorption gap, the two dyadic
  comparisons, the complex motif counts, and the strict complex branching-ratio
  bound. The logarithm enclosure is proved from a finite exponential-series
  lower bound inside Lean. These do not establish the motif's circuit interface
  or the costs of an implementation. Module-scoped imports and separate
  rational goals allow the full parameter file to pass the guarded local check
  without increasing memory or proof limits.
- `Shared50Parameters.lean`: exact h=50 two-bank counts, positive deficit,
  finite exponential-series logarithm enclosure and strict branching inequality
  for the selected tau. Converting the numerical budget into an actual circuit
  bound still requires its proved rank balance and loss estimate.
- `TimeBound.lean`: the complete time bound of §8 as a statement about cost
  functions. With precision `p = 6 lg n`, which is at least `6`, tends to
  infinity, and is at most `12 log n / log 2`, a dominant row
  `C V (log p)^k p^e` with `e < 1 - κ` and volume `V ≤ cV n` is eventually at
  most `C cV 6^(1-κ)` times the target time `n (lg n)^(1-κ)`; a setup cost
  `D p^A` and a cost `D V φ(p)` with `φ` eventually bounded are eventually
  fixed multiples of the target time as well. Finite lists of such rows sum to
  `C n (lg n)^(1-κ)` for all large `n`, and the seven table rows with
  exponents `1 - margin i` instantiate this at `κ = 83 / 10^12`, the exponent
  of `Machine.EndToEnd`. The row costs themselves, and the translation of the
  size parameters `d, K, ℓ, r` into powers of `p`, are supplied by the
  components and remain open.
- `Sizes.lean`: the input and transform sizes of §8. From `b = lg n`, with
  `2^(b-1) < n ≤ 2^b` and `b ≤ n`, the number of axes `d = ⌊b^ε⌋` satisfies
  `1 ≤ d ≤ b` and `d ≤ p^ε`, and eventually `p^ε / 12 ≤ d`; the chunk width
  `K = ⌊d^c⌋` with `c = spacing` satisfies `K ≤ p^(εc)` and eventually
  `p^(εc) / 24 ≤ K`; the transform length `T = 2^⌈log₂ (4n/b)⌉` lies in
  `[4n/b, 8n/b)`, so `24 n ≤ T p < 48 n` for every `n ≥ 1`; eventually
  `b / 2 ≤ log₂ T ≤ b`, hence `p / (12 d) ≤ ℓ ≤ p / (3 d)` for
  `ℓ = ⌈log₂ T / d⌉`, and the axis length `r = 2^ℓ` is at least
  `2^(p^(1-ε) / 12)`. These are the comparison constants `a_d = a_r = 1/12`,
  `b_d = 1`, `b_r = 1/3` of the layer and transform interfaces.
- `ExactRecovery.lean`: precision and exact recovery (§8, the final integer
  coefficients). With computed source and opposite transforms within scaled
  error `E_s` of the exact contractions on the half ball and the pointwise
  product truncated to the grid, quarter-ball inputs keep every computed
  array in the disk and the computed opposite transform is within
  `(3 E_s + 2) 2^(-p)` of `G (F u · F v)`. Through the convolution identity
  `G (F u · F v) = (u ∗ v) / S²`, the numerator scaling `16 S` returns the
  normalised convolution of the digit vectors within `16 S (3 E_s + 2) 2^(-p)`,
  and the rounding recovery of `MainReduction` gives the exact product once
  `2^(2k+4) S² (3 E_s + 2) < 2^(p-1)`. With `E_s = 9 · 2^γ T L`, `S ≤ T < 2^k`,
  `L < k`, `γ ≤ k/4` and `p = 6k`, both margins follow from
  `896 k 2^(k/4) < 2^k`, which holds for all large `k`. Tape costs are not
  here.

- `MathlibTM2/Node/CompactSetup.lean`, `Node/CompactSlotRun.lean`: The compact slot XOR on Mathlib TM2 from its unary inputs: 41 setup stages fill the index fields, masks, counters and interchange headers (`cxSetup_exec`), `cxCore` moves the records, and the cleanup restores every register except the stream (`cxSlotRun_exec`).
- `MathlibTM2/Node/CompactSlotCost.lean`: The slot XOR costs `O(M (L + B) max(1, (k - 1) G)^τ)` on `M` records of index length `L` and record length `B`; bad repair records are paid by the late repair density.
- `MathlibTM2/Node/CompactGeometryRecursive.lean`: Shared-shape child reservation invariant and the live selected-bit embedding.
- `MathlibTM2/Cost/CompactSlotPacking.lean`: The parameter conditions of the compact slot operations (`CompactSlotPacked`) from dyadic guards, and eventually from the actual multiplier sizes.
- `MathlibTM2/Fast/CompactSynRecArithmetic.lean`: Runtime ceiling division and front/back/active/offset reservation arithmetic with exact costs and scratch restoration. Row-axis count is an explicit input; recursive record production remains separate.

- `MathlibTM2/Fast/CompactSynRecRows.lean`, `Fast/CompactSynRecPieces.lean`, `Fast/CompactSynRec.lean`: Separate checked executions compute the exact native row-axis reservation and front/back counts, emit active digit pieces and the back leaf, and restore all temporary counters with exact runtime costs. Actual row padding, top configuration, fallback and coverage remain separate.
- `MathlibTM2/Fast/CompactSynSel.lean`: Validity at a sufficient common row depth and exact exponent sum for the reserved piece records; no assumed execution and no claim of completed transform coverage.

- `MathlibTM2/Node/CompactEncodingOffset.lean`: Literal encoding reshape absorbs arbitrary low address spectators into coefficient payloads, with shifted slot-action compatibility and exact volume preservation.

- `MathlibTM2/Fast/CompactReservationGeometry.lean`, `Fast/CompactSynCoverage.lean`: Literal runtime reservations determine a common shape for digit pieces and child slots. Exact offsets, pre-padding volume and complete selected-coordinate coverage are proved under explicit capacity premises; execution of the new top configuration remains separate.

- `MathlibTM2/Fast/CompactSynRows.lean`: Rebase piece row metadata to exact quotients of the actual padded row count without changing serialized records. Native divisibility and original-axis depth discharge shared-row validity.

- `MathlibTM2/Fast/CompactSynRecRoot.lean`: Concrete original-input composition of exact row-axis calculation, reserved piece production and scratch cleanup; its generic internal composition is discharged by actual executions.
- `MathlibTM2/Fast/CompactTopRows.lean`: Actual top-level row padding includes outside rows and high spectators, is at most twice original row stock, and validates the rebased piece records using the single global divisor.

- `MathlibTM2/Fast/CompactTopSelection.lean`: Exact selected-coordinate permutation, nonduplication, padded-piece validity and exponent sum.
- `MathlibTM2/Fast/CompactTopConfigFields.lean`, `Fast/CompactTopConfigWrite.lean`, `Fast/CompactTopConfigPadding.lean`, `Fast/CompactTopConfigDivisor.lean`, `Fast/CompactTopConfigRows.lean`, `Fast/CompactTopConfig.lean`: Runtime global divisor and exact padding, ten-field configuration serialization and working width, with source restoration. Derived original-input coordinates remain caller work.
- `MathlibTM2/Cost/CompactCallerParameters.lean`: Eventual repair packing from manuscript sizes, explicit reservation/row/width premises; runtime size-generator identification remains separate.

- `MathlibTM2/Cost/CompactCallerRows.lean`: Actual padded top-row and descendant-quotient bounds, paying one exponent bit for padding; the combined outside-row/spectator allowance remains explicit.

- `MathlibTM2/Fast/CompactTopReady.lean`: Exact selection mask/length, computed shift, piece-width validity and reserved top-transform semantics. This is mathematical correctness; actual compact layer replacement remains separate.
- `MathlibTM2/Cost/CompactCallerRuntimeParameters.lean`: Repair packing directly for the running integer-root size generator, without equating its dimension/chunk with the manuscript regime.
- `MathlibTM2/Cost/CompactCallerCapacity.lean`: Actual reservation cutoff, eventual fractional-dimension bounds and capacity for nonterminal synthetic rounds. Small selected sets retain a capacity/fallback obligation.
- `MathlibTM2/Node/CompactBasisSlot.lean`, `Node/CompactBasis.lean`: Low-offset compact slot operations by the Mathlib slot XOR from the descriptor registers, within `compactBasisSlotCost`; list composition realizes the exact basis map with restored frame and summed costs. Concrete register wiring remains separate.

- `MathlibTM2/Fast/CompactTopCoordinates.lean`, `Fast/CompactTopSetup.lean`: Actual original-input root record and top-coordinate computation, regenerating cleared reservation counts and restoring all intermediates. The configuration serializer role adapter remains separate.

- `MathlibTM2/Node/CompactBasisRegisters.lean`: Concrete finite compact register bank, persistent global reservation predicate and layer-counter aliases; actual basis execution changes only its selected wire. Factor/layer and top-wrapper integration remain separate.

- `MathlibTM2/Fast/CompactTopOriginal.lean`: Complete original-input piece/configuration/working-width constructor, including role adaptation and cleanup. Arbitrary persistent outside-row source and every input/scratch tape are restored.
- `MathlibTM2/Cost/CompactCallerSelectedRows.lean`: Exact selected top split, native-row identity, padded descendant bound and actual repair packing from original address/row precision premises.

- `MathlibTM2/Cost/CompactBasis.lean`: Complete computed-slot and basis costs bounded by actual local volume times compact width to `tau`, including quadratic descriptor arithmetic, seed/header/native execution and cleanup, with fixed power-of-two coefficients.
- `MathlibTM2/Node/CompactFactorBasis.lean`, `Node/CompactFactor.lean`: Complete compact factor program and exact factor contract, replacing both basis calls while restoring persistent globals; recursive child execution remains the existing `CallSpec` induction boundary.

- `MathlibTM2/Node/CompactLayerProc.lean`, `Node/CompactLayerGeometry.lean`: Complete actual compact recursive layer and closed call contract; child geometry follows from the root layout, with local packing and numeric basis-budget obligations explicit.
- `MathlibTM2/Cost/CompactFactor.lean`, `Cost/CompactFactorActual.lean`: Full non-child factor overhead at compact-width local volume, fixed power-of-two coefficient and child coefficient one.
- `MathlibTM2/Node/CompactTopProcRegs.lean`, `Node/CompactTopProcCall.lean`, `Node/CompactTopProcKernel.lean`, `Node/CompactTopProcLeaf.lean`: Generic persistent-bank top registers, actual field reads/call cleanup/kernel; the top leaf kernel's call contract is discharged by actual execution.
- `MathlibTM2/Node/CompactRegisterEmbedding.lean`, `Fast/CompactTopPlaced.lean`: One fixed union bank shares ordinary registers and separates private banks; actual original-input setup executes on it with unchanged cost and no procedure-table assumption.

- `MathlibTM2/Node/CompactLayerPlaced.lean`: Actual recursive layer on the shared union host, preserving exact costs and every caller register except the output stream.
- `MathlibTM2/Node/CompactTopProcRows.lean`, `Node/CompactTopProcPieces.lean`, `Node/CompactTopProcStages.lean`, `Node/CompactTopProc.lean`: All seven actual top stages, including padded recursive piece processing, with exact transform and normalized butterfly semantics. Generic per-layer call contracts remain the assembly boundary.
- `MathlibTM2/Cost/CompactLayer.lean`, `Cost/CompactLayerReady.lean`: Canonical proved compact basis budget, actual layer-cost majorant recurrence and recursive readiness without arbitrary cost premises.
- `MathlibTM2/Fast/CompactTopPrecision.lean`: Original numerator bounds imply input fit and intermediate fit at the exact computed working width.

- `MathlibTM2/Cost/CompactLayerNormalized.lean`: Exact per-volume recurrence, original level-zero leaf term and compact-width basis ratio; address-to-payload overhead remains explicit.

- `MathlibTM2/Fast/CompactPieceGeometry.lean`, `Fast/CompactTopExecution.lean`: Actual reserved piece layouts, offsets and kernel extent, plus full top execution on the concrete placed compact layer. Recursive readiness and primitive layout parameters remain explicit at this interface.
- `MathlibTM2/Cost/CompactPiecePacking.lean`: Uniform descendant packing and canonical recursive readiness from original address/row precision, runtime size bounds and primitive guard/record inequalities.
- `MathlibTM2/Cost/CompactLayerBound.lean`: Closed normalized layer recurrence with a fixed power-of-two coefficient, compact-width charge and retained leaf term; full top summation and caller cost propagation remain separate.
- `MathlibTM2/Node/CompactBasisSetupCounts.lean`, `Node/CompactBasisSetupPlacement.lean`: Actual persistent reservation arithmetic and injective placement into the seven shared-host work registers, preserving source roles.

- `MathlibTM2/Cost/CompactCallerShape.lean`: Actual runtime sizes imply shared-shape guard positivity, guard room and record capacity uniformly in selected dimensions and low offsets; only reservation capacity and original runtime row/width lower bounds are required.

- `MathlibTM2/Cost/CompactTopBound.lean`: Geometric summation over actual digit records without a logarithmic piece-count factor, and exact decomposition of executable top costs into retained control work, top kernel and recursive calls.

- `MathlibTM2/Node/CompactBasisSetupFrame.lean`, `CompactBasisSetupOutput.lean`, `CompactBasisSetup.lean`: Actual shared-host persistent-bank initialization from original source words with exact seven-register output, preserved sources, restored scratch and unchanged execution costs.

- `MathlibTM2/Cost/CompactTopControlBound.lean`: Actual full-array phase scans and final unit multiplication have linear volume bounds under explicit address/payload conditions; configuration reads and unary headers remain charged separately.

- `MathlibTM2/Fast/CompactTopRuntimeExecution.lean`: Actual runtime top execution derives all recursive readiness and primitive shape conditions internally from original precision, runtime sizes and reservation capacity, with the prepared machine state explicit.
- `MathlibTM2/Fast/CompactSynRoundSources.lean`: Actual chunk-round stride, phase and current low-offset production from the existing round counters, with empty scratch and a preserved compact bank on the union host.

- `MathlibTM2/Cost/CompactInterimParameters.lean`: Exact conditional compact-integration candidate with dyadic chunk/dimension constants and saving `2^-37`; all five listed stage margins cover it, while the old full-width internal inequality is proved to fail. This is parameter arithmetic, not a stronger public machine theorem.
- `MathlibTM2/Cost/CompactTopRowControlBound.lean`: Linear actual-volume bounds for row reshaping and padding/unpadding, including unary counters and discarded rows.
- `MathlibTM2/Fast/CompactMainRegs.lean`: One fixed expanded main-host register family, injective old-main and compact-transform placements, shared actual source stream and private-bank separation. The public multiplier has not switched hosts.
- `MathlibTM2/Node/CompactBasisSetupRest.lean`, `CompactBasisCleanup.lean`: Persistent reservation rest invariant and actual exact cleanup.
- `MathlibTM2/Node/CompactGlobalBootstrapCounts.lean`, `CompactGlobalBootstrap.lean`: Actual original-precision guard/dimension setup from copied unary sources, preserving source roles and clearing input copies.
- `MathlibTM2/Node/CompactBasisRefreshPlacement.lean`, `CompactBasisRefresh.lean`, `CompactBasisRefreshRest.lean`: Actual five-field per-round refresh, restored temporary outputs, preserved original guard/dimension and proved rest invariant/cleanup.
- `MathlibTM2/Fast/CompactSynRoundGlobal.lean`, `CompactSynRoundRest.lean`, `CompactSynRoundRegs.lean`, `CompactSynRoundPark.lean`, `CompactSynRoundCompose.lean`: Checked individual round stages and register/frame bridges for global reads, rest setup/teardown, stashing, configuration push/drop, unstashing and sequential composition. Full chunk-round composition remains separate.

- `MathlibTM2/Cost/CompactTopRecordBound.lean`, `CompactTopBlockBound.lean`: Header bounds derived from actual piece validity, complete dispatch and record-erasure costs, and full padded-block control including all reshaping/padding/cleanup.
- `MathlibTM2/Cost/CompactTopOverhead.lean`, `CompactTopControlVolume.lean`: Every nonrecursive top stage is charged by `2^14 * (pieceCount+1) * paddedVolume`, with actual geometry and word-width conditions explicit.
- `MathlibTM2/Fast/CompactMainBootstrapRead.lean`, `CompactMainBootstrap.lean`: Actual named original precision/dimension copies and persistent bootstrap on the expanded main host with exact costs and final register file.
- `MathlibTM2/Fast/CompactSynLayerStepFrame.lean`, `CompactSynLayerStepSources.lean`, `CompactSynLayerStep.lean`: Actual source setup and cleanup contracts plus the complete round program definition. Whole-round execution is checked in `CompactSynLayerStepExecution`; main transform integration remains separate.

- `MathlibTM2/Cost/CompactTopPieceCount.lean`, `CompactTopControlPower.lean`: Actual reserved record count is logarithmic in original dimension; complete actual top control work is absorbed into any positive dimension power with a fixed dyadic coefficient.
- `MathlibTM2/Cost/CompactTopCoordinates.lean`: Exact translation from absolute serialized piece offsets to relative layer offsets, preserving rebasing, validity, row stock and total volume.
- `MathlibTM2/Fast/CompactMainBootstrapFrame.lean`, `CompactMainConstants.lean`: Original source/copy frame facts for the actual bootstrap and a fixed state capacity covering original and compact native programs; main pipeline state transport remains separate.
- `MathlibTM2/Node/CompactBasisRefreshInput.lean`: Derives actual per-round refresh source projection from a blank refresh bank.
- `MathlibTM2/Fast/CompactSynLayerStepProjection.lean`, `CompactSynLayerStepWires.lean`, `CompactSynLayerStepRecords.lean`, `CompactSynLayerStepRefresh.lean`, `CompactSynLayerStepClear.lean`: Concrete source/record/refresh execution, frame projections and source-copy cleanup from the original round invariant.
- `MathlibTM2/Fast/CompactSynLayerStepPrepare.lean`, `CompactSynLayerStepBasis.lean`, `CompactSynLayerStepPark.lean`, `CompactSynLayerStepCleanup.lean`, `CompactSynLayerStepSeq.lean`: Complete actual preparation and parking, derived basis invariants, exact final cleanup and cost-preserving sequential reassociation. Whole-round execution is checked in `CompactSynLayerStepExecution`; main transform integration remains separate.

- `MathlibTM2/Cost/CompactTopActualBound.lean`, `CompactTopAbsoluteBound.lean`, `CompactTopCompleteBound.lean`: Complete actual top-transform cost, including the reserved recursive-call sum, widened kernel and all controls, in one shared padded-volume envelope.
- `MathlibTM2/Cost/CompactTopOriginalBound.lean`, `CompactTopOriginalVolume.lean`, `CompactTopOriginalGeometry.lean`: Concrete serialization, input restoration and unary row-padding costs; reserved address geometry pays the row-division budget. Record construction and original-divisor setup remain separate.
- `MathlibTM2/Host/StateTransport.lean`, `StateLift.lean`: Exact host execution transport along a local-state injection/retraction and to a larger finite state capacity; an explicit one-step normalization admits arbitrary larger-capacity states without changing stacks or user data.

- `MathlibTM2/Fast/CompactSynLayerStepReady.lean`, `CompactSynLayerStepTopRegs.lean`, `CompactSynLayerStepRuntime.lean`, `CompactSynLayerStepUnpark.lean`, `CompactSynLayerStepCompose.lean`, `CompactSynLayerStepAlgebra.lean`, `CompactSynLayerStepCost.lean`, `CompactSynLayerStepExecution.lean`: Complete actual compact chunk round from the original synthetic state and persistent globals, through preparation/top execution/restoration/cleanup. Returns the original full register file with only transformed I/O and charges every stage; main transform integration remains separate.
- `MathlibTM2/Cost/CompactTopRecordSetupBound.lean`: Checked polynomial costs of both row reservation scans, reservation arithmetic, active/back descriptor construction, coordinate setup, and original row-divisor computation.
- `MathlibTM2/Cost/CompactTopOriginalRuntime.lean`: Actual integer-root multiplier sizes pay the unary row-division budget for selected intervals at least one chunk long.

- `MathlibTM2/Host/StatePlacement.lean`, `Fast/CompactMainTransport.lean`: Combined finite-state/register transport and concrete read/parameter/pointwise/round/output wrappers on the expanded main machine, with a disjoint old/compact procedure table, one charged entry normalization, exact original I/O projection and untouched compact private bank.
- `MathlibTM2/Host/WordTape.lean`: word tapes on host stacks (namespace `Host.WordCmd`): a word tape on a register keeps the cells from the head on on the right stack and the cells left of the head, nearest first, on the left stack (`place`; `regs` for raw stacks); single-step actions (`actThen`, `mv1`, `scanAll`) and the one- and two-register loops (`moveLR`, `moveRL`, `dropR`, `copyLoop`) with exact step counts. `HostSpec 3 n pre sem cost prog`: on any injective register family of any host with `n ≤ Q`, `prog` takes the placed tapes to those of the effect within `3 (cost + 1)` steps; `HNoCalls`: it makes no procedure calls. Rewind, back, clear and emit (`rewind_hostSpec`, …).
- `MathlibTM2/Host/WordCmd.lean`: word programs on host stacks. Every primitive carries its host implementation (`Prim.prog`, `Prim.hspec`, `Prim.hcalls`), so `tcompile ι c` compiles a word program with no multitape machine in between; `tcompile_exec`: for `cmdStates c ≤ Q`, an execution of `c` within `k` steps is a host execution between the placed banks within `3 (k + 1)` steps; `tcompile_noCalls`.
- `MathlibTM2/Host/WordStream.lean`: the streaming primitive on host stacks (`stream_hostSpec`, the rule's state in `st`, `card R.Q` control states): per driver bit one host action records the inputs' tops, moves the further inputs the rule advances, emits, steps the driver and enters the next rule state (`bitStep_run`, `bitLoop` against `Strm.go`); then the further inputs skip to their separators in parallel (`skipLoop`), the flush is emitted and every input steps past its separator. `2 n + 2 rest + 5` steps against the cost `time`.
- `MathlibTM2/Host/WordCopy.lean`: reverse (`reverse_hostSpec`, `6 n + 8` steps) and chunk (`chunk_hostSpec`, at most `12 n + 8` steps) on host stacks; `chunkPush_cut`: the bits with a separator after each completed piece and after a final partial one are the symbols of `cut W x`.

- `MathlibTM2/Fast/CompactSynLayerStepSemantics.lean`, `CompactSynLayerStepStream.lean`: The actual compact round selects the original physical butterfly coordinates and produces the original synthetic butterfly stream, with exact full-register restoration except I/O.
- `MathlibTM2/Cost/CompactTopOriginalCompleteBound.lean`: Complete original-input constructor cost, including records, divisor, coordinates, serialization and restoration, bounded by `2^17*(G+m+1)*B^7 + 2^13*V`; scalar budgets are explicit and the division budget follows from geometry.

- `MathlibTM2/Fast/CompactMainLayer.lean`: Canonical compact native procedure table and actual chunk program on the combined main host; checked round contracts transfer at identical cost and restore the entire main file except its original source-array stream.

- `MathlibTM2/Fast/CompactMainBootstrapPipelineFrame.lean`, `CompactMainBootstrapPipeline.lean`, `CompactMainBootstrapPipelineGlobals.lean`, `CompactMainBootstrapPipelineExit.lean`, `CompactMainBootstrapPipelineSource.lean`, `CompactMainBootstrapPipelinePrecision.lean`, `CompactMainBootstrapPipelineCompose.lean`: Once-per-transform original-input bootstrap, charged correction of initial `d-1` to retained original `d`, actual distribution/parameter source provenance, preserved globals and exact charged exit cleanup.
- `MathlibTM2/Fast/CompactMainBootstrapRuntime.lean`: Bootstrap globals supply the exact original dimension and guard words expected by runtime chunk execution; actual round I/O updates preserve the entire private bank and initialized globals.
- `MathlibTM2/Fast/CompactSynCompare.lean`, `CompactSynDispatch.lean`, `CompactMainLegacyRuns.lean`, `CompactSynDirect.lean`, `CompactSynMainProjection.lean`, `CompactSynHybridRound.lean`: Actual reversible counter selector, transported direct rounds and complete hybrid round with original butterfly stream semantics. Both branch executions are derived internally; only chunk rounds require reservation capacity.
- `MathlibTM2/Cost/CompactCallerFullDimension.lean`, `CompactCallerWorkingWidth.lean`: Actual initial dimension `d-1` pays the compact reservation and a chunk; actual working precision is at most twice caller precision.
- `MathlibTM2/Cost/CompactRuntimePolynomial.lean`, `CompactRoundVolume.lean`: Fixed polynomial setup charges fit the actual coefficient count with dyadic volume coefficients; actual padded working volume lies between the original stream volume and four times that volume.
- `MathlibTM2/Cost/CompactSynLayerOverheadBound.lean`: Every actual round-overhead stage and actual record/configuration length is charged, giving `2^18*(G+m+1)*B^7 + 2^14*V + 2*stash` under explicit scalar geometry budgets.
- `MathlibTM2/Cost/CompactSynLayerOverheadRuntime.lean`: Complete actual round overhead is at most `2^15*V + 2*stash` once the common scalar budget is polynomial in actual precision; derives both setup absorption and `B≤V` from the actual coefficient count.

- `MathlibTM2/Fast/CompactSynRoundFrame.lean`, `CompactSynLayerContract.lean`, `CompactSynTwiddle.lean`, `CompactSynRound.lean`: Stable original globals, hybrid layer contracts and actual forward/opposite rounds, including charged transported twiddle normalization and exact original stream semantics.
- `MathlibTM2/Fast/CompactSynLoopBody.lean`, `CompactSynLoopCost.lean`, `CompactSynScanFrame.lean`, `CompactSynLoopFStep.lean`, `CompactSynLoopOStep.lean`, `CompactSynLoopF.lean`, `CompactSynLoopO.lean`, `CompactSynLoopsContract.lean`: Complete actual counter-driven scans in both directions, with original forward/opposite semantics, restored counters and full-register frame except output.
- `MathlibTM2/Fast/CompactSynInitialGeometry.lean`, `CompactSynInitialContract.lean`, `CompactSynInitialLoops.lean`, `CompactSynLayoutTransport.lean`: Actual distributed-transform geometry and canonical main-table loop contracts, plus exact transported layout execution.
- `MathlibTM2/Fast/CompactMainBootstrapView.lean`, `CompactMainBootstrapTransformFrame.lean`, `CompactMainTransformPipeline.lean`: Derive bootstrap execution from real precision/depth sources and blank scratch; preserve the synthetic view, establish runtime readiness, and compose a core with charged setup/exit to restore the whole original file except output.
- `MathlibTM2/Cost/CompactCallerScalarBudget.lean`, `CompactCallerDivisorPolynomial.lean`: Common quadratic precision bounds for actual caller fields and a dyadic polynomial bound for the original row divisor; final combined overhead specialization remains separate.
- `MathlibTM2/Mult/CompactSizes.lean`, `Cost/CompactCallerRetunedCapacity.lean`: Parallel eighth-root chunk sizes and monotone reservation capacity between the original and larger chunk sizes. Executable retuning and the stronger total-cost theorem remain separate.

- `MathlibTM2/Fast/CompactSynFwd.lean`, `CompactSynOpp.lean`, `CompactSynTransformPre.lean`, `CompactSynFwdSpec.lean`, `CompactSynOppSpec.lean`, `CompactSynInitialTransforms.lean`, `CompactSynConcreteTransforms.lean`: Complete concrete forward/opposite transform specifications on the expanded main host, with original numerical/error semantics, actual initial parameters and existing layouts. Charged bootstrap/core/exit restore all non-output registers; final eventual contracts require no execution, layout or readiness oracle.
- `MathlibTM2/Cost/CompactCallerCombinedBudget.lean`: Combined dyadic scalar/divisor polynomial budget, derived actual piece validity and complete overhead bounded by `2^15*V+2*stash`, uniformly for larger chunk sizes and explicitly for eighth-root chunks.
- `MathlibTM2/Cost/CompactCallerUniformReadiness.lean`, `CompactPieceUniformPacking.lean`, `Fast/CompactTopUniformRuntimeExecution.lean`, `CompactSynLayerStepUniformRuntime.lean`: Uniform shared shape, selected row and descendant repair packing; actual recursive top execution from refreshed/parked files, for every chunk size between the legacy chunk and original dimension.
- `MathlibTM2/Cost/CompactCallerGuardPower.lean`, `CompactCallerLayerGrowth.lean`: Actual precision guard bounded by a dyadic coefficient times any positive original-dimension power; the full guard factor in the closed compact layer recurrence fits the proposed layer exponent gap.

- `MathlibTM2/Fast/CompactParamProg.lean`, `CompactParamPipeline.lean`, `CompactDistRetune.lean`, `CompactDist.lean`: Charged eighth-root parameter-slot overwrite and actual distribution wrapper; all other table fields, outputs and cleared scratch are preserved.
- `MathlibTM2/Fast/CompactDistWires.lean`, `CompactDistWiresExec.lean`, `CompactBundleMnLay.lean`: Actual retuned synthetic wire initialization and executable layout bundle; chunk, block counts, twiddle positions and layout permutation consistently use the eighth-root size.
- `MathlibTM2/Fast/CompactSynLayerStepUniformExecution.lean`, `CompactSynLayerStepUniformStream.lean`, `CompactSynUniformHybridRound.lean`, `CompactSynUniformLayerContract.lean`: Full actual chunk execution, original stream semantics and hybrid layer contracts uniformly for larger chunks.
- `MathlibTM2/Fast/CompactSynUniformRound.lean`, `CompactSynUniformLoopCost.lean`, `CompactSynUniformLoopFStep.lean`, `CompactSynUniformLoopOStep.lean`, `CompactSynUniformLoopF.lean`, `CompactSynUniformLoopO.lean`, `CompactSynUniformLoopsContract.lean`: General chunk-size round and complete scan contracts, reusing the existing programs and preserving their exact frames and costs.
- `MathlibTM2/Fast/CompactSynUniformFwd.lean`, `CompactSynUniformOpp.lean`, `CompactSynUniformTransformPre.lean`, `CompactSynUniformFwdSpec.lean`, `CompactSynUniformOppSpec.lean`, `CompactSynUniformTransforms.lean`, `CompactSynRetunedGeometry.lean`, `CompactSynRetunedTransforms.lean`: Complete actual eighth-root forward/opposite transforms with concrete initial wires and layouts; final eventual specifications quantify only the canonical legacy main-program parameter and derive geometry, loop execution and layout execution internally.
- `MathlibTM2/Fast/CompactSynMainFrame.lean`, `CompactSynMainEntry.lean`, `CompactSrcMachine.lean`, `CompactSrcFrame.lean`, `CompactSrcBase.lean`, `CompactSrcStages.lean`, `CompactSrcMainStages.lean`: Expanded source-machine placement, source-stage framing and entry from the original main/distribution invariant; actual source forward/opposite stages with exact costs. Expanded main-chain assembly remains separate.
- `MathlibTM2/Cost/CompactRetunedReservationGrowth.lean`, `CompactRetunedTopGrowth.lean`, `CompactRetunedTopCost.lean`: All original reserved axes fit every dimension exponent above seven eighths; the actual complete top program, recursive calls, widened kernel and controls obey the proposed compact layer exponent, with fixed dyadic coefficients and concrete address-geometry premises.

- `MathlibTM2/Cost/CompactGrowth.lean`, `CompactStageGrowth.lean`, `CompactTotal.lean`: Eighth-root chunk growth and complete analytic stage envelope at saving `2^-37`; the final runtime theorem requires an actual execution-cost match.
- `MathlibTM2/Cost/CompactRetunedCallerSlack.lean`, `CompactRetunedCallerTopCost.lean`: Actual caller capacity slack and address specialization of the complete recursive top-cost estimate.
- `MathlibTM2/Fast/CompactBdRetune.lean`, `CompactBdWiresCost.lean`, `CompactBundleWires.lean`: Executable retuned distribution bundle and dyadic costs from the original distribution precondition.
- `MathlibTM2/Fast/CompactSynRetunedMainFrame.lean`, `CompactSynRetunedMainEntry.lean`, `CompactSynRetunedDistributionEntry.lean`: Actual distribution establishes placed retuned transform entry; forward/opposite specifications preserve the main frame.
- `MathlibTM2/Fast/CompactMainCalls.lean`, `CompactMainEntryTable.lean`: Restricted-call execution transport allows replacement of the main entry while preserving both recursive layer tables.

- `MathlibTM2/Cost/CompactRetunedDirectCost.lean`: Actual full-dimension chunk-layer cost with caller obligations discharged, and actual retuned direct-branch costs matched to the compact convolution envelope.
- `MathlibTM2/Fast/CompactMainTransformCalls.lean`, `CompactSynRetunedEntrySpecs.lean`, `CompactSrcRetunedFrame.lean`, `CompactSrcRetunedStages.lean`: Full retuned source transforms under an arbitrary expanded main entry, with restricted-call transport, preserved source frame and exact stage costs.
- `MathlibTM2/Fast/CompactMainPrimitiveRuns.lean`: Legacy source primitives transported into the expanded host with preserved private bank and one charged normalization step.
- `MathlibTM2/Fast/CompactMainTimeGlue.lean`, `CompactMainTimeBound.lean`: Aggregate unchanged primitive costs with supplied expanded source costs and symbolic host cleanup; fixed normalization overhead is absorbed, yielding the stronger asymptotic bound conditional on the source-run cost match.

- `MathlibTM2/Cost/CompactRetunedLoopMatch.lean`: Actual compact/direct round costs and both loop sums fit the retuned convolution envelope with an explicit stash budget.
- `MathlibTM2/Fast/CompactSourceCost.lean`, `CompactMainRunsCost.lean`, `CompactMainRunsTime.lean`: Expanded-host source core and forward/opposite costs; all three source runs and full main-cost envelope yield the stronger asymptotic bound once complete transform costs are matched.

- `MathlibTM2/Fast/CompactMainStableFrame.lean`, `CompactMainSourceLift.lean`, `CompactMainSourceStages.lean`: Main-chain invariant stable under main-register changes, and placed source stages that recover their precision source at entry.

- `MathlibTM2/Cost/CompactRetunedLayoutMatch.lean`, `CompactRetunedStashMatch.lean`: Complete concrete forward/opposite costs, including layouts, actual stored wires, original-source bootstrap, loops and cleanup, fit the retuned convolution envelope without supplied stage-cost hypotheses.
- `MathlibTM2/Fast/CompactMainPrimitiveEntry.lean`: Original primitive executions and call support transported under the replaced main entry, preserving private registers with one charged normalization step.
- `MathlibTM2/Fast/CompactMainDispatch.lean`, `CompactRetunedMainBound.lean`: Concrete full-time estimate at saving `2^-37` and final finite-machine packaging, conditional only on eventual execution within that estimate; public multiplier theorem remains unchanged.

- `MathlibTM2/Fast/CompactMainChain.lean`: Complete fifteen-stage retuned arithmetic chain with exact source-stage costs, twelve wrapper steps and original coefficient-output contract, checked under default proof limits.

- `MathlibTM2/Fast/CompactMainParamCalls.lean`, `CompactMainDistributionCalls.lean`, `CompactMainInputDistribution.lean`: Actual input, parameter and retuned distribution execution under the final recursive table, with one normalized entry and no call-support premise.
- `MathlibTM2/Fast/CompactMainRunsAt.lean`, `CompactMainChainExec.lean`, `CompactMainChainEntry.lean`, `CompactMainCoefficients.lean`, `CompactMainOutput.lean`: Concrete distributed-state entry to the full arithmetic chain, exact source-cost identity, coefficient correctness and canonical binary output.
- `MathlibTM2/Fast/CompactMainCleanup.lean`, `CompactMainHost.lean`, `CompactMainPrefixCost.lean`, `CompactFinal.lean`: Complete private-register cleanup, finite push bound, exact prefix accounting and unconditional `MulInTime (2^37)⁻¹`, now exported by the public theorem.

- `MathlibTM2/Cost/CompactLogGrowth.lean`: Dimension-independent dyadic bounds for binary logarithms and the Schönhage–Strassen polylogarithmic overhead, with logarithmic loss `2^-5`; integration into resampling costs remains separate.

- `MathlibTM2/Layer/LayerR.lean`, `NodeRSharp.lean`, `TopRS.lean`, `TopRFit.lean`, `Mult/SynthErrRoundsQ.lean`, `PipelineQ.lean`, `Fast/SrcStageG.lean`, `Fast/CompactMain*R.lean`, `Fast/CompactFinalR.lean`, `Cost/*R.lean`: Rounded synthetic layers (per-level truncation, sharp error, shrunk top), computed rounds within `√2(1+1/16)/2^p`, the pipeline for any box convolution with `BoxConvSpec`, the main chain on the rounded box stage and its costs needing only `d² ≤ b`. `compactR_mulInTime_final` proves unconditional `MulInTime (2^33)⁻¹` at `epsilon=9/32`, exported by the public theorem; axiom audit passes.

- `MathlibTM2/Mult/CompactDyadicRootRoom.lean`: Checked universal squared-cap fit in `4*b+32` bits for the sixty-fourth root of `b^9`, plus seventh-power dimension room. Arithmetic groundwork only.
- `MathlibTM2/Fast/CompactDimensionPower.lean`: Five-atom table program computes `b^9`, preserves input and accumulator, and proves exact word-fit and execution contracts.
- `MathlibTM2/Fast/CompactDyadicDimension.lean`: Checked composition computes `iroot 64 (b^9)` with charged cost `58+44*iroot 64 (b^9)`, preserving input and accumulator. Actual parameter allocation and changed sizing definitions remain separate. Both executable helpers pass a focused standard-axiom audit.

- `MathlibTM2/Mult/CompactDyadicPrecision.lean`: Seventh-power size room supplies modulus inequalities for `d≥2` and the exact-recovery gamma guard for `d≥64`. These and the candidate width passed a 19-declaration standard-axiom audit; no new multiplier bound is asserted.

- `MathlibTM2/Fast/CompactDyadicParamStageCore.lean`: Candidate dimension stage on the forty-variable parameter table, preserving all other parameters and accumulator, clearing borrowed scratch, within the previous dimension-stage allowance. The generic core stays below ParamProg in the import graph.

- `Networks/BinaryScalarReplay.lean`: Binary masks denote linear forms on arbitrary stored inputs; checked XOR, singleton, source-fold and row-update theorems connect symbolic replay to actual scalar circuit gates. All five semantic lemmas pass the standard-axiom audit; concrete supplier endpoint certificates remain separate.

- `Networks/Certificates/PR589/{Scalar,D,A,B,C,scatter,Word,FirstCheckpoint,Semantics}.lean`: Deterministic import of the pinned selected 5583-gate scalar word, preserving frame metadata, with generic binary-replay soundness and a kernel-checked first-four-gate prefix. All 6119 declarations pass the standard-axiom audit. Full-word restoration, framed semantics, nesting and charged machine execution remain open.
- `scripts/generate_pr589_scalar.py`: Hash-pinned literal-data importer with deterministic regeneration; external exact dirty-column replay validates source ingestion, while only explicit checked Lean prefix certificates establish formal endpoints.

- `Networks/FramedEventTrace.lean`: A checked literal sequence of frame-label changes and scalar gates executes exactly as its erased scalar word between the initial/final frame encodings, for arbitrary dirty stored values. Decidable event validity supports finite certificates; all three semantic theorems pass guarded checking and the standard-axiom audit. Concrete T16 trace validity and frame interpretation remain separate.

- `Networks/Certificates/T16/` charge and owner tables: removed 2026-10-18 (restore from 3b3911b0^). `Layer/SelectedMoments` now derives the per-call rank profile from the native traces (`Trace.forwardEvents`/`backwardEvents`), each rank a certified frame-dimension jump; the idle inventory remains upstream data.

- `Networks/FramedEventTrace.lean` additionally models literal clear and copy assignments, their actual scalar effects and resulting frame labels. Clearing dirty data is explicit in the erased scalar word; no restoration assumption is introduced. Guarded verification and the complete104-declaration standard-axiom audit pass.

- `Networks/Certificates/PR589/` checked replay prefixes now cover the complete D, A and retained-helper scatter sections, using shallow mask-bank checkpoints and Replay000 through Replay096. All register bounds and the exact24305 elementary-addition count are checked separately. The frozen prefix audit passes12218 declarations; the later B/C replay and complete dirty endpoint remain outside this checkpoint.

- `Networks/Certificates/T16/Trace/`: Complete selected forward/backward native-event label continuity certificates, preserving all 24767 events per orientation and checking touched scalar frames, explicit copy/clear transitions and phase order. All 56 modules pass guarded checks; the namespace audit covers 27443 declarations with standard axioms only. Frame geometry, actual adapter operators, full dirty routing, owner hosting and tape costs remain separate. Hash-pinned importer: `scripts/generate_t16_trace.py`.

- `Networks/Certificates/PR589/{DirtyEndpoint,FiniteWord}.lean`: Complete selected 5583-instruction scalar word on arbitrary dirty inputs, with source/helper restoration and target additions; the finite661-register program retains every instruction. All235 replay chunks and complete14586-declaration standard-axiom audit pass, plus four finite-adapter contracts. Exact24305 elementary additions are counted. Frame/scatter-COPY interpretation, rank geometry, hosting and tape costs remain open.

- `NLogN/PhaseCell.lean`: Exact integer phase and affine offset relation for the existing nearest-rounding convention; each within-cell lattice coefficient of the actual `normExp` factors into Gaussian distance and positive diagonal similarity weights. Potential/weight bounds are proved. Guarded checking and all12-declaration standard-axiom audit pass. Periodic alias sums, truncation, rounded Toeplitz inverses, bulk execution and costs remain open.

- `NLogN/PhaseCellScan.lean`: Executable integer phase/remainder scan, one comparison and at most one correction per index, with invariant identifying exact existing nearest-rounding phases and offsets (including ties). Guarded check and seven standard-axiom theorem audits pass. Tape representation, physical cell/boundary sizing and actual bit costs remain separate.

- `NLogN/PhaseCellIntervals.lean`: Monotone nearest-rounding phase, order-convex physical cells, strict within-cell offset gap and selected4d+1 interval-cardinality bound, including truncated end cells, with a concrete scan corollary. Guarded checking and nine standard-axiom theorem audits pass. Boundary extraction, full-cell lower lengths where required, inverse execution and tape costs remain open.

- `NLogN/InversePerturbation.lean`: Actual two-sided continuous-linear-map inverse stability, with explicit M/(1-M*eta) inverse norm and M^2*eta/(1-M*eta) inverse error, plus half-gap specialization. Guarded checking and both standard-axiom theorem audits pass. Construction and approximation bounds for the selected rounded operator remain explicit premises.

- `NLogN/PhaseCellRounded{,Error}.lean`: Rational within-cell block with shared symmetric Gaussian-distance samples, exact unit diagonal, band zeros and exact diagonal similarity; actual P-grid floor error gives in-band coefficient error at most3eta/r² under a certified positive denominator lower bound. Both guarded checks and all14 theorem axiom audits pass. Noncomputable floor specifies rounding; the corrected exponential evaluator, selected lower weights, cross-cell/alias/tail and full operator bounds/costs remain open.

- `NLogN/PhaseCellWeightBounds.lean`: The selected gap and normalization budgets imply weight≥2^(-8p), rounded-denominator positivity at precision2^15*p, and the actual ideal-grid coefficient error without a positivity oracle. Guarded check and six standard-axiom contract audits pass.

- `NLogN/PhaseCellExpSample.lean`: Corrected executable expPiNat sample (subtract2, clamp0, divide2^P), proved nonnegative/downward with error≤4/2^P from the existing Taylor evaluator. Guarded check and seven standard-axiom theorem audits pass. Native ExpTape executes the uncorrected routine; rational-argument mapping, coefficient transfer, correction execution and Mathlib backend costs remain separate.

- `NLogN/PhaseCellExecutableCoefficients.lean`: Actual corrected exponential samples form rational shared kernels and structured within-cell entries with literal diagonal/band conventions. Exact similarity and coefficient error≤12eta/r² follow from certified target mappings and denominator margin. Guarded check and nine standard-axiom theorem audits pass, reusing the now-public ratio_error bound. Concrete argument mapping, selected margin, cross-cell/alias/tail/operator estimates and tape costs remain separate.

- `NLogN/PhaseCellRationalArgs.lean`: Executable integer nearest rounding and rational phase/Gaussian exponent arguments agree exactly with existing real definitions; positivity and natural numerator/denominator encoding proved. Guarded check and all15-declaration standard-axiom audit pass.

- `NLogN/PhaseCellConcreteCoefficients.lean`: Ordinary executable corrected coefficients instantiated with those exact rational arguments; selected gap/normalization/precision prove positive denominator samples, shared-kernel symmetry, exact similarity and mapping-free coefficient error. Guarded check and fourteen standard-axiom theorem audits pass. Cross-cell, periodic/band tails, operator row estimates and tape costs remain open.

- `MathlibTM2/Fast/CompactStopped{DigBody,Digits}.lean`: Actual complete digit scanner with supplied cutoff, exact rebased records/exponents, actual rebased-leaf clearing, per-pass prefix lengths and all live-wire restoration. Two clean guarded checks and three standard-axiom contract audits pass. Runtime cutoff, semantic piece identification, precision, caller replacement and full stopped-layer cost absorption remain separate.

- `Networks/Certificates/T16/Geometry/`: Exact1004 binary bases/duals; a span checker proved sound once decides every climb/center edge of the forward trace from the catalog, and the backward geometry follows from the forward one; doubled-space shear/Lagrangian intersections give every declared geometric width deficit. All182 modules pass clean guarded checks;16310-declaration audit standard axioms only. Actual canonical Clifford action, symplectic B-block rank correspondence, global phases and hosted tape realization remain unproved.

- `NLogN/PhaseCellCrossCell.lean`: Executable direct cross-cell samples and a combined retained-band entry with actual phase selection, literal unit diagonal and band zeros; selected entry error is uniform across within-cell and cross-cell branches. Guarded check passed.

- `NLogN/PhaseCell{TailBounds,SelectedTail}.lean`: Dimension-independent entire-lattice omitted-tail estimate, including all periodic aliases among omitted offsets. Both signed tails sum to at most2^(-46p) under explicit16p≤u*w². Guarded checks and the combined26-declaration cross-cell/tail standard-axiom audit pass. Executable band selection, periodic matrix assembly, operator row estimates and machine costs remain open.

- `NLogN/PhaseCellBand.lean`: Executable width sqrt(floor(16p/u))+1 strictly satisfies the entire-lattice band condition; the preceding square gives a matching rational scale bound. Instantiation discharges the full2^(-46p) signed-tail allowance without a width oracle. Guarded check and six-declaration standard-axiom audit pass. Tape execution/cost and periodic-row assembly remain separate.

- `Networks/Certificates/T16/Tableau{,Rank,Source,Certificate}.lean`: Source-faithful binary canonical recipes, including zero/full-rank branches, proved inverse-Z subspaces without restricted nondegeneracy, and actual relative-tableau X-block rank by kernel transport/rank-nullity. Literal ordered-basis extension API links native rank claims to certified spans. Four guarded checks and104-declaration standard-axiom audit pass. Supplying1004 literal extension matrices, complex/Pauli/global-phase semantics, dirty routing and hosted costs remain open.

- `MathlibTM2/Fast/CompactStoppedGlobal{Cutoff,Pipeline}.lean`: Actual preserved global dimension supplies the selected floor-log cutoff with denominator10^24 and one level of digit slack. The complete semantic scanner computes and clears the cutoff, preserving global dimension and live wires; every emitted leaf satisfies leaf^(10^24)≤globalD above the explicit log threshold. Small dimensions explicitly yield cutoff zero. Guarded checks and standard-axiom audits pass. Actual compact-caller replacement, stopped precision, small-input treatment and full cost absorption remain open.

- `Networks/Certificates/PR589/Frames/`: Exact occurrence-indexed frame-state replay through D/A/scatter/B/C/final alignment, retaining all29250 phase incidences and527 logical scatter incidences. Generic compiler-pair/phase-semantic identities and exact boundary profiles pass guarded checks;1760-declaration standard-axiom audit passes. Frozen240-file manifest matches. Actual E8 operator interpretation, distinct-frame COPY execution, geometric ranks, hosting and costs remain open.

- `MathlibTM2/Fast/CompactStopped{ReservedPieces,SynRec,SynRoot,Precision}.lean`: Actual original-parameter reservation/root constructor uses preserved global dimension for stopped active-digit scanning, retains the existing back reservation, returns mapped semantic pieces and fresh exponent sum with exact full-frame costs. Precision follows from the actual configured width and activeD≤globalD, without an assumed stopped precision bound. Four guarded checks and seven principal standard-axiom contract audits pass. Top adapter/layer replacement, asymptotic costs, and a separate back-leaf budget remain open.

- `NLogN/PhaseCellRow{,Budget}.lean`: Actual corrected finite periodic row accumulates every retained offset into its residue, including repeated aliases; identified with the existing normN lattice series. Exact signed-tail splitting plus executable-band tail and retained-entry estimates yield dimension-independent row error≤2^(-45p) against normN. Both guarded source checks and22-declaration standard-axiom audit pass. Actual continuous-linear-map/inverse packaging, sharp inverse bounds, Toeplitz/Schur/core/halo tape realization and costs remain open.

- `Networks/Certificates/T16/TableauExtension.lean`, `TableauNative.lean`: every certified frame extends to an invertible address map retaining its columns, by completing its independent vectors to a Mathlib basis; native inverse-Z and actual relative X-block rank hold for every climb/center event in both original orientations. Only the retained columns are specified, so no literal extension matrices are needed. Complex Pauli/global-phase semantics, monomial-factor realization, dirty routing and machine costs remain open.

- `NLogN/PhaseCellOperator.lean`: Actual corrected periodic row is a continuous linear map; its proved operator-norm error≤2^(-45p) feeds the quantitative inverse theorem. Given an actual exact inverse bounded by2^(16p), it constructs a two-sided rounded inverse bounded by2^(16p+1) within2^(-12p). Guarded check and14-declaration standard-axiom audit pass. The exact sharp inverse bound and structured execution/cost remain open obligations.

- `Networks/Certificates/PR589/Copy/`: Source-faithful nine COPY/ERASE lifecycles through physical temporary661, with527 frame-zero ADD incidences (545 total records). Proves decoded logical-scatter equivalence for arbitrary dirty binary streams and supplied invertible frame interpretation, immutable copied source and cleared temporary. Four guarded module checks and101-declaration standard-axiom audit pass; exporter order and all six manifest hashes verified. Concrete rational E8 operator interpretation and true COPY/MOVE ranks remain open.

- `MathlibTM2/Fast/{CompactTopAdapterContract,CompactStoppedTopSetup,CompactStoppedTopOriginal,CompactStoppedBackBudget}.lean` and `Cost/CompactStoppedReservation.lean`: Complete actual stopped top constructor reuses unchanged adapter with fresh exponent/configuration/width and exact full-frame costs. Back reservation is unchanged and separately charged by512*B*V, with actual floor-chunk bound B≤2*g*d^(1-c)+1; no tiny-beta premise is imposed on reserved rows. All guarded checks and principal standard-axiom audits pass. Source reserves those rows outside active stopping. Hosting/layer replacement and active recurrence absorption remain open.

- `NLogN/PhaseCell{Dominance,DominanceBudget,SharpInverse}.lean`: Paired nearest-neighbour bound plus entire-lattice tail gives actual offDiagCLM norm≤1−1/(4p) for p≥2,8p≤2^u,alpha²=u and axis gap≥1/(4p). Constructs actual two-sided normalized inverse of norm≤4p and actual corrected periodic rounded inverse of norm≤8p, with inverse difference≤32p²/2^(45p), under the existing similarity/precision budget. No alpha²*axisGap≥1 assumption remains. Three guarded source checks and eight-declaration standard-axiom audit pass. Fast structured solve, boundary composition, prime supply and tape-cost integration remain open.

- `MathlibTM2/Fast/CompactStopped{AmbientDepth,TopPlaced,SynLayerRecords,Geometry}.lean` and `Cost/CompactStoppedReservationReady.lean`: Actual host placement and SynV layer-record execution return the fresh stopped records/configuration; selected-address lists agree exactly after global rebase, preserving coverage and padded-row geometry. Fresh precision discharges actual piece readiness and separate reservation costs. Ambient recursion depth is bounded from the selected-axis runtime cutoff, including small selected dimensions. Five guarded checks and seven principal standard-axiom audits pass. Nonempty selected-axis case is explicit; downstream refresh/prepare, empty fallback and active numerical recurrence remain open.

- `Networks/Certificates/PR589/Geometry/`: Actual rational E8 root spans with dot/2 form give nondegenerate projection subspaces by positivity. Concrete frame operators are ShearFrame pullbacks on binary-valued streams over rational address pairs; COPY is the inverse projection shear and its rank is the actual span finrank. Comparable MOVE rank is the projector-difference rank. All nine retained COPY ranks equal7 (sum63), and first literal MOVE0→2 rank1 is checked. Four guarded module checks, final model check and99-declaration standard-axiom audit pass; six-file manifest verified. Complete label/MOVE profile, moments, hosting and tape realization remain open.

- `NLogN/Schur{Dominance,Elimination}.lean`: Literal one-pivot real Schur update on arbitrary active vertex sets preserves any positive row-dominance margin and cannot increase absolute row mass. Successive updates retain both invariants, skip absent/duplicate vertices, and satisfy the exact right-hand-side equation from the original pivot equation. No symmetry/positive-definiteness assumption. Both guarded checks and17-declaration standard-axiom audit pass. Instantiation with the actual rounded Gaussian matrix, boundary sparsity/ordering, LU/Woodbury execution and costs remain open.

- `Networks/Certificates/T16/Pauli{,C,Generators,Diagonal,DiagonalAction,Source,Inverse}.lean`: Genuine complex C/P/D operators with phase-exact conjugation and inverses on arbitrary Paulis, literal source diagonal polynomial and alpha parity compatibility, finite-word composition and explicit global-phase operator. All seven guarded checks and164-declaration standard-axiom audit pass without warnings; eight-file manifest verified. Canonical-word/native-tableau identification, monomial residual equality, tableau-plus-zero-state completeness, adapters/routing and machine costs remain open.

- `NLogN/PhaseCell{Matrix,Boundary}.lean`: Executable rational periodic matrix accumulates every retained alias, has nonnegative entries and diagonal≥1, and its matrix-vector action equals the actual rounded Gaussian operator. Proves true matrix row margin1/(8p) in the selected small-gap regime and preserves it through arbitrary interior elimination. Both guarded checks and12-declaration standard-axiom audit pass. Boundary sparsity/order, exact block-Schur identification, structured solver realization and tape costs remain open.

- `NLogN/{SchurSolve,PhaseCellBoundarySolve}.lean`: Successive Schur elimination carries its right-hand side exactly: every full solution restricts to the eliminated system, eliminated vertices are recovered from their pivot rows, and a positive row-dominance margin μ bounds active solutions by max|rhs|/μ and makes them unique. On the actual rounded Gaussian matrix, any interior elimination leaves a reduced boundary system whose solution equals the full solution and is bounded by 8p times its right-hand side. Both guarded checks and the10-declaration standard-axiom audit pass. Boundary sparsity/order, Gohberg–Semencul interior inverses, rounded structured solves and tape costs remain open.

- `NLogN/{SchurSupport,PhaseCellBoundarySupport}.lean`: Schur fill-in needs both links through the pivot, so eliminating vertices that couple only within their own cell leaves original entries or same-cell entries. The actual rounded Gaussian matrix is supported in the cyclic band of the selected width; a vertex whose band stays in the array and in one phase cell is interior, and eliminating any interior vertices leaves only band entries or entries joining one phase cell. Both guarded checks and the10-declaration standard-axiom audit pass. Boundary count/ordering bandwidth, Gohberg–Semencul interior inverses, rounded structured solves and tape costs remain open.

- `NLogN/ToeplitzInverse.lean`: Gohberg–Semencul for any two-sided inverse of a symmetric Toeplitz matrix over a field: the inverse is symmetric and persymmetric, satisfies the Trench diagonal recurrence, and with first column x and shifted reversed column z (z₀=0) gives x₀M=L(x)L(x)ᵀ−L(z)L(z)ᵀ entrywise. Only x₀≠0 is assumed, no positive-definiteness. Guarded check and the24-declaration standard-axiom audit pass. Instantiation on phase-cell interiors, rounded factors and convolution costs remain open.

- `NLogN/ToeplitzDominant.lean`: A symmetric Toeplitz block with unit diagonal and off-diagonal row mass ρ<1 has an actual two-sided inverse (via dominance-forced injectivity), every inverse row has absolute sum at most 1/(1−ρ), and its corner is at least 1−ρ/(1−ρ). Row mass is at most twice the one-sided coefficient sum. For ρ≤1/8 the corner is at least 6/7 and the Gohberg–Semencul factorization holds. Guarded check and the41-declaration ToeplitzInverse-namespace standard-axiom audit pass. Instantiation on the actual phase-cell kernel, rounded factors and convolution costs remain open.

- `NLogN/PhaseCellToeplitz.lean`: The actual shared within-cell kernel has unit diagonal and executable off-diagonal samples at most 20^-δ once u≥1, so its one-sided sum is at most 1/16 and every Toeplitz block has row mass at most 1/8. Each interior block of any length therefore has an actual inverse with corner at least 6/7 and the Gohberg–Semencul factorization; actual cell entries are exactly its diagonal similarity from any physical start. Guarded check and the10-declaration standard-axiom audit pass. Interior/boundary block composition, rounded factors and convolution costs remain open.

- `NLogN/{SchurBlockSolve,PhaseCellFourStep}.lean`: The source's two interior passes and one boundary solve (y=Rb, r=b_B−A_BI y, Sx_B=r, x_I=R(b−A_IB x_B)) for any exact interior solver R: exact interior solves are linear under dominance, any boundary solution glues to a full solution, and under a margin on I∪B it is the unique solution with boundary values at most max|b|/μ. On the actual rounded Gaussian matrix, for any interior set, the four steps reproduce the full solution with boundary values at most 8p times the right-hand side. Both guarded checks and the10-declaration standard-axiom audit pass. Rounded factors, error propagation and convolution/tape costs remain open.

- `NLogN/{SchurBlockError,PhaseCellRoundedSolve}.lean`: Error composition of the four-step solve. The exact full solution satisfies the Schur boundary equation, the Schur operator is linear with inverse bound 1/μ, and stage deviations e₁…e₅ (interior pass, residual, boundary solve, recovery right-hand side, interior pass) give boundary error e₃+(Ke₁+e₂)/μ and interior error e₅+(e₄+K·boundary)/μ for coupling row mass K. On the actual rounded Gaussian matrix, off-diagonal row mass is at most one, so the errors are e₃+8p(e₁+e₂) and e₅+8p(e₄+e₃+8p(e₁+e₂)), with no factor in the number of cells. Both guarded checks and the8-declaration standard-axiom audit pass. Local stage error bounds for rounded Gohberg–Semencul and boundary elimination, and tape costs, remain open.

- `NLogN/{ToeplitzApply,ToeplitzRounded}.lean`: Gohberg–Semencul as an operator: x₀·M v equals L(x)L(x)ᵀv−L(z)L(z)ᵀv with truncated lower convolutions and upper correlations, whose row norms are bounded by the coefficient mass. Rounded application: with masses at most two, x₀≥1/2, factors and reciprocal within η and each of the five computed stages rounded within η, the result is within 64·L·η·V of the exact inverse application for inputs bounded by V≥1 when Lη≤1. Both guarded checks and the39-declaration standard-axiom audit pass. Similarity scaling, actual factor rounding and convolution costs remain open.

- `NLogN/PhaseCellInteriorRow.lean`: The retained window is the symmetric integer interval sum. An interior row (band inside the array and one phase cell) has no aliasing, so every entry of the actual rounded Gaussian matrix in that row is exactly a_i·G(|l−i|)/a_l with the shared Toeplitz kernel G, including zeros beyond the band. Guarded check and the3-declaration standard-axiom audit pass. Per-cell interior solves, similarity-scaled rounding and costs remain open.

- `NLogN/ToeplitzLocal.lean`: A dominance margin on a finite active set yields an actual exact solver for every right-hand side. On a block of the active set closed under its couplings, with entries a diagonal similarity d_a·g(|a−k|)/d_k of a symmetric Toeplitz matrix with inverse m, every solution equals d_a·Σ_k m(a,k)·c_k/d_k. Guarded check and the2-declaration standard-axiom audit pass.

- `NLogN/SchurIdentify.lean`: Exact block-Schur identification. Elimination leaves exactly the set minus the eliminated list, right-hand sides vanishing on eliminated vertices are carried unchanged, and after eliminating all interior vertices in any order the reduced matrix acts on boundary vectors exactly as the Schur operator A_BB−A_BI·A_II⁻¹·A_IB; it inherits the full dominance margin. Guarded check and the4-declaration standard-axiom audit pass.

- `NLogN/SchurLU.lean`: LU factors of successive elimination in list order: A=LU on the active set, each pivot consumes μ|A_ik|/A_kk of every other row's mass so multiplier rows sum to at most 1+mass/μ, and pivot rows keep the margin μ and never exceed the original row mass. Any computed forward and back substitutions with residuals εf, εb against the exact factors solve the system within (Λεb+εf)/μ. Guarded check and the5-declaration standard-axiom audit pass.

- `NLogN/SchurLURounded.lean`: Rounded triangular solves with rounded factors: multipliers have unit diagonal; with factor row-sum errors εL, εU, forward rows rounded within η and back-substitution residual δ, and smallness c=(ΛεU+εL(M+εU))/μ≤1/2, the computed solution is within 2((Λδ+η+εLδ)/μ+cX) of the exact solution bounded by X. The a priori growth of computed values is bootstrapped from the maximum error. Backward-error form `backward_lu`: computed factors with unit-diagonal multipliers whose product equals the matrix up to row mass εS give error 2((Λδ+η)/μ+(εS/μ)X) when εS/μ≤1/2, so factors produced by rounded elimination need only a backward bound, not closeness to the exact factors. Guarded check and the3-declaration standard-axiom audit pass.

- `NLogN/SchurLUBackward.lean`: Backward stability of rounded elimination with any multiplier rule within η of the exact quotient (`mul`, e.g. rounded division `divMul` or a stored rounded reciprocal times the entry): each multiplier and update rounded within η keeps dominance with margin loss 2η(n+m) and mass gain η(n+m) per stage; while losses stay inside the budgets the computed unit-lower and pivot-row factors reproduce every entry within len·η(1+M), pivot rows keep margin μ/2 and mass M, and multipliers sum to at most 1+len(2M/μ+η). Combined with rounded triangular solves, the computed solution is within 2((Λδ+η)/μ+(εS/μ)X), εS=n·len·η(1+M). Guarded check and the5-declaration standard-axiom audit pass.

- `NLogN/NewtonRecip.lean`: Rounded Newton reciprocals with multiplications only (no record division exists on tapes). Perturbed steps satisfy E'≤E²+ε; with ε≤2κ/9 and E₀≤1−κ the error obeys (1+κ/2)E_k≤(1−κ/2)^(2^k) until it reaches the floor 3ε/κ (quadratic convergence, O(log(pP)) steps). From 1/4, r←rd(r(2−rd(br))) gives |r_K−1/b|≤60η/β² for b∈[β,3]; the total multiplier rule `recipMul` (Newton reciprocal times entry on the working range) is within η(1+60M/β²) of exact division and maps 0 to 0, so it plugs into the generalized rounded elimination. Guarded check and the namespace standard-axiom audit pass. `recipNewton` (stored pivot reciprocal) has residual |c r−1|≤180η/β² on [β,3].

- `NLogN/{PhaseCellWeightRange,PhaseCellRoundedCell}.lean`: Every actual executable similarity weight lies in [2^-(8p+1),1] at the selected precision. Rounded interior solve of one actual phase-cell interval: computed reciprocal weights, scaled inputs, the five Gohberg–Semencul stages and rescaling reproduce the exact interior solution of the actual rounded Gaussian matrix within η+64LηV+2(η+Cη). Both guarded checks and the2-declaration standard-axiom audit pass.

- `NLogN/PhaseCellBoundaryLU.lean`: Actual rows have absolute mass at most two. After eliminating the interior, the actual boundary Schur matrix keeps margin 1/(8p) and row mass at most two, its multipliers sum to at most 1+16p and pivot rows to at most two; rounded factors and rounded triangular solves are within 2(((1+16p)δ+η+εLδ)·8p+c·8p·8pρ) of the exact Schur solution for right-hand sides bounded by ρ, under smallness c=((1+16p)εU+εL(2+εU))·8p≤1/2. Guarded check and the2-declaration standard-axiom audit pass.

- `NLogN/PhaseCellFactorization.lean`: Permutation-left factorization in the small-gap regime without α²θ≥1: the actual exact inverse of N (norm up to 4p) gives P_s F_s = 2^(2⌈α²⌉+2+j)·B₀'·P_t F_t A with contractions A and B₀'=B₀/2^j whenever 2p≤2^j, the form consumed by the generic source-error theorem `sourceApprox_err` with γ=d(2⌈α²⌉+2+j). Guarded check and the standard-axiom audit pass.

- `MathlibTM2/Mult/B0Generic.lean`: `B̃₀ = D̃'·J̃·C` for an arbitrary computed inverse J̃: if J̃ keeps the unit disk and is within εJ of J(v/2), the map satisfies the pipeline's `hB'`/`hB'1` interface with error 6+εJ; B₀ is linear in its inverse, so the small-gap target B₀(J/2^j) is B₀(J)/2^j. Guarded check and the3-declaration standard-axiom audit pass.

- `MathlibTM2/Mult/PhaseCellB0.lean`: Small-gap `B̃₀` interface: a computed inverse within e of L(v/2)/2^j, with L the rounded-operator inverse within δ₀ of the exact inverse J (‖J‖≤4p, 4p≤2^j, e+δ₀/2≤1/2), keeps the unit disk and makes `B̃₀` approximate the normalized factorization target B₀(J)/2^j with error 6+2^p(e+δ₀/2). Guarded check and the2-declaration standard-axiom audit pass.

- `MathlibTM2/Mult/SmallGapSizes.lean`: Small-gap parameters at the existing sizes: with u=⌈log₂(8p)⌉ and the dimension d as cell parameter, every axis satisfies 8p≤2^u, 1/(4p)≤θ_i, 1/4≤dθ_i and u·d≤p (via u²≤36b). The banded small-gap inverse can therefore replace the Neumann inverse with α²=u without changing axis sizes. Guarded check and the4-declaration standard-axiom audit pass.

- `MathlibTM2/Mult/BandedB0.lean`: The rounded operator acts on complex vectors through the real matrix on real and imaginary parts, so its inverse is assembled from two exact real solves. Real solves within e of the exact solutions, normalized within η, give the pipeline `B̃₀` interface for the small-gap factorization target B₀(J)/2^j with error 6+2^p((2e+η)+δ₀/2). Guarded check and the3-declaration standard-axiom audit pass.

- `NLogN/{SchurFill,PhaseCellBandFill}.lean`: Ordered fill: if a support relation contains the original entries and is closed under fill through earlier pivots, every multiplier and pivot-row entry of elimination in that order lies in it. For the actual rounded matrix in physical order, the band-or-cyclic-border relation qualifies, so every factor entry lies within the selected band width or in the w-wide border, and every non-border factor row has at most 3w+1 entries; a line solve with stored factors touches O(sw) entries. `fill_support_r` gives the same for rounded elimination with rd 0=0, together with triangularity of the rounded factors in elimination order. Both guarded checks and the5-declaration standard-axiom audit pass.

- `NLogN/SchurSubst.lean`: Rounded forward substitution (each unit-lower row rounded once) and back substitution (each quotient by the pivot rounded once) along the elimination order, with residuals within η and Mη; `bandSolve` composes rounded elimination with both substitutions and `bandSolve_error` bounds its error end to end for any dominant system. Machine-faithful variants `fwdM`/`bwdM`/`bandSolveM` round every product separately with exact sums and multiply by stored rounded pivot reciprocals (no record division on tapes); their residuals are nη and (n+M+2θM)η+2θMB, and `bandSolveM_error` bounds the solve via the size-dependent `backward_lu_k`. Column-oriented `colFwd`/`colBwd` (update pending right-hand sides after each final value, as the tape machine does) equal the row-oriented `fwdM`/`bwdM` because sums are exact. Guarded check and the12-declaration standard-axiom audit pass.
- `NLogN/{SchurCongr,SchurStages,SchurWindow}.lean`: Rules agreeing on the working range (entries ≤M, pivots in [μ/2,M]) give the same factors and solve (`lur_congr`, `bandSolveG_congr`); factors relabel along injections (`lur_map`) and, for the natural order, are entries of the stage matrices `stg` (`lur_range`); the sliding-window factorization (`stepRows`, `factorRows`) on B+1 rows × 2B+1 columns emits each stage's eliminated column and pivot row (`stepRows_window`, `factorRows_run`), using band preservation (`bandFrom_relim`, `stg_far`). Guarded checks and the standard-axiom audit pass.
- `MathlibTM2/Mult/BandFactor.lean`: Integer-numerator window factorization (`newtonZ` Newton reciprocals, `mulZ` multipliers, `stepRowsZ`/`factorRowsZ`) equals the real run with `rdP P` and `machMul` on the grid (`newtonZ_eq`, `factorRowsZ_map`). `FastB0.concrete_resampB₀_specX/specP` (ConcreteB0) give the pipeline interface for any line solver and for `machSolveT` on a perturbation `At` of the phase-cell matrix (`NLogN/PhaseCellPerturb`: margin 1/(16p), mass 9/4, extra error 64p²ε); `Big.newton_conditions`/`Big.concreteB0P_conditions` (ConcreteB0Sizes) discharge it at precision 5p with β=1/(32p), `newtonK` iterations, ε ≤ 2^-3p, error ≤ p². Guarded checks and the standard-axiom audit pass.
- `MathlibTM2/Mult/BandSolveList.lean`: Integer stage matrices `stgZ` (grid values = real `stg`), window outputs identified (`factorRowsZ_run`), forward table = padded multiplier columns (`lcols_eq`, `banded_LzN`), backward table = transposed pivot rows (`ucolZ`, `ucols_eq`, `banded_UzN`); `lineSolveZ_eq`: the numerator line solve equals the machine-rule `bandSolveG` of the natural order. `bandSolveG_map` (SchurStages) relabels solves along injections. Guarded checks and the standard-axiom audit pass.
- `NLogN/{PhaseCellPerturb,PhaseCellMachMatrix}.lean`: A row-sum perturbation ε ≤ 1/(32p) of the phase-cell matrix keeps margin 1/(16p), mass 9/4; the machine solve is within 62000(2p)³s²η'+64p²ε (`bandSolveMach_perturb`). The wrapped Gaussian window matrix `windowMatrix` with entries within δ is within (2w+1)δ+2^-46p+2^-45p per row (`windowMatrix_close`). `FastB0.concrete_resampB₀_specW` and `Sizes.window_eps_le` close the B̃₀ interface for it. Guarded checks and the standard-axiom audit pass.
- `MathlibTM2/Mult/BandSolveFold.lean`: Numerator window matrix `wmZ` (grid values = `windowMatrix`), folded storage `foldZ` with band 2w+1 (`foldZ_band`); `lineSolveFold_eq`: the numerator line solve on `foldZ` is `FastB0.machSolveT` read in folded positions. Guarded check and the standard-axiom audit pass.
- `MathlibTM2/Mult/BandTranspose.lean`: The pivot-row transpose as a sliding window of B blocks (`tStep`, `tRun`, window `tWin`); `tRun_eq`: from the zero window it emits the backward-pass columns `ucolZ` in increasing pivot order. Guarded check passes.
- `MathlibTM2/Mult/BandFoldRows.lean`: The folded matrix rows a table machine emits: `foldEntryZ` (by the forward residue `fdist` of folded vertices, `2^P` on the diagonal, `tableE` within the band; equals `foldZ` of `coefZ` when 2w+1 < s via `wmZ_single`), rows `foldRowZ` on 2B+1 columns, `foldRows_eq` (the stream is the initial window then the factorization inputs), `coefZ_err` (coefficients within 2/2^P of the Gaussian). Guarded check passes.
- `MathlibTM2/Mult/BandFoldList.lean`: Folding a line as list operations (`foldList`: interleave the first half with the reversed rest; `unfoldList`: evens then reversed odds) with entrywise identities `getD_foldList` (index `foldAtN`, equal to `foldAt` values) and `getD_unfoldList` (index `foldPosN`). Guarded check passes.
- `MathlibTM2/Fast/TableFold.lean`: Table-VM program `tblFoldStreamCode` (60 variables; reuses the Gaussian entry bodies `tblOffPosBody`/`tblOffNegBody` renamed into the first 48) emitting the folded rows: rows i < NR, in row i the 2B+1 entries `foldEntryZ` from column i−min(i,B) (`tblFoldStream_do`), with per-entry (`tblFoldEntry_do`), per-column, per-row (`tblFoldRow_do`) and setup (`tblFoldSetup_do`, π, constants, 2^P) contracts; `tblFoldStream_cstream` (the stream is the records of the rows `foldRowZ`) and `tblFoldStream_host` (on the host). Guarded check and the standard-axiom audit pass.
- `MathlibTM2/Fast/BandFactor.lean`: Tape machines of the window factorization. `bandNewtonStepP` (one Newton step `r ← 2r − r(cr)` on `xa` for the pivot on `hv`, two record products and two record subtractions, `band_newtonStep_runs`) and `bandNewtonP` (start from the constant on `bx`, one step per symbol of `kn`, ends with `newtonZ P c K`, `band_newton_runs`); `bandFacRowP` (one non-pivot row: multiplier by the stored reciprocal, row update by the forward step on 2B tail records, shift into the new window `sr` with a zero record, `band_facRow_runs`) and `bandFacRowsP` (the B rows, `band_facRows_runs`, outputs in terms of `facMul`/`facRow`); `bandFacStepP` (one window step: pivot row to `hf`, Newton reciprocal to `df`, multipliers to `dout`, updated rows plus the next input row of `src` back on `vk`, `band_facStep_runs`); `bandFacLoopP` (s window steps; window state `facState` iterates `stepRowsZ`, outputs pivot rows, reciprocals and all multipliers, `band_facLoop_runs`, under the width conditions `FacFits`); `bandTBlkP`/`bandTStepP` (one transpose step: block heads to the column on `ef`, blocks shifted with a zero, new first block from the next pivot row of `src`, `band_tStep_runs`) and `bandTLoopP` (all pivots: `ef` gains the backward-pass columns `ucolZ`, last on top, `band_tLoop_runs`); `bandRevP` (block-order reversal between registers, `band_rev_runs`); `bandAxisFacP` (split off the window and factor, `band_axisFac_runs`), `bandAxisOrgP` (reorganize factor outputs and switch counters between phases, `band_axisOrg_runs`), `bandAxisTrP` (transpose and store the backward columns, `band_axisTr_runs`); `bandAxisPrepP` (the whole per-axis preparation: forward table on `bo`, backward columns on `hf`, reciprocals on `df`, line counters set; `band_axisPrep_runs`, cost `bandAxisPrepCost`; `factorRowsZ_facState` reads the integer run off the window states); `facState_window`: the tape window states are the windows of the integer stage matrices `stgZ`. `NLogN/SchurStages.stg_inv` gives the stage invariant (margin, mass) after every pivot, for the record-width bounds. Guarded check passes.
- `MathlibTM2/Fast/BandFold.lean`: Record moves for folding a line on tapes: one record through `ac2` keeping its symbols (`band_rec1_runs`), the interleave and deinterleave loops (`band_ileave_runs`, `band_deileave_runs`), repeated record moves (`band_rec1Rep_runs`), the fold of a line `sel → vk` (`bandFoldLineP`, `band_foldLine_runs`, result `foldList`) and the unfold `dout → sel` (`bandUnfoldLineP`, `band_unfoldLine_runs`, result `unfoldList`; `split_evens_odds` in BandFoldList). Guarded check passes.
- `MathlibTM2/Fast/BandLineDriver.lean`: The three phases of one banded line on tapes: input (`bandLineInP`, `band_lineIn_runs`: select the rows, fold, scale by the constant on `smwn`, append B zero records), passes (`bandLinePassP`, `band_linePass_runs`: forward loop with the table `bo`, re-pad, backward loop with columns `hf` and reciprocals `df`), output (`bandLineOutP`, `band_lineOut_runs`, with the registers `dtab`, `padc` of `RsbR`: unfold, scale by the constant on `bx`, multiply by the diagonal table `dtab`, move onto `dst`, pad `t - s` zero records), and the whole line (`bandLineP`, `band_line_runs`: `dst` gains `bandOutVec` of `bandSolveVec` of `bandInVec`, then `t - s` zero records). Explicit step bounds `bandLineInCost`, `bandLinePassCost`, `bandLineOutCost`, `bandLineCost`. Guarded check passes.
- `MathlibTM2/Fast/BandLineSpec.lean`: What the tape line computes. Factor tables of the folded window matrix (`bandFac`, `bandLc`, `bandUc`, `bandRcs`); `bandSolveVec_re_eq/im_eq` (the complex passes are `lineSolveZ` on each part); exact rescalings (`tdivN_scale_in/out/tab`, `rhoC_scale`); `prep_bo_eq`, `prep_hf_eq`, `prep_df_eq` (the preparation tables are the line tables `bandLc`, `bandUc`, `bandRcs`); `bandLine_spec`: with input constant `2^(2P-p-1)`, output constant `2^(p-j)` and diagonal table `D·2^(P-p)`, entry ℓ of the line output is entry ℓ of `resampB₀Of p (bandJtX p j (machSolveT K (rdP P) (windowMatrix …))) df` on the grid input; `bandLineG` (the tape line as a list map) and `band_lineG_rel` (`RsbLineRel` to that map at scale 2^p, the interface of `rsb_tensor`). Guarded check passes.
- `MathlibTM2/Fast/BandAxis.lean`: The banded `B̃₀` along the innermost axis (`bandAxisP`: the line while `src` is nonempty, then the outputs back): `BandAxisCfg` (registers configured for an axis), `BandTabOk` (table shapes and widths), `BandLineOk` (record widths of one line), `bandLineT` (the line map for any tables), `band_axis_runs` (cost `bandAxisCost`). Guarded check passes.
- `MathlibTM2/Fast/BandPrepVM.lean`: The 60-variable table machine on the `B̃₀` stage: `bandLay` places variables 48–59 on the spare bank registers `vx j` (`RsbX.vx`), `bandLay_inj`, and `band_toRuns` turns its contracts into stage contracts. Guarded check passes.
- `MathlibTM2/Fast/BandPrep.lean`: the loader of the banded `B̃₀` from the Neumann per-axis record on the new parameter register `prm`, deriving precision `5p`, window `8m`, half band `16m+1`, `4α²` Newton steps by unary arithmetic (`twRuns_umulSym`, `twRuns_udiv`): step 1 (`band_preA`: clear, fields, headers), counts (`band_preF1`), the folded rows onto `src` (`band_preFold`, conditions `BandFoldW`), the factor-phase counters (`band_preF2`), the Newton start (`band_preF3`), the line-phase values parked on `vx` (`band_preL1`–`band_preL9`, `band_vmH` for powers of two), the diagonal table `D·2^(4p)` (`band_preL10`), the factorization with explicit result `bandFP` (`band_preP`; `band_axisPrep_runs` now states every changed register), the final moves (`band_preE`); the whole loader `bandPreB` (`band_preB_runs`: from a register file with empty scratch (`BandPreFree`) and parameter conditions `BandPreOk`, it ends in `bandLoad`, cost `bandPreCost`); `bandLoad_cfg`: the loaded file is a `BandAxisCfg` for the axis tables `bandLc`, `bandUc`, `bandRcs`, `bandDl` and constants `2^(9p-1)`, `2^(p-α²)`. Guarded check passes.
- `NLogN/SchurSizes.lean`: sizes met by the rounded band solve: the stage invariant at every elimination step with a multiplier rule accurate only on the working range (`stg_invL`, `stg_sizes`: pivots in `[μ/2, M]`, active entries at most `M`), relabelling and congruence of the invariant (`stageInv_map`, `stageInv_congr`), and the solve sizes (`bandSolveG_sizes`: solution within the exact bound plus the error, forward values at most `M` times that plus the back residual). Guarded check passes.
- `MathlibTM2/Fast/BandFits.lean`: record widths of the banded `B̃₀` from the stage invariant of the Gaussian window matrix (margin `1/(16p)`, mass `9/4`) and the precision conditions of the machine solve, with `(6/β+1)2^P < 2^(w-1)`: the factorization (`band_facFits`: every window state is `FacFits`), the stored tables (`band_tabOk`), and every line of grid values at most `1` (`band_lineOk`: `BandLineOk`; solution at most `8p+1`, forward heads at most `3(8p+1)+1`, back heads at most `4(8p+2)` through the reciprocal lower bound `band_rcs_lb`). Guarded check passes.
- `MathlibTM2/Fast/BandStage.lean`: the banded `B̃₀` stage. The loader never reads the box or axis registers (`AgreeOff`, layer lemmas, `bandLoad_rsbWith`, `bandPreCost_agree`), so it meets the `hprep` contract of the generic driver (`bandPreB_rsbWith`); frames of the loader (`bandLoad_prm`, `bandLoad_sw`, `bandLoad_vx`, `bandLoad_free`); the configured files `bandCfgB` and step bounds `bandCpB` with their invariants (`BandBase`); the line maps `bandG` and real maps `bandA` per axis (`band_axis_rel`: `RsbLineRel`; `lineRel_ball`); the axis and loader contracts (`band_stage_hcfg`, `band_stage_hprep`); and **`bandStage_exec`**: under the per-axis numeric facts `BandAxisMath` (stage invariant of the window matrix, precision, unit-ball map), `BandPrec`, `BandPreOk` and fitting diagonal tables, the stage computes `tensorZR (d n) (t n) (s n) (bandA n) u` with step bound `rsbAllCostG … bandAxisCost … bandCpB`. Guarded check passes.
- `MathlibTM2/Mult/BandSpec.lean`: the banded `B̃₀` line maps `bandA` and their numeric facts at the pipeline sizes, for a Gaussian width with `8p ≤ 2^(α²)` and `α² d ≤ p`: coefficient accuracy (`bandAZ_err`), every axis's `BandAxisMath` with `β = 1/(32p)` (`band_axis_math`), `BandPrec` with `4α²` Newton steps (`band_newton`, `band_prec`), the unit-ball and `2^-α² ℬ₀` approximation per axis (`band_axis_full`) and `band_factorization`. `Mult/Pipeline` now takes `lineB = bandA` with exponent `γ = d(3α²+2)`; `pipeline_correct` holds unchanged. Guarded check passes.
- `MathlibTM2/Mult/SourceErrScaled.lean`: the source-error assembly with arbitrary line operators and per-line exponent `c` (`factorization_multiC`, `sourceErr_of_componentsC`, `exact_product_of_componentsC`), so a line map approximating `2^-j ℬ₀` enters with `c = 2⌈α²⌉+2+j`. Guarded check passes.
- `MathlibTM2/Cost/MatchBandB.lean`, `MathlibTM2/Cost/MatchBandLoad.lean`: the cost of the banded `B̃₀` stage. One banded line costs `mtBandX ≤ mtBandCX · α √p M(p)` per record (`mt_band_X_le`); the generic driver `rsbAllCostG` along all axes (`mt_rsbG_all_le`); the loader at every step (`mt_band_cp_le`, `42 T w + 300 T + O(r p^5)`) and the cleared registers of the configured files (`mt_band_clr_cfg`); **`mt_band_stage_le_linear`**: the stage costs `O(totResamp + totDirectCRT + T p)`. The tape source phase (`SrcPhase.srcPB`) now runs the band stage with records on `prm`, widths `dsW ≈ 10p`, `dsWW ≈ 70p`; `IntegerMultBounds.MathlibTM2.Theorem` builds with standard axioms.
- `MathlibTM2/Fast/ResampBAll.lean` (generic layer): `rsbStepAxG`/`rsb_stepAxG_runs`, `rsbAllG`/`rsb_allG_runs`/`rsb_allG_tensor` and costs `rsbStepAxCostG`, `rsbAllCostG` take any axis program with a line map `g i`, admissibility `Ok i` and axis cost `cax i`. Guarded build of `IntegerMultBounds.MathlibTM2` passes.
- Removed with the Neumann `B̃₀` of the tape pipeline (restore from `1cb2723b`): `Mult/FastB0.lean` (`resampB₀NumK`: Horner–Neumann `B̃₀` with `α²` steps and window `√p/α`, error `p²` on the unit disk, `resampB₀NumK_spec`), its sizing in `Mult/FastB0Sizes` (`fastB0_conditions`, `p ≤ α⁴ θ`), the Neumann line and axis machines (`ResampBLine.rsbLineP`/`rsb_line_runs`, `ResampBAxis.rsbAxisP`/`rsb_axis_runs`, `ResampBMath.rsb_resampB₀NumK`), the Neumann driver instance (`ResampBAll.rsbAllP`/`rsb_all_tensor`/`rsbAllCost`), the Neumann loader and stage (`PrepB.preB`/`preB_runs`/`preCfgB`/`preCpB`/`rsbStage_exec`), the Neumann pipeline (`ResampBPipe.lineBN`) and its cost (`MatchResampB.mt_rsb_stage_le_linear`). The banded `B̃₀` replaced them.

- `NLogN/PhaseCellBandSolve.lean`: The concrete rounded band solve on the actual rounded Gaussian matrix in physical order: with rounding η, rd 0=0 and 128ps²η≤1, the computed solution of Hx=b with |b|≤1/2 is within 2700s²p²η of the exact solution. The machine-faithful `bandSolveM` (rounded products, stored pivot reciprocals) is within 62000p³s²η when 2^16p²s²η≤1 (`bandSolveM_actual`, arithmetic in `bandM_arith`). Guarded check and the6-declaration standard-axiom audit pass.

- `NLogN/{PhaseCellFold,PhaseCellFoldSolve}.lean`: Folded elimination order 0, s−1, 1, s−2, … turns the cyclic band of half width w into an ordinary band of half width 2w+1: positions are injective and sorted, every original entry and (by ordered fill) every rounded factor entry lies within 2w+1 folded positions of the diagonal, so there is no border fill. The machine-faithful solve in folded order keeps the 62000p³s²η bound (`bandSolveM_fold`). Both guarded checks and the standard-axiom audit pass. `bandSolveG_fold` allows any multiplier rule within η and any pivot reciprocal with residual ≤3η; `bandSolveN_fold` instantiates Newton reciprocals (`recipMul`, `recipNewton`) with error 62000p³s²η(1+180/β²), β≤1/(16p).

- `MathlibTM2/Mult/BandList.lean`: List-level substitutions on integer numerators as the tape machine computes them (`fwdZ`, `bwdZ`: pop the final head, subtract truncated column products from the following pending numerators, with stored reciprocal numerators for the backward pass). On the 2^-P grid they reproduce the column-oriented real solves exactly (`fwdZ_eq`, `bwdZ_eq`, via `rdP_mul_grid`), and zero column tails can be dropped (`subCol_append_zeros`), so only the 2w+1 band entries are touched. Complex-record forms `fwdZC`/`bwdZC` (real column entries acting on both parts) agree with the integer forms on real and imaginary parts, and columns padded to exactly B entries with B zero dummies on the pending list reproduce the full computation for banded factors (`fwdZ_pad`, `bwdZ_pad`), the uniform loop shape the machine runs. Guarded check and the namespace standard-axiom audit pass.

- `MathlibTM2/Fast/BandLine.lean` (in progress): Tape machine pieces of the banded line solve on the `RsbR` registers: pop the final head of the pending stack (`band_pop_runs`), move one padded column of B stored entries (`band_col_runs`), replicate the head B times (`band_rep_runs`), and B pending updates against products rebuilding the records (`band_sub_runs`, `band_subLoop_runs`), each with an exact register contract and step bound; `band_fwdLoop_runs` runs s steps and leaves exactly the step-indexed pending list and outputs of `Mult.BandList` (`bandPend`, `bandOut`, which give `fwdZC`); the backward pass reuses the step after a reciprocal preamble (`band_recip_runs`, `band_bwdStep_runs`) and `band_bwdLoop_runs` leaves `bandPendB`/`bandOutB` (which give `bwdZC`); `band_fwdStep_runs` composes them with one stream product into a full forward column step within `B(rmulCost+40w+60)+30w+60` steps. Guarded check and the10-declaration standard-axiom audit pass.

- `MathlibTM2/Mult/ConcreteB0.lean`: The concrete small-gap `B̃₀` line map: `bandJt` computes the inverse by two rounded band solves of the rounded matrix on the real and imaginary parts of v/2, scales by 2^-j and rounds to the p-grid. Under 128ps²η≤1 and an explicit smallness condition, `B̃₀` satisfies the pipeline interface (error 6+2^p(5400s²p²η+2/2^p+16p²/2^{45p}), unit disk kept) for the normalized factorization target B₀(J)/2^j, J the exact inverse of N. The machine-faithful variant `bandJtM`/`concrete_resampB₀_specM` uses `bandSolveM` (error 62000p³s²η under 2^16p²s²η≤1). The folded variant `bandJtF`/`concrete_resampB₀_specF` is the target of the tape machine. Guarded check and the2-declaration standard-axiom audit pass.

- `MathlibTM2/Mult/ConcreteB0Sizes.lean`: At the existing sizes, rounding toward zero at working precision 3p (`rdP`, error ≤2^-P, rdP 0=0) and normalization j=⌈log₂(4p)⌉ satisfy every precision condition of the concrete small-gap `B̃₀`, and its interface error is at most p² (via s_i≤2^ℓ, 3ℓ≤p, p≥64). `Big.concreteB0M_conditions` gives the same for the machine-faithful map. Guarded check and the4-declaration standard-axiom audit pass.

- `MathlibTM2/Fast/CompactStopped{SynLayerPrepare,TopSelection,EmptyFallback}.lean`: Executed stopped records are refreshed/prepared using fresh exponent/configuration and satisfy exact original address selection. Positive ambient parameters plus the existing capacity implication derive the nonempty selected case; empty selection forces the existing direct fallback without a new branch. Three guarded checks and principal standard-axiom audit pass. Packed-child geometry/readiness and complete stopped recurrence costs remain unfinished; drafts are excluded from this checkpoint.

- `Networks/Certificates/PR589/Geometry/Dimensions/` and `Geometry/Moves/Model.lean`: All636 actual rational label dimensions are proved by exact spanning/dual certificates. Generic root-list subset certificates imply genuine subspace nesting and actual projector-difference rank, with ordered-list rank conversion. All44 Lean modules pass guarded checks;1981-declaration standard-axiom audit passes. Exact46-file manifest verified,42 generated modules reproduce,517 earlier files unchanged. Concrete nesting/ranks for the29250 phase plus661 final incidences, weighted moments and hosted costs remain open.
