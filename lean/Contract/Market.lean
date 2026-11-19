/-!
# Market's contract

The market data contract's formal definition: its records and its rules. The K-line and the ongoing
K-line, of whatever source gives them. The records are those of the contract's `.proto`, field for
field; each rule is a name and what holds of a record that keeps it. They are the contract's, in name
and meaning as the contract's Lean states them, and the contract takes them from the definition at a
release (`qi-v2-contracts`). What stays the contract's own is code to run or the wire's form: the
`.proto`, the reader of Protobuf's JSON (`ProtoJson`, the `FromJson` instances), the examples and the
program that checks them against the rules, Go and TypeScript. So this module imports nothing, where
the contract's Lean imports `Lean.Data.Json` for its reader alone.

A time is milliseconds since 1970-01-01 00:00:00 UTC: a K-line's `date`, an ongoing K-line's `asOf`.
A position is a K-line's place in its series, from 0: its `index`. A price or a volume is a number,
which needs no more than 6 decimal places; more is not refused.

A field of type `Nat` holds a uint64: a value with a field past 2⁶⁴ − 1 is no record on the wire,
which the contract's reader refuses. That bound is held by the reader alone, as in the contract's
Lean, not by the records here. `broken` and each rule's decision are computable, as the contract
states them, so that the contract's program that checks its examples evaluates them.
-/

namespace Market

/-- A rule of records of `α`: its name, and what holds of a record that keeps it. -/
structure Rule (α : Type) where
  name : String
  holds : α → Prop
  [dec : DecidablePred holds]

/-- The names of the rules of `rules` that `x` breaks, in their order. -/
def broken {α : Type} (rules : List (Rule α)) (x : α) : List String :=
  rules.filterMap fun r => if @decide _ (r.dec x) then none else some r.name

/-- A complete bar. -/
structure KLine where
  index : Nat
  date : Nat
  «open» : Float
  high : Float
  low : Float
  close : Float
  volume : Float
  deriving Repr

/-- A bar still going on. -/
structure OngoingKLine where
  index : Nat
  date : Nat
  «open» : Float
  high : Float
  low : Float
  close : Float
  volume : Float
  asOf : Nat
  deriving Repr

/-- Every price and the volume a finite number. -/
abbrev KLine.finite (k : KLine) : Prop := ∀ x ∈ [k.open, k.high, k.low, k.close, k.volume], x.isFinite

/-- The open and the close within the low and the high. -/
abbrev KLine.range (k : KLine) : Prop := k.low ≤ k.open ∧ k.low ≤ k.close ∧ k.open ≤ k.high ∧ k.close ≤ k.high

/-- The volume not negative. -/
abbrev KLine.volumeNotNegative (k : KLine) : Prop := 0 ≤ k.volume

def KLine.rules : List (Rule KLine) :=
  [⟨"finite", KLine.finite⟩, ⟨"range", KLine.range⟩, ⟨"volumeNotNegative", KLine.volumeNotNegative⟩]

/-- An ongoing K-line's fields as a K-line's. -/
def OngoingKLine.kline (o : OngoingKLine) : KLine := ⟨o.index, o.date, o.open, o.high, o.low, o.close, o.volume⟩

/-- Its values not updated before it began. -/
abbrev OngoingKLine.asOfNotBeforeDate (o : OngoingKLine) : Prop := o.date ≤ o.asOf

/-- An ongoing K-line's rules: its K-line's, and `asOfNotBeforeDate`. -/
def OngoingKLine.rules : List (Rule OngoingKLine) :=
  KLine.rules.map (fun r => @Rule.mk _ r.name (fun o => r.holds o.kline) (fun o => r.dec o.kline)) ++
    [⟨"asOfNotBeforeDate", OngoingKLine.asOfNotBeforeDate⟩]

end Market
