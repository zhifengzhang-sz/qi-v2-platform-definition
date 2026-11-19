/-!
# Market's contract

The market data contract's formal definition: its records, the K-line and the ongoing K-line, of
whatever source gives them, field for field the messages of the contract's `.proto`; and its rules,
each a name and what holds of a record that keeps it. This module is their home: they were read from
the contract's own Lean in name and meaning unchanged, for the contract to take from the definition
at a release. How an implementation follows them, and what is its own: `docs/guide/market.md`. This
module imports nothing.

Each field's doc comment says what it is and in what unit. A price or a volume needs no more than 6
decimal places; more is not refused. That a record keeps its contract is a structure of `Prop`s, one
field for each of its rules, by the rule's name (`KLine.Keeps`, …), and a record keeps it exactly when
it breaks none of its rules (`KLine.keeps_iff`, …, from `broken_eq_nil`).

A field of type `Nat` holds a uint64: a value with a field past 2⁶⁴ − 1 is no record on the wire. That
bound is held by the contract's reader alone, not by the records here. `broken` and each rule's
decision are computable, so that the contract's program that checks its examples evaluates them.
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

/-- A record breaks none of `rules` exactly when each of them holds of it. -/
theorem broken_eq_nil {α : Type} (rules : List (Rule α)) (x : α) :
    broken rules x = [] ↔ ∀ r ∈ rules, r.holds x := by
  induction rules with
  | nil => simp [broken]
  | cons r rs ih =>
    have hrs : broken (r :: rs) x =
        (if @decide _ (r.dec x) then none else some r.name).elim (broken rs x) (· :: broken rs x) := by
      simp only [broken, List.filterMap_cons]
      cases (if @decide _ (r.dec x) then none else some r.name) <;> rfl
    rw [hrs, List.forall_mem_cons, ← ih]
    by_cases h : r.holds x
    · simp [h]
    · simp [h]

/-- A complete bar. -/
structure KLine where
  /-- its place in its series, from 0: a position -/
  index : Nat
  /-- its begin time: milliseconds since 1970-01-01 00:00:00 UTC -/
  date : Nat
  /-- its open: a price -/
  «open» : Float
  /-- its high: a price -/
  high : Float
  /-- its low: a price -/
  low : Float
  /-- its close: a price -/
  close : Float
  /-- its volume -/
  volume : Float
  deriving Repr

/-- A bar still going on. -/
structure OngoingKLine where
  /-- the place it will take in its series when complete, from 0: a position -/
  index : Nat
  /-- its begin time: milliseconds since 1970-01-01 00:00:00 UTC -/
  date : Nat
  /-- its open: a price -/
  «open» : Float
  /-- its high: a price -/
  high : Float
  /-- its low: a price -/
  low : Float
  /-- its close: a price -/
  close : Float
  /-- its volume -/
  volume : Float
  /-- when its values were last updated: milliseconds since 1970-01-01 00:00:00 UTC -/
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

/-- A K-line keeps market's contract: each of its rules holds of it. -/
structure KLine.Keeps (k : KLine) : Prop where
  /-- every price and the volume a finite number -/
  finite : k.finite
  /-- the open and the close within the low and the high -/
  range : k.range
  /-- the volume not negative -/
  volumeNotNegative : k.volumeNotNegative

/-- A K-line keeps market's contract exactly when it breaks none of its rules. -/
theorem KLine.keeps_iff (k : KLine) : broken KLine.rules k = [] ↔ k.Keeps := by
  rw [broken_eq_nil]
  constructor
  · intro h
    exact ⟨h _ (.head _), h _ (.tail _ (.head _)), h _ (.tail _ (.tail _ (.head _)))⟩
  · intro h r hr
    unfold KLine.rules at hr
    cases hr with
    | head => exact h.finite
    | tail _ hr => cases hr with
      | head => exact h.range
      | tail _ hr => cases hr with
        | head => exact h.volumeNotNegative
        | tail _ hr => cases hr

/-- An ongoing K-line's fields as a K-line's. -/
def OngoingKLine.kline (o : OngoingKLine) : KLine := ⟨o.index, o.date, o.open, o.high, o.low, o.close, o.volume⟩

/-- Its values not updated before it began. -/
abbrev OngoingKLine.asOfNotBeforeDate (o : OngoingKLine) : Prop := o.date ≤ o.asOf

/-- An ongoing K-line's rules: its K-line's, and `asOfNotBeforeDate`. -/
def OngoingKLine.rules : List (Rule OngoingKLine) :=
  KLine.rules.map (fun r => @Rule.mk _ r.name (fun o => r.holds o.kline) (fun o => r.dec o.kline)) ++
    [⟨"asOfNotBeforeDate", OngoingKLine.asOfNotBeforeDate⟩]

/-- An ongoing K-line keeps market's contract: each of its rules holds of it. -/
structure OngoingKLine.Keeps (o : OngoingKLine) : Prop where
  /-- every price and the volume a finite number -/
  finite : o.kline.finite
  /-- the open and the close within the low and the high -/
  range : o.kline.range
  /-- the volume not negative -/
  volumeNotNegative : o.kline.volumeNotNegative
  /-- its values not updated before it began -/
  asOfNotBeforeDate : o.asOfNotBeforeDate

/-- An ongoing K-line keeps market's contract exactly when it breaks none of its rules. -/
theorem OngoingKLine.keeps_iff (o : OngoingKLine) : broken OngoingKLine.rules o = [] ↔ o.Keeps := by
  rw [broken_eq_nil]
  constructor
  · intro h
    exact ⟨h _ (.head _), h _ (.tail _ (.head _)), h _ (.tail _ (.tail _ (.head _))),
      h _ (.tail _ (.tail _ (.tail _ (.head _))))⟩
  · intro h r hr
    unfold OngoingKLine.rules KLine.rules at hr
    cases hr with
    | head => exact h.finite
    | tail _ hr => cases hr with
      | head => exact h.range
      | tail _ hr => cases hr with
        | head => exact h.volumeNotNegative
        | tail _ hr => cases hr with
          | head => exact h.asOfNotBeforeDate
          | tail _ hr => cases hr

end Market
