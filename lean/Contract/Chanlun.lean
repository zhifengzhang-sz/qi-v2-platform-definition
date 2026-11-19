/-!
# 缠论's contract

The chanlun contract's formal definition: its records and its rules. The records the algorithm of
缠论 makes beyond the K-line, of whatever implementation makes them: the merged bar (包含), the 分型,
the line (笔), the 线段, the 走势 and the 中枢. The contract says what a value is, not whether it is
right by the lessons, and not how records are gathered: a run of them, their order, and which is
still going on are their user's. The records are those of the contract's `.proto`, field for field;
each rule is a name and what holds of a record that keeps it. Each rule is of one record alone. They
are the contract's, in name and meaning as the contract's Lean states them (`qi-v2-contracts`). What
stays the contract's own: the `.proto`, the wire's form; the reader of Protobuf's JSON (`ProtoJson`,
the `FromJson` instances), code to run; the examples and the program that checks them against the
rules; Go and TypeScript. So this module imports nothing, where the contract's Lean imports
`Lean.Data.Json` for its reader alone.

A position is a K-line's place in its series, from 0, market's `KLine.index`: a merged bar's
`index`, `start`, `end`, `confirmEnd` and `extremes`. A bar is a merged bar's number, its `mIndex`,
from 0: a 分型's `mIndex`, a line's, a 线段's, a 走势's and a 中枢's `start`, `end` and `confirmEnd`.
A price is a number, which needs no more than 6 decimal places, more not refused: a merged bar's
`high` and `low`, a 中枢's `zg`, `zd`, `gg` and `dd`. A level is from 0: a 线段's, a 走势's and a
中枢's `level`. A `confirmEnd` not set means the record is still going on: a merged bar still
merging, a line not yet ended, a 中枢 under construction; one set is after the record's `end`
(`endBeforeConfirmEnd`).

A field of type `Nat` holds a uint64: a value with a field past 2⁶⁴ − 1 is no record on the wire,
which the contract's reader refuses. That bound is held by the reader alone, as in the contract's
Lean, not by the records here. `broken` and each rule's decision are computable, as the contract
states them, so that the contract's program that checks its examples evaluates them.
-/

namespace Chanlun

/-- A rule of records of `α`: its name, and what holds of a record that keeps it. -/
structure Rule (α : Type) where
  name : String
  holds : α → Prop
  [dec : DecidablePred holds]

/-- The names of the rules of `rules` that `x` breaks, in their order. -/
def broken {α : Type} (rules : List (Rule α)) (x : α) : List String :=
  rules.filterMap fun r => if @decide _ (r.dec x) then none else some r.name

/-- 包含's merged bar. -/
structure MergedBar where
  mIndex : Nat
  up : Bool
  start : Nat
  «end» : Nat
  confirmEnd : Option Nat
  extremes : List Nat
  index : Nat
  high : Float
  low : Float
  deriving Repr

/-- 分型. -/
structure Fractal where
  mIndex : Nat
  deriving Repr

/-- A line: a 笔. -/
structure Line where
  start : Nat
  «end» : Nat
  confirmEnd : Option Nat
  deriving Repr

/-- 线段 of a level. -/
structure Segment where
  start : Nat
  «end» : Nat
  confirmEnd : Option Nat
  level : Nat
  deriving Repr

/-- 走势 of a level. -/
structure Move where
  start : Nat
  «end» : Nat
  confirmEnd : Option Nat
  level : Nat
  deriving Repr

/-- 中枢 of a level. -/
structure Consolidation where
  level : Nat
  start : Nat
  «end» : Nat
  confirmEnd : Option Nat
  zg : Float
  zd : Float
  gg : Float
  dd : Float
  deriving Repr

/-- Its high and its low finite numbers. -/
abbrev MergedBar.finite (m : MergedBar) : Prop := m.high.isFinite ∧ m.low.isFinite

/-- Its low not above its high. -/
abbrev MergedBar.range (m : MergedBar) : Prop := m.low ≤ m.high

/-- Each of its extremes from its first K-line to its last. -/
abbrev MergedBar.extremesWithin (m : MergedBar) : Prop := ∀ p ∈ m.extremes, m.start ≤ p ∧ p ≤ m.«end»

/-- Its extremes in ascending order, none twice. -/
abbrev MergedBar.extremesAscending (m : MergedBar) : Prop := m.extremes.Pairwise (· < ·)

/-- Its index one of its extremes. -/
abbrev MergedBar.indexInExtremes (m : MergedBar) : Prop := m.index ∈ m.extremes

/-- Its last K-line before the K-line that confirmed it, if it is confirmed. -/
abbrev MergedBar.endBeforeConfirmEnd (m : MergedBar) : Prop := ∀ c ∈ m.confirmEnd, m.«end» < c

def MergedBar.rules : List (Rule MergedBar) :=
  [⟨"finite", MergedBar.finite⟩, ⟨"range", MergedBar.range⟩, ⟨"extremesWithin", MergedBar.extremesWithin⟩,
    ⟨"extremesAscending", MergedBar.extremesAscending⟩, ⟨"indexInExtremes", MergedBar.indexInExtremes⟩,
    ⟨"endBeforeConfirmEnd", MergedBar.endBeforeConfirmEnd⟩]

/-- Why no rule says a merged bar's first K-line is not after its last: its index is one of its extremes, which are
from its first to its last. -/
theorem MergedBar.startNotAfterEnd (m : MergedBar) (h : m.indexInExtremes) (w : m.extremesWithin) :
    m.start ≤ m.«end» :=
  Nat.le_trans (w m.index h).1 (w m.index h).2

/-- A 分型 has no rule. -/
def Fractal.rules : List (Rule Fractal) := []

/-- Its start before its end. -/
abbrev Line.startBeforeEnd (l : Line) : Prop := l.start < l.«end»

/-- Its end before the merged bar at which it was confirmed, if it is confirmed. -/
abbrev Line.endBeforeConfirmEnd (l : Line) : Prop := ∀ c ∈ l.confirmEnd, l.«end» < c

def Line.rules : List (Rule Line) :=
  [⟨"startBeforeEnd", Line.startBeforeEnd⟩, ⟨"endBeforeConfirmEnd", Line.endBeforeConfirmEnd⟩]

/-- Its start before its end. -/
abbrev Segment.startBeforeEnd (s : Segment) : Prop := s.start < s.«end»

/-- Its end before the merged bar at which it was confirmed, if it is confirmed. -/
abbrev Segment.endBeforeConfirmEnd (s : Segment) : Prop := ∀ c ∈ s.confirmEnd, s.«end» < c

def Segment.rules : List (Rule Segment) :=
  [⟨"startBeforeEnd", Segment.startBeforeEnd⟩, ⟨"endBeforeConfirmEnd", Segment.endBeforeConfirmEnd⟩]

/-- Its start before its end. -/
abbrev Move.startBeforeEnd (m : Move) : Prop := m.start < m.«end»

/-- Its end before the merged bar at which it was confirmed, if it is confirmed. -/
abbrev Move.endBeforeConfirmEnd (m : Move) : Prop := ∀ c ∈ m.confirmEnd, m.«end» < c

def Move.rules : List (Rule Move) :=
  [⟨"startBeforeEnd", Move.startBeforeEnd⟩, ⟨"endBeforeConfirmEnd", Move.endBeforeConfirmEnd⟩]

/-- Its band and its range finite numbers. -/
abbrev Consolidation.finite (c : Consolidation) : Prop := ∀ x ∈ [c.zg, c.zd, c.gg, c.dd], x.isFinite

/-- Its start before its end. -/
abbrev Consolidation.startBeforeEnd (c : Consolidation) : Prop := c.start < c.«end»

/-- Its band, ZD to ZG, within its range, DD to GG. -/
abbrev Consolidation.bands (c : Consolidation) : Prop := c.dd ≤ c.zd ∧ c.zd ≤ c.zg ∧ c.zg ≤ c.gg

/-- Its end before the merged bar at which it was confirmed, if it is confirmed. -/
abbrev Consolidation.endBeforeConfirmEnd (c : Consolidation) : Prop := ∀ b ∈ c.confirmEnd, c.«end» < b

def Consolidation.rules : List (Rule Consolidation) :=
  [⟨"finite", Consolidation.finite⟩, ⟨"startBeforeEnd", Consolidation.startBeforeEnd⟩,
    ⟨"bands", Consolidation.bands⟩, ⟨"endBeforeConfirmEnd", Consolidation.endBeforeConfirmEnd⟩]

end Chanlun
