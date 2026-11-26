import Kahn.Log
import Contract.Market

/-!
# The clean k-line stream, and the vendor's feed

The clean k-line stream is what the platform's components read: a log of market's k-lines, each
holding its place as its `index`, their dates rising, each keeping market's rules (`Valid`). A stream
here is a Kahn log, which only grows at its end and never changes what it holds (`Kahn.Log`); and
what reads a stream is a Kahn process, which never takes back what it has given (`Kahn.Process`).
How an implementation carries a log, Kafka say, is the implementation's: it shows that what each
reader reads is the log that was written.

The vendor's feed is the log of what the vendor says, as it is read: each statement one bar of one
window, with the time it was read (`Statement`, `Feed`). The features of the vendor's data that the
research collected (`docs/designs/research/stream.md`, Part 2) are stated of a feed, each shown on
the sample feed (`sample`), whose bars are invented to show them.

The clean data of a feed is a clean k-line stream that holds, of each window, the vendor's last word
on it (`CleanOf`). Each feed has its clean data, the sample feed's among them (`cleanOf_one`,
`cleanOf_two`); but no process gives the clean data of every feed (`no_process`). A process cannot
tell a feed that has ended from one that goes on, and the vendor can always say a later word on a
window: so what a process gives as a window's bar, the next statement can make wrong, and a process
never takes it back.
-/

namespace CleanStream

open Kahn Market

/-! ## The clean k-line stream -/

/-- A clean k-line stream: each k-line holds its place in the stream as its `index`, a later k-line
has a later date, and each k-line keeps market's rules. -/
structure Valid (c : Log KLine) : Prop where
  /-- each k-line's `index` is its place in the stream -/
  index : ∀ n k, c.get n = some k → k.index = n
  /-- a later k-line has a later date -/
  ascending : ∀ m n k k', m < n → c.get m = some k → c.get n = some k' → k.date < k'.date
  /-- each k-line keeps market's rules -/
  keeps : ∀ n k, c.get n = some k → k.Keeps

/-- A clean k-line stream has one k-line of each date it holds. -/
theorem Valid.date_inj {c : Log KLine} (h : Valid c) {m n : Nat} {k k' : KLine}
    (hm : c.get m = some k) (hn : c.get n = some k') (hd : k.date = k'.date) : m = n := by
  rcases Nat.lt_trichotomy m n with hl | he | hg
  · have := h.ascending m n k k' hl hm hn
    omega
  · exact he
  · have := h.ascending n m k' k hg hn hm
    omega

/-! ## The vendor's feed -/

/-- A bar as the vendor gives it: its window's start and its values. The vendor gives no place in a
series, no version, and no mark that the bar is final. -/
structure Bar where
  /-- its window's start: milliseconds since 1970-01-01 00:00:00 UTC -/
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

/-- The bar as market's k-line at place `i`. -/
def Bar.kline (b : Bar) (i : Nat) : KLine :=
  ⟨i, b.date, b.open, b.high, b.low, b.close, b.volume⟩

/-- A k-line's bar: its date and its values, without its place. -/
def barOf (k : KLine) : Bar :=
  ⟨k.date, k.open, k.high, k.low, k.close, k.volume⟩

theorem barOf_kline (b : Bar) (i : Nat) : barOf (b.kline i) = b := rfl

/-- One statement of the vendor, as it is read: one bar, and when it was read. -/
structure Statement where
  /-- the bar the vendor gave -/
  bar : Bar
  /-- when it was read: milliseconds since 1970-01-01 00:00:00 UTC -/
  readAt : Nat

/-- The vendor's feed: its statements, in the order they are read. That every log of statements is a
feed the vendor can give is a modelling choice, not a theorem: the vendor states no limit on when it
revises a bar, and marks no bar final (`docs/designs/research/stream.md`, features 1, 3 and 7). -/
abbrev Feed := Log Statement

/-- `b` is the vendor's last word on its window in the feed `s`: a statement of `s` gives `b`, and no
later statement of `s` is of `b`'s window. -/
def LastWord (s : Feed) (b : Bar) : Prop :=
  ∃ n st, s.get n = some st ∧ st.bar = b ∧
    ∀ m st', n < m → s.get m = some st' → st'.bar.date ≠ b.date

/-! ## The features of the vendor's data -/

/-- A bar is sent again, changed: two statements of one window give different bars. -/
def Resent (s : Feed) : Prop :=
  ∃ m n a b, m < n ∧ s.get m = some a ∧ s.get n = some b ∧ a.bar.date = b.bar.date ∧ a.bar ≠ b.bar

/-- Bars come out of date order: a later statement is of an earlier window. -/
def OutOfOrder (s : Feed) : Prop :=
  ∃ m n a b, m < n ∧ s.get m = some a ∧ s.get n = some b ∧ b.bar.date < a.bar.date

/-- A window of period `p` has no bar: the window after a statement's is one no statement is of,
though a statement of a later window comes. -/
def Missing (p : Nat) (s : Feed) : Prop :=
  ∃ m a, s.get m = some a ∧ (∃ n b, s.get n = some b ∧ a.bar.date + p < b.bar.date) ∧
    ∀ n b, s.get n = some b → b.bar.date ≠ a.bar.date + p

/-- A bar is revised late: a later statement of a window gives a different bar, read more than `δ`
milliseconds after the earlier one. -/
def RevisedAfter (δ : Nat) (s : Feed) : Prop :=
  ∃ m n a b, m < n ∧ s.get m = some a ∧ s.get n = some b ∧ a.bar.date = b.bar.date ∧
    a.bar ≠ b.bar ∧ a.readAt + δ < b.readAt

/-- A bar breaks market's rules. -/
def Broken (s : Feed) : Prop :=
  ∃ n a, s.get n = some a ∧ ¬ (a.bar.kline 0).Keeps

/-- A bar is of a window that had not begun when it was read: what a reading error gives, a time in
nanoseconds read as milliseconds say. -/
def NotYetBegun (s : Feed) : Prop :=
  ∃ n a, s.get n = some a ∧ a.readAt < a.bar.date

/-! ## The sample feed

Seven statements of one minute series, on 2026-09-10 from 09:30 Eastern (13:30 UTC). Its bars are
invented to show each feature. -/

/-- 2026-09-10 13:30:00 UTC, in milliseconds. -/
def t₀ : Nat := 1789047000000

/-- One minute, in milliseconds. -/
def minute : Nat := 60000

/-- One day, in milliseconds. -/
def day : Nat := 86400000

/-- The first minute's bar, as first sent. -/
def b₀ : Bar := ⟨t₀, 100.00, 100.50, 99.80, 100.20, 12000⟩

/-- The first minute's bar again, a late trade taken in: its high and its volume higher. -/
def b₀' : Bar := ⟨t₀, 100.00, 100.60, 99.80, 100.20, 12500⟩

/-- The first minute's bar a day later, a cancelled trade left out: its volume lower. -/
def b₀'' : Bar := ⟨t₀, 100.00, 100.60, 99.80, 100.20, 12400⟩

/-- The second minute's bar. -/
def b₁ : Bar := ⟨t₀ + minute, 100.20, 100.40, 100.00, 100.30, 8000⟩

/-- The fourth minute's bar: the third minute had no trade, and has none. -/
def b₃ : Bar := ⟨t₀ + 3 * minute, 100.30, 100.70, 100.10, 100.60, 9500⟩

/-- A bar whose low is above its high. -/
def bBroken : Bar := ⟨t₀ + 4 * minute, 100.60, 100.50, 100.70, 100.60, 7000⟩

/-- A bar whose date was read in the wrong unit: far in the future. -/
def bFuture : Bar := ⟨t₀ * 1000, 100.60, 100.90, 100.50, 100.80, 6000⟩

/-- The sample feed's statements, in the order read. -/
def sampleList : List Statement :=
  [⟨b₀, t₀ + minute + 2000⟩, ⟨b₁, t₀ + 2 * minute + 2000⟩, ⟨b₀', t₀ + 2 * minute + 30000⟩,
    ⟨b₃, t₀ + 4 * minute + 2000⟩, ⟨bBroken, t₀ + 5 * minute + 2000⟩,
    ⟨bFuture, t₀ + 6 * minute + 2000⟩, ⟨b₀'', t₀ + day + 3600000⟩]

/-- The sample feed. -/
def sample : Feed := Log.ofList sampleList

theorem b₀_ne_b₀' : b₀ ≠ b₀' := by
  intro h
  have hv : (12000 : Float) = 12500 := congrArg Bar.volume h
  have hl : (12000 : Float) < 12500 := by decide
  rw [hv] at hl
  exact absurd hl (by decide)

theorem b₀'_ne_b₀'' : b₀' ≠ b₀'' := by
  intro h
  have hv : (12500 : Float) = 12400 := congrArg Bar.volume h
  have hl : (12400 : Float) < 12500 := by decide
  rw [hv] at hl
  exact absurd hl (by decide)

/-- The sample feed sends a bar again, changed: the first minute's, at positions 0 and 2. -/
theorem sample_resent : Resent sample :=
  ⟨0, 2, _, _, by decide, rfl, rfl, rfl, b₀_ne_b₀'⟩

/-- The sample feed is out of date order: the first minute's bar again, after the second's. -/
theorem sample_outOfOrder : OutOfOrder sample :=
  ⟨1, 2, _, _, by decide, rfl, rfl, by decide⟩

/-- The sample feed has a minute with no bar: the third. -/
theorem sample_missing : Missing minute sample := by
  refine ⟨1, _, rfl, ⟨3, _, rfl, by decide⟩, ?_⟩
  intro n b h
  match n, h with
  | 0, h => cases h; decide
  | 1, h => cases h; decide
  | 2, h => cases h; decide
  | 3, h => cases h; decide
  | 4, h => cases h; decide
  | 5, h => cases h; decide
  | 6, h => cases h; decide
  | _ + 7, h => cases h

/-- The sample feed revises a bar more than a day after: the first minute's, at positions 2 and 6. -/
theorem sample_revisedAfter : RevisedAfter day sample :=
  ⟨2, 6, _, _, by decide, rfl, rfl, rfl, b₀'_ne_b₀'', by decide⟩

/-- The sample feed has a bar that breaks market's rules: its low above its high. -/
theorem sample_broken : Broken sample :=
  ⟨4, _, rfl, fun h => absurd h.range (by decide)⟩

/-- The sample feed has a bar of a window not yet begun when read. -/
theorem sample_notYetBegun : NotYetBegun sample :=
  ⟨5, _, rfl, by decide⟩

/-! ## The clean data of a feed -/

/-- The clean data of the feed `s`: a clean k-line stream each of whose k-lines is the vendor's last
word on its window in `s`, holding a k-line for each last word that keeps market's rules. -/
structure CleanOf (s : Feed) (c : Log KLine) : Prop where
  /-- it is a clean k-line stream -/
  valid : Valid c
  /-- each of its k-lines is the vendor's last word on its window -/
  last : ∀ n k, c.get n = some k → LastWord s (barOf k)
  /-- each last word that keeps market's rules is one of its k-lines -/
  complete : ∀ b, LastWord s b → (b.kline 0).Keeps → ∃ n k, c.get n = some k ∧ barOf k = b

/-- The feed of the one statement `⟨b, t⟩`. -/
def one (b : Bar) (t : Nat) : Feed := Log.ofList [⟨b, t⟩]

/-- The feed of the statement `⟨b, t⟩`, then the statement `⟨b', t'⟩`. -/
def two (b : Bar) (t : Nat) (b' : Bar) (t' : Nat) : Feed := Log.ofList [⟨b, t⟩, ⟨b', t'⟩]

/-- The feed of one statement extends to the feed with a second statement after it. -/
theorem one_le_two (b : Bar) (t : Nat) (b' : Bar) (t' : Nat) : one b t ≤ two b t b' t' :=
  Log.ofList_le_append (α := Statement) [⟨b, t⟩] [⟨b', t'⟩]

/-- A k-line that keeps market's rules keeps them at any place: its rules do not read its `index`. -/
theorem keeps_kline {b : Bar} (h : (b.kline 0).Keeps) (i : Nat) : (b.kline i).Keeps :=
  ⟨h.finite, h.range, h.volumeNotNegative⟩

/-- The one k-line `k`, as a stream. -/
def single (k : KLine) : Log KLine := Log.ofList [k]

theorem single_valid {b : Bar} (h : (b.kline 0).Keeps) : Valid (single (b.kline 0)) where
  index n k hk := by
    match n, hk with
    | 0, hk => cases hk; rfl
    | _ + 1, hk => cases hk
  ascending m n k k' hmn hm hn := by
    match m, n, hm, hn with
    | 0, 0, _, _ => omega
    | _ + 1, _, hm, _ => cases hm
    | _, _ + 1, _, hn => cases hn
  keeps n k hk := by
    match n, hk with
    | 0, hk => cases hk; exact h
    | _ + 1, hk => cases hk

/-- The last word of the feed of one statement is its bar. -/
theorem lastWord_one (b : Bar) (t : Nat) : LastWord (one b t) b :=
  ⟨0, _, rfl, rfl, fun m st' hm h => by
    match m, h with
    | _ + 1, h => cases h⟩

/-- The feed of one statement, its bar keeping market's rules, has that bar as its clean data. -/
theorem cleanOf_one {b : Bar} (t : Nat) (h : (b.kline 0).Keeps) :
    CleanOf (one b t) (single (b.kline 0)) where
  valid := single_valid h
  last n k hk := by
    match n, hk with
    | 0, hk => cases hk; exact lastWord_one b t
    | _ + 1, hk => cases hk
  complete b' hb' _ := by
    obtain ⟨n, st, hst, rfl, _⟩ := hb'
    match n, hst with
    | 0, hst => cases hst; exact ⟨0, _, rfl, rfl⟩
    | _ + 1, hst => cases hst

/-- After a second statement of the same window with a different bar, the first bar is no last word. -/
theorem not_lastWord_two {b b' : Bar} (t t' : Nat) (hd : b'.date = b.date) (hne : b' ≠ b) :
    ¬ LastWord (two b t b' t') b := by
  rintro ⟨n, st, hst, hb, hlast⟩
  match n, hst with
  | 0, _ => exact hlast 1 ⟨b', t'⟩ (by omega) rfl hd
  | 1, hst => cases hst; exact hne hb
  | _ + 2, hst => cases hst

/-- The last word of the feed of two statements of one window is the second's bar. -/
theorem lastWord_two (b : Bar) (t : Nat) (b' : Bar) (t' : Nat) : LastWord (two b t b' t') b' :=
  ⟨1, _, rfl, rfl, fun m st' hm h => by
    match m, h with
    | _ + 2, h => cases h⟩

/-- The feed of two statements of one window, the second's bar keeping market's rules, has the second
bar as its clean data. -/
theorem cleanOf_two {b b' : Bar} (t t' : Nat) (hd : b'.date = b.date)
    (h : (b'.kline 0).Keeps) : CleanOf (two b t b' t') (single (b'.kline 0)) where
  valid := single_valid h
  last n k hk := by
    match n, hk with
    | 0, hk => cases hk; exact lastWord_two b t b' t'
    | _ + 1, hk => cases hk
  complete b'' hb'' _ := by
    obtain ⟨n, st, hst, hb, hlast⟩ := hb''
    match n, hst with
    | 0, hst =>
      cases hst
      exact absurd (hb ▸ hd) (hlast 1 ⟨b', t'⟩ (by omega) rfl)
    | 1, hst => cases hst; subst hb; exact ⟨0, _, rfl, rfl⟩
    | _ + 2, hst => cases hst

/-! ## No process gives the clean data -/

/-- No process gives the clean data of every feed. Take a bar `b` that keeps market's rules, and a
different bar `b'` of the same window. The clean data of the feed of `b` alone holds `b`, so a process
that gives it gives `b`, at some place. The feed with `b'` after `b` extends that feed, so the process
gives `b` there too, at the same place: a process never takes back what it has given. But there `b`
is no last word on its window, `b'` is, so the process does not give that feed's clean data. -/
theorem no_process {b b' : Bar} (t t' : Nat) (hd : b'.date = b.date) (hne : b' ≠ b)
    (h : (b.kline 0).Keeps) (P : Process Feed (Log KLine)) : ¬ ∀ s, CleanOf s (P s) := by
  intro hP
  obtain ⟨n, k, hk, hbk⟩ := (hP (one b t)).complete b (lastWord_one b t) h
  have hk' : (P (two b t b' t')).get n = some k := P.mono (one_le_two b t b' t') n k hk
  have := (hP (two b t b' t')).last n k hk'
  rw [hbk] at this
  exact not_lastWord_two t t' hd hne this

/-- The sample's bars: no process gives the clean data of every feed, as the first minute's bar, sent
again changed (`b₀`, `b₀'`), shows. -/
theorem no_process_sample (P : Process Feed (Log KLine)) : ¬ ∀ s, CleanOf s (P s) :=
  no_process (b := b₀) (b' := b₀') 0 0 rfl (Ne.symm b₀_ne_b₀')
    ⟨by decide, by decide, by decide⟩ P

/-! ## The clean data, made outside the stream

The corollary of `no_process`: the clean data is made outside the streaming system, from a snapshot
of the feed, a finite list of statements taken as complete, by a function, not a process
(`construct`); it is stored, and acquisition feeds the stored clean series into the stream, cleaning
nothing (`feed`). The stream then holds the snapshot's clean data (`store_route`). -/

/-- The last words of a snapshot, in the order read: the bar of each statement that no later
statement of its window follows. -/
def lastWords : List Statement → List Bar
  | [] => []
  | st :: rest =>
    if rest.any (fun st' => st'.bar.date == st.bar.date) then lastWords rest
    else st.bar :: lastWords rest

theorem lastWords_cons (st : Statement) (rest : List Statement) :
    lastWords (st :: rest) =
      if rest.any (fun st' => st'.bar.date == st.bar.date) then lastWords rest
      else st.bar :: lastWords rest := rfl

theorem lastWord_cons_iff (st : Statement) (rest : List Statement) (b : Bar) :
    LastWord (Log.ofList (st :: rest)) b ↔
      (st.bar = b ∧ ∀ st' ∈ rest, st'.bar.date ≠ b.date) ∨ LastWord (Log.ofList rest) b := by
  constructor
  · rintro ⟨n, st₀, hst, hb, hlast⟩
    match n, hst with
    | 0, hst =>
      cases hst
      refine Or.inl ⟨hb, fun st' hmem => ?_⟩
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      exact hlast (i + 1) st' (by omega) hi
    | n + 1, hst =>
      exact Or.inr ⟨n, st₀, hst, hb, fun m st' hm h => hlast (m + 1) st' (by omega) h⟩
  · rintro (⟨hb, hrest⟩ | ⟨n, st₀, hst, hb, hlast⟩)
    · refine ⟨0, st, rfl, hb, fun m st' hm h => ?_⟩
      match m, h with
      | i + 1, h => exact hrest st' (List.mem_iff_getElem?.mpr ⟨i, h⟩)
    · refine ⟨n + 1, st₀, hst, hb, fun m st' hm h => ?_⟩
      match m, h with
      | i + 1, h => exact hlast i st' (by omega) h

theorem mem_lastWords_bar {l : List Statement} {b : Bar} (h : b ∈ lastWords l) :
    ∃ st ∈ l, st.bar = b := by
  induction l with
  | nil => cases h
  | cons st rest ih =>
    rw [lastWords_cons] at h
    split at h
    · obtain ⟨st', hm, hb⟩ := ih h
      exact ⟨st', List.mem_cons_of_mem _ hm, hb⟩
    · cases h with
      | head => exact ⟨st, List.mem_cons_self, rfl⟩
      | tail _ h =>
        obtain ⟨st', hm, hb⟩ := ih h
        exact ⟨st', List.mem_cons_of_mem _ hm, hb⟩

/-- A bar is among a snapshot's last words exactly when it is the vendor's last word on its window. -/
theorem mem_lastWords (l : List Statement) (b : Bar) :
    b ∈ lastWords l ↔ LastWord (Log.ofList l) b := by
  induction l with
  | nil =>
    constructor
    · intro h; cases h
    · rintro ⟨n, st, hst, _⟩; cases hst
  | cons st rest ih =>
    rw [lastWord_cons_iff, ← ih, lastWords_cons]
    split
    · next hany =>
      obtain ⟨st', hm, hd⟩ := List.any_eq_true.mp hany
      constructor
      · exact Or.inr
      · rintro (⟨hb, hrest⟩ | h)
        · exact absurd (hb ▸ beq_iff_eq.mp hd) (hrest st' hm)
        · exact h
    · next hany =>
      have hrest : ∀ st' ∈ rest, st'.bar.date ≠ st.bar.date := fun st' hm hd =>
        hany (List.any_eq_true.mpr ⟨st', hm, beq_iff_eq.mpr hd⟩)
      constructor
      · intro h
        cases h with
        | head => exact Or.inl ⟨rfl, hrest⟩
        | tail _ h => exact Or.inr h
      · rintro (⟨rfl, _⟩ | h)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h

/-- A snapshot's last words are of different windows. -/
theorem lastWords_dates (l : List Statement) :
    (lastWords l).Pairwise (fun a b => a.date ≠ b.date) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons st rest ih =>
    rw [lastWords_cons]
    split
    · exact ih
    · next hany =>
      refine List.pairwise_cons.mpr ⟨fun b hb hd => ?_, ih⟩
      obtain ⟨st', hm, rfl⟩ := mem_lastWords_bar hb
      exact hany (List.any_eq_true.mpr ⟨st', hm, beq_iff_eq.mpr hd.symm⟩)

/-- Whether a bar keeps market's rules, computed. -/
def keepsB (b : Bar) : Bool := (broken KLine.rules (b.kline 0)).isEmpty

theorem keepsB_iff (b : Bar) : keepsB b = true ↔ (b.kline 0).Keeps := by
  rw [← KLine.keeps_iff]
  unfold keepsB
  cases broken KLine.rules (b.kline 0) <;> simp

/-- A snapshot's last words that keep market's rules, in date order. -/
def sorted (l : List Statement) : List Bar :=
  ((lastWords l).filter keepsB).mergeSort (fun a b => decide (a.date ≤ b.date))

theorem mem_sorted (l : List Statement) (b : Bar) :
    b ∈ sorted l ↔ LastWord (Log.ofList l) b ∧ (b.kline 0).Keeps := by
  unfold sorted
  rw [List.mem_mergeSort, List.mem_filter, mem_lastWords, keepsB_iff]

theorem sorted_ascending (l : List Statement) :
    (sorted l).Pairwise (fun a b => a.date < b.date) := by
  have hle : (sorted l).Pairwise (fun a b => decide (a.date ≤ b.date) = true) := by
    unfold sorted
    exact List.pairwise_mergeSort (le := fun a b : Bar => decide (a.date ≤ b.date))
      (fun a b c hab hbc => decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _) _
  have hne : (sorted l).Pairwise (fun a b => a.date ≠ b.date) :=
    ((lastWords_dates l).filter keepsB).perm (List.mergeSort_perm _ _).symm (fun h => Ne.symm h)
  exact (hle.and hne).imp fun ⟨h₁, h₂⟩ => Nat.lt_of_le_of_ne (of_decide_eq_true h₁) h₂

/-- The clean data of a snapshot, made outside the stream: its last words that keep market's rules,
in date order, each at its place. -/
def construct (l : List Statement) : List KLine :=
  (sorted l).mapIdx fun i b => b.kline i

theorem construct_get {l : List Statement} {n : Nat} {k : KLine}
    (h : (Log.ofList (construct l)).get n = some k) : ∃ b, (sorted l)[n]? = some b ∧ k = b.kline n := by
  change (construct l)[n]? = some k at h
  unfold construct at h
  rw [List.getElem?_mapIdx] at h
  cases hb : (sorted l)[n]? with
  | none => rw [hb] at h; cases h
  | some b => rw [hb] at h; exact ⟨b, rfl, (Option.some.inj h).symm⟩

/-- What `construct` makes of a snapshot is the snapshot's clean data. -/
theorem cleanOf_construct (l : List Statement) :
    CleanOf (Log.ofList l) (Log.ofList (construct l)) where
  valid := {
    index := fun n k h => by
      obtain ⟨b, _, rfl⟩ := construct_get h
      rfl
    ascending := fun m n k k' hmn hm hn => by
      obtain ⟨b, hb, rfl⟩ := construct_get hm
      obtain ⟨b', hb', rfl⟩ := construct_get hn
      obtain ⟨hm', hbm⟩ := List.getElem?_eq_some_iff.mp hb
      obtain ⟨hn', hbn⟩ := List.getElem?_eq_some_iff.mp hb'
      have := List.pairwise_iff_getElem.mp (sorted_ascending l) m n hm' hn' hmn
      rw [hbm, hbn] at this
      exact this
    keeps := fun n k h => by
      obtain ⟨b, hb, rfl⟩ := construct_get h
      exact keeps_kline ((mem_sorted l b).mp (List.mem_of_getElem? hb)).2 n }
  last n k h := by
    obtain ⟨b, hb, rfl⟩ := construct_get h
    exact ((mem_sorted l b).mp (List.mem_of_getElem? hb)).1
  complete b hb hk := by
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp ((mem_sorted l b).mpr ⟨hb, hk⟩)
    refine ⟨n, b.kline n, ?_, rfl⟩
    change (construct l)[n]? = some (b.kline n)
    unfold construct
    rw [List.getElem?_mapIdx, hn]
    rfl

/-- Acquisition on the store route: it feeds the stored clean series into the stream as the store
holds it, cleaning nothing. While the store is only extended, the stream follows it (`feed.mono`);
a store made again is fed as a new stream. -/
noncomputable def feed : Process (Log KLine) (Log KLine) := Process.id

/-- The store route: the clean data of a snapshot, made outside the stream and stored, is fed into the
stream by acquisition, and the stream holds the snapshot's clean data. -/
theorem store_route (l : List Statement) :
    CleanOf (Log.ofList l) (feed (Log.ofList (construct l))) :=
  cleanOf_construct l

/-- The sample's clean data, made outside the stream. -/
theorem sample_clean : CleanOf sample (feed (Log.ofList (construct sampleList))) :=
  store_route sampleList

end CleanStream
