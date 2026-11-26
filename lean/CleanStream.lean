import Kahn.Prefix
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
window, with the time it was read (`Statement`, `Feed`); a statement read before its window began is
no word of the vendor's (`Statement.begun`). Four features of the vendor's data that the research
collected (`docs/designs/research/stream.md`, Part 2), and two kinds of error besides, are stated of
a feed, each shown on the sample feed (`sample`), whose bars are invented to show them.

The clean data of a feed is the clean k-line stream that holds, of each window whose last word keeps
market's rules, the vendor's last word on it (`CleanOf`); a feed has one at most (`CleanOf.unique`).
Every finite feed has it (`cleanOf_construct`), but no process gives it (`no_process_finite`,
`no_process`): a process cannot tell a feed that has ended from one that goes on, the vendor can
always say a later word on a window, and a process never takes back what it has given. A process
whose every k-line is always a last word gives nothing (`final_gives_nothing`).

The design takes two routes from this (`docs/designs/acquisition.md`). Route 1: the clean data is made
outside the stream, from a snapshot, by a function that is no process (`construct`,
`construct_not_process`), and passed into the stream as it is (`feed`, `store_route`). Route 2: the
settling rule on the raw topic of statements and watermarks (`Record`, `settle`, `settleP`).
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

/-- A bar as the vendor gives it: its window's start and its values. As the research reads the
vendor's documentation, a bar carries no place in a series, no version and no mark that it is final
(`docs/designs/research/stream.md`, Part 2). -/
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

/-- A statement read once its window had begun. One read before is no word of the vendor's: it is the
reading's error, a time in the wrong unit say (`docs/designs/research/stream.md`, feature 9). -/
def Statement.begun (st : Statement) : Bool := decide (st.bar.date ≤ st.readAt)

/-- `b` is the vendor's last word on its window in the feed `s`: a statement of `s` read once its
window had begun gives `b`, and no later statement of `s` so read is of `b`'s window. -/
def LastWord (s : Feed) (b : Bar) : Prop :=
  ∃ n st, s.get n = some st ∧ st.begun = true ∧ st.bar = b ∧
    ∀ m st', n < m → s.get m = some st' → st'.begun = true → st'.bar.date ≠ b.date

/-- A window has one last word at most. -/
theorem LastWord.unique {s : Feed} {b b' : Bar} (h : LastWord s b) (h' : LastWord s b')
    (hd : b.date = b'.date) : b = b' := by
  obtain ⟨n, st, hn, hb, rfl, hl⟩ := h
  obtain ⟨n', st', hn', hb', rfl, hl'⟩ := h'
  rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
  · exact absurd hd.symm (hl n' st' hlt hn' hb')
  · subst heq; rw [hn] at hn'; cases hn'; rfl
  · exact absurd hd (hl' n st hgt hn hb)

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

/-- A bar breaks market's rules: the vendor states no filter that keeps such a bar out
(`docs/designs/research/stream.md`, feature 6). -/
def Broken (s : Feed) : Prop :=
  ∃ n a, s.get n = some a ∧ ¬ (a.bar.kline 0).Keeps

/-- A statement read before its window began: what a reading error gives, a time in microseconds read
as milliseconds say (`docs/designs/research/stream.md`, feature 9). It is no word of the vendor's
(`Statement.begun`). -/
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

/-- A bar whose date was read in the wrong unit, microseconds as milliseconds: far in the future. -/
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
word on its window in `s`, holding each last word that keeps market's rules. A window whose last word
breaks them has no k-line in it, whatever was said of it before. -/
structure CleanOf (s : Feed) (c : Log KLine) : Prop where
  /-- it is a clean k-line stream -/
  valid : Valid c
  /-- each of its k-lines is the vendor's last word on its window -/
  last : ∀ n k, c.get n = some k → LastWord s (barOf k)
  /-- each last word that keeps market's rules is one of its k-lines -/
  complete : ∀ b, LastWord s b → (b.kline 0).Keeps → ∃ n k, c.get n = some k ∧ barOf k = b

theorem kline_ext {k k' : KLine} (h : barOf k = barOf k') (hi : k.index = k'.index) : k = k' := by
  cases k; cases k'
  simp only [barOf, Bar.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only at hi
  subst h1 h2 h3 h4 h5 h6 hi
  rfl

theorem barOf_date (k : KLine) : (barOf k).date = k.date := rfl

theorem keeps_barOf {k : KLine} (h : k.Keeps) : ((barOf k).kline 0).Keeps :=
  ⟨h.finite, h.range, h.volumeNotNegative⟩

/-- Two clean data of one feed that agree before position `n` agree at `n`. -/
theorem CleanOf.step {s : Feed} {c c' : Log KLine} (h : CleanOf s c) (h' : CleanOf s c') {n : Nat}
    (hagree : ∀ j, j < n → c.get j = c'.get j) {k : KLine} (hk : c.get n = some k) :
    c'.get n = some k := by
  obtain ⟨m, k', hm, hbk⟩ := h'.complete _ (h.last n k hk) (keeps_barOf (h.valid.keeps n k hk))
  have hdate : k'.date = k.date := by rw [← barOf_date, hbk, barOf_date]
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · rw [← hagree m hlt] at hm
    exact absurd (h.valid.date_inj hm hk hdate) (Nat.ne_of_lt hlt)
  · subst heq
    have := kline_ext hbk (by rw [h'.valid.index _ _ hm, h.valid.index _ _ hk])
    rw [hm, this]
  · obtain ⟨k₁, hk₁⟩ : ∃ k₁, c'.get n = some k₁ :=
      Option.ne_none_iff_exists'.mp (Log.get_ne_none_of_le hm (Nat.le_of_lt hgt))
    obtain ⟨j, k₂, hj, hbk₂⟩ :=
      h.complete _ (h'.last n k₁ hk₁) (keeps_barOf (h'.valid.keeps n k₁ hk₁))
    have hdate₂ : k₂.date = k₁.date := by rw [← barOf_date, hbk₂, barOf_date]
    rcases Nat.lt_trichotomy j n with hjl | hje | hjg
    · rw [hagree j hjl] at hj
      exact absurd (h'.valid.date_inj hj hk₁ hdate₂) (Nat.ne_of_lt hjl)
    · subst hje
      rw [hk] at hj
      cases hj
      exact absurd (h'.valid.date_inj hm hk₁ (hdate.trans hdate₂)) (Nat.ne_of_gt hgt)
    · have h1 := h.valid.ascending n j k k₂ hjg hk hj
      have h2 := h'.valid.ascending n m k₁ k' hgt hk₁ hm
      omega

theorem CleanOf.le {s : Feed} {c c' : Log KLine} (h : CleanOf s c) (h' : CleanOf s c') : c ≤ c' := by
  have hall : ∀ n, ∀ j, j < n → c.get j = c'.get j := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      intro j hj
      by_cases hjn : j < n
      · exact ih j hjn
      · have hjn' : j = n := by omega
        subst hjn'
        cases hk : c.get j with
        | some k => exact (h.step h' ih hk).symm
        | none =>
          cases hk' : c'.get j with
          | none => rfl
          | some k' =>
            have := h'.step h (fun i hi => (ih i hi).symm) hk'
            rw [hk] at this
            cases this
  intro n k hk
  rw [← hall (n + 1) n (by omega)]
  exact hk

/-- A feed has one clean data at most. -/
theorem CleanOf.unique {s : Feed} {c c' : Log KLine} (h : CleanOf s c) (h' : CleanOf s c') : c = c' :=
  Poset.antisymm (h.le h') (h'.le h)

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

/-- The last word of the feed of one statement, read once its window had begun, is its bar. -/
theorem lastWord_one (b : Bar) (t : Nat) (hb : (⟨b, t⟩ : Statement).begun = true) :
    LastWord (one b t) b :=
  ⟨0, _, rfl, hb, rfl, fun m st' hm h _ => by
    match m, h with
    | _ + 1, h => cases h⟩

/-- The feed of one statement, read once its window had begun, its bar keeping market's rules, has
that bar as its clean data. -/
theorem cleanOf_one {b : Bar} (t : Nat) (hb : (⟨b, t⟩ : Statement).begun = true)
    (h : (b.kline 0).Keeps) : CleanOf (one b t) (single (b.kline 0)) where
  valid := single_valid h
  last n k hk := by
    match n, hk with
    | 0, hk => cases hk; exact lastWord_one b t hb
    | _ + 1, hk => cases hk
  complete b' hb' _ := by
    obtain ⟨n, st, hst, _, rfl, _⟩ := hb'
    match n, hst with
    | 0, hst => cases hst; exact ⟨0, _, rfl, rfl⟩
    | _ + 1, hst => cases hst

/-- After a second statement of the same window, read once it had begun, with a different bar, the
first bar is no last word. -/
theorem not_lastWord_two {b b' : Bar} (t t' : Nat) (hd : b'.date = b.date) (hne : b' ≠ b)
    (hb' : (⟨b', t'⟩ : Statement).begun = true) : ¬ LastWord (two b t b' t') b := by
  rintro ⟨n, st, hst, _, hb, hlast⟩
  match n, hst with
  | 0, _ => exact hlast 1 ⟨b', t'⟩ (by omega) rfl hb' hd
  | 1, hst => cases hst; exact hne hb
  | _ + 2, hst => cases hst

/-- The last word of the feed of two statements of one window is the second's bar, read once its
window had begun. -/
theorem lastWord_two (b : Bar) (t : Nat) (b' : Bar) (t' : Nat)
    (hb' : (⟨b', t'⟩ : Statement).begun = true) : LastWord (two b t b' t') b' :=
  ⟨1, _, rfl, hb', rfl, fun m st' hm h _ => by
    match m, h with
    | _ + 2, h => cases h⟩

/-- The feed of two statements of one window, the second read once its window had begun and its bar
keeping market's rules, has the second bar as its clean data. -/
theorem cleanOf_two {b b' : Bar} (t t' : Nat) (hd : b'.date = b.date)
    (hb' : (⟨b', t'⟩ : Statement).begun = true) (h : (b'.kline 0).Keeps) :
    CleanOf (two b t b' t') (single (b'.kline 0)) where
  valid := single_valid h
  last n k hk := by
    match n, hk with
    | 0, hk => cases hk; exact lastWord_two b t b' t' hb'
    | _ + 1, hk => cases hk
  complete b'' hb'' _ := by
    obtain ⟨n, st, hst, _, hb, hlast⟩ := hb''
    match n, hst with
    | 0, hst =>
      cases hst
      exact absurd (hb ▸ hd) (hlast 1 ⟨b', t'⟩ (by omega) rfl hb')
    | 1, hst => cases hst; subst hb; exact ⟨0, _, rfl, rfl⟩
    | _ + 2, hst => cases hst

/-- The last word after one more statement: that statement's bar, if it was read once its window had
begun; or an earlier last word, of another window if that statement was so read. -/
theorem lastWord_snoc_iff (F : List Statement) (st : Statement) (b : Bar) :
    LastWord (Log.ofList (F ++ [st])) b ↔
      (st.begun = true ∧ st.bar = b) ∨
        (LastWord (Log.ofList F) b ∧ (st.begun = true → st.bar.date ≠ b.date)) := by
  have gF : ∀ m, m < F.length → (Log.ofList (F ++ [st])).get m = (Log.ofList F).get m :=
    fun m hm => List.getElem?_append_left hm
  have gst : (Log.ofList (F ++ [st])).get F.length = some st := List.getElem?_concat_length
  have gpast : ∀ m, F.length < m → (Log.ofList (F ++ [st])).get m = none := fun m hm =>
    List.getElem?_eq_none_iff.mpr (by simp; omega)
  have gF' : ∀ m x, (Log.ofList F).get m = some x → m < F.length := fun m x h =>
    (List.getElem?_eq_some_iff.mp h).1
  constructor
  · rintro ⟨n, st₀, hn, hb, rfl, hl⟩
    rcases Nat.lt_trichotomy n F.length with hlt | heq | hgt
    · refine Or.inr ⟨⟨n, st₀, by rw [← gF n hlt]; exact hn, hb, rfl, fun m st' hm h hb' => ?_⟩,
        fun hb' => hl F.length st hlt gst hb'⟩
      exact hl m st' hm (by rw [gF m (gF' m st' h)]; exact h) hb'
    · subst heq; rw [gst] at hn; cases hn; exact Or.inl ⟨hb, rfl⟩
    · rw [gpast n hgt] at hn; cases hn
  · rintro (⟨hb, rfl⟩ | ⟨⟨n, st₀, hn, hb, rfl, hl⟩, hst⟩)
    · refine ⟨F.length, st, gst, hb, rfl, fun m st' hm h _ => ?_⟩
      rw [gpast m hm] at h; cases h
    · have hnl := gF' n st₀ hn
      refine ⟨n, st₀, by rw [gF n hnl]; exact hn, hb, rfl, fun m st' hm h hb' => ?_⟩
      rcases Nat.lt_trichotomy m F.length with hml | hme | hmg
      · rw [gF m hml] at h; exact hl m st' hm h hb'
      · subst hme; rw [gst] at h; cases h; exact hst hb'
      · rw [gpast m hmg] at h; cases h

/-- Every bar has a different bar of the same window. -/
theorem exists_other (b : Bar) : ∃ b' : Bar, b'.date = b.date ∧ b' ≠ b := by
  by_cases h0 : b.volume = 0
  · refine ⟨{ b with volume := 1 }, rfl, fun h => ?_⟩
    have hv : (1 : Float) = b.volume := congrArg Bar.volume h
    rw [h0] at hv
    have h1 : (0 : Float) < 1 := by decide
    rw [hv] at h1
    exact absurd h1 (by decide)
  · exact ⟨{ b with volume := 0 }, rfl, fun h => h0 (congrArg Bar.volume h).symm⟩

/-! ## No process gives the clean data -/

/-- No process gives the clean data of every finite feed. Take a bar `b` that keeps market's rules,
and a different bar `b'` of the same window, each read once the window had begun. The clean data of
the feed of `b` alone holds `b`, so a process that gives it gives `b`, at some place. The feed with
`b'` after `b` extends that feed, so the process gives `b` there too, at the same place: a process
never takes back what it has given. But there `b` is no last word on its window, `b'` is. -/
theorem no_process_finite {b b' : Bar} (t t' : Nat) (hd : b'.date = b.date) (hne : b' ≠ b)
    (hb : (⟨b, t⟩ : Statement).begun = true) (hb' : (⟨b', t'⟩ : Statement).begun = true)
    (h : (b.kline 0).Keeps) (P : Process Feed (Log KLine)) :
    ¬ ∀ l, CleanOf (Log.ofList l) (P (Log.ofList l)) := by
  intro hP
  obtain ⟨n, k, hk, hbk⟩ := (hP [⟨b, t⟩]).complete b (lastWord_one b t hb) h
  have hk' : (P (two b t b' t')).get n = some k := P.mono (one_le_two b t b' t') n k hk
  have := (hP [⟨b, t⟩, ⟨b', t'⟩]).last n k hk'
  rw [hbk] at this
  exact not_lastWord_two t t' hd hne hb' this

/-- No process gives the clean data of every feed (`no_process_finite`). -/
theorem no_process {b b' : Bar} (t t' : Nat) (hd : b'.date = b.date) (hne : b' ≠ b)
    (hb : (⟨b, t⟩ : Statement).begun = true) (hb' : (⟨b', t'⟩ : Statement).begun = true)
    (h : (b.kline 0).Keeps) (P : Process Feed (Log KLine)) : ¬ ∀ s, CleanOf s (P s) :=
  fun hP => no_process_finite t t' hd hne hb hb' h P fun _ => hP _

/-- The sample's bars: no process gives the clean data of every feed, as the first minute's bar, sent
again changed (`b₀`, `b₀'`), shows. -/
theorem no_process_sample (P : Process Feed (Log KLine)) : ¬ ∀ s, CleanOf s (P s) :=
  no_process (b := b₀) (b' := b₀') t₀ t₀ rfl (Ne.symm b₀_ne_b₀') (by decide) (by decide)
    ⟨by decide, by decide, by decide⟩ P

/-- A process each of whose k-lines is always the vendor's last word on its window gives nothing, on
any finite feed: whatever it gives, the vendor may say that window again, changed. -/
theorem final_gives_nothing (P : Process Feed (Log KLine))
    (hP : ∀ l n k, (P (Log.ofList l)).get n = some k → LastWord (Log.ofList l) (barOf k))
    (l : List Statement) (n : Nat) : (P (Log.ofList l)).get n = none := by
  cases hk : (P (Log.ofList l)).get n with
  | none => rfl
  | some k =>
    exfalso
    obtain ⟨b', hd, hne⟩ := exists_other (barOf k)
    have hk' := P.mono (Log.ofList_le_append l [⟨b', b'.date⟩]) n k hk
    have hlw := (lastWord_snoc_iff l ⟨b', b'.date⟩ (barOf k)).mp (hP _ n k hk')
    have hb : (⟨b', b'.date⟩ : Statement).begun = true := by simp [Statement.begun]
    rcases hlw with ⟨_, h⟩ | ⟨_, h⟩
    · exact hne h
    · exact h hb hd

/-! ## Route 1: the clean data, made outside the stream

The first route the design takes from `no_process` (`docs/designs/acquisition.md`): the clean data is
made outside the streaming system, from a snapshot of the feed, a finite list of statements taken as
complete, by a function (`construct`) that is no process (`construct_not_process`); it is stored, and
acquisition passes the stored clean series into the stream, cleaning nothing (`feed`). -/

/-- Whether a statement is a last word in a snapshot: read once its window had begun, and no later
statement so read is of its window. -/
def lastHere (st : Statement) (rest : List Statement) : Bool :=
  st.begun && !(rest.any fun st' => st'.begun && st'.bar.date == st.bar.date)

theorem lastHere_iff (st : Statement) (rest : List Statement) :
    lastHere st rest = true ↔
      st.begun = true ∧ ∀ st' ∈ rest, st'.begun = true → st'.bar.date ≠ st.bar.date := by
  unfold lastHere
  rw [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false]
  simp only [Bool.and_eq_true, beq_iff_eq, not_and, ne_eq]

/-- The last words of a snapshot, in the order read. -/
def lastWords : List Statement → List Bar
  | [] => []
  | st :: rest => if lastHere st rest then st.bar :: lastWords rest else lastWords rest

theorem lastWords_cons (st : Statement) (rest : List Statement) :
    lastWords (st :: rest) = if lastHere st rest then st.bar :: lastWords rest else lastWords rest :=
  rfl

theorem lastWord_cons_iff (st : Statement) (rest : List Statement) (b : Bar) :
    LastWord (Log.ofList (st :: rest)) b ↔
      (st.begun = true ∧ st.bar = b ∧ ∀ st' ∈ rest, st'.begun = true → st'.bar.date ≠ b.date) ∨
        LastWord (Log.ofList rest) b := by
  constructor
  · rintro ⟨n, st₀, hst, hbg, hb, hlast⟩
    match n, hst with
    | 0, hst =>
      cases hst
      refine Or.inl ⟨hbg, hb, fun st' hmem hb' => ?_⟩
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      exact hlast (i + 1) st' (by omega) hi hb'
    | n + 1, hst =>
      exact Or.inr ⟨n, st₀, hst, hbg, hb, fun m st' hm h hb' => hlast (m + 1) st' (by omega) h hb'⟩
  · rintro (⟨hbg, hb, hrest⟩ | ⟨n, st₀, hst, hbg, hb, hlast⟩)
    · refine ⟨0, st, rfl, hbg, hb, fun m st' hm h hb' => ?_⟩
      match m, h with
      | i + 1, h => exact hrest st' (List.mem_iff_getElem?.mpr ⟨i, h⟩) hb'
    · refine ⟨n + 1, st₀, hst, hbg, hb, fun m st' hm h hb' => ?_⟩
      match m, h with
      | i + 1, h => exact hlast i st' (by omega) h hb'

theorem mem_lastWords_bar {l : List Statement} {b : Bar} (h : b ∈ lastWords l) :
    ∃ st ∈ l, st.begun = true ∧ st.bar = b := by
  induction l with
  | nil => cases h
  | cons st rest ih =>
    rw [lastWords_cons] at h
    split at h
    · next hl =>
      cases h with
      | head => exact ⟨st, List.mem_cons_self, ((lastHere_iff st rest).mp hl).1, rfl⟩
      | tail _ h =>
        obtain ⟨st', hm, hb, hbb⟩ := ih h
        exact ⟨st', List.mem_cons_of_mem _ hm, hb, hbb⟩
    · obtain ⟨st', hm, hb, hbb⟩ := ih h
      exact ⟨st', List.mem_cons_of_mem _ hm, hb, hbb⟩

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
    · next hl =>
      rw [lastHere_iff] at hl
      constructor
      · intro h
        cases h with
        | head => exact Or.inl ⟨hl.1, rfl, hl.2⟩
        | tail _ h => exact Or.inr h
      · rintro (⟨_, rfl, _⟩ | h)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h
    · next hl =>
      constructor
      · exact Or.inr
      · rintro (⟨hb, rfl, hrest⟩ | h)
        · exact absurd ((lastHere_iff st rest).mpr ⟨hb, hrest⟩) hl
        · exact h

/-- The last words after one more statement, as `lastWord_snoc_iff` gives them. -/
theorem mem_lastWords_snoc (F : List Statement) (st : Statement) (b : Bar) :
    b ∈ lastWords (F ++ [st]) ↔
      (st.begun = true ∧ st.bar = b) ∨ (b ∈ lastWords F ∧ (st.begun = true → st.bar.date ≠ b.date)) := by
  rw [mem_lastWords, mem_lastWords, lastWord_snoc_iff]

/-- A snapshot's last words are of different windows. -/
theorem lastWords_dates (l : List Statement) :
    (lastWords l).Pairwise (fun a b => a.date ≠ b.date) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons st rest ih =>
    rw [lastWords_cons]
    split
    · next hl =>
      rw [lastHere_iff] at hl
      refine List.pairwise_cons.mpr ⟨fun b hb hd => ?_, ih⟩
      obtain ⟨st', hm, hb', rfl⟩ := mem_lastWords_bar hb
      exact hl.2 st' hm hb' hd.symm
    · exact ih

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

/-- Bars of different windows, sorted by date, are in strictly rising date order. -/
theorem mergeSort_ascending {L : List Bar} (h : L.Pairwise (fun a b => a.date ≠ b.date)) :
    (L.mergeSort (fun a b => decide (a.date ≤ b.date))).Pairwise (fun a b => a.date < b.date) := by
  have hle := List.pairwise_mergeSort (le := fun a b : Bar => decide (a.date ≤ b.date))
    (fun a b c hab hbc => decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _) L
  have hne := h.perm (List.mergeSort_perm L (fun a b : Bar => decide (a.date ≤ b.date))).symm
    (fun h => Ne.symm h)
  exact (hle.and hne).imp fun ⟨h₁, h₂⟩ => Nat.lt_of_le_of_ne (of_decide_eq_true h₁) h₂

theorem sorted_ascending (l : List Statement) :
    (sorted l).Pairwise (fun a b => a.date < b.date) :=
  mergeSort_ascending ((lastWords_dates l).filter keepsB)

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

/-- Acquisition on route 1: it passes the stored clean series into the stream as the store holds it,
cleaning nothing; in the Lean, the process that passes its input on. That a store made again is fed as
a new stream is the design's (`docs/designs/acquisition.md`, Route 1), not this definition's. -/
noncomputable def feed : Process (Log KLine) (Log KLine) := Process.id

/-- Route 1: the clean data of a snapshot, made outside the stream and stored, passed into the stream
by acquisition: the stream holds the snapshot's clean data (`cleanOf_construct`, as `feed` passes its
input on). -/
theorem store_route (l : List Statement) :
    CleanOf (Log.ofList l) (feed (Log.ofList (construct l))) :=
  cleanOf_construct l

/-- The sample's clean data, made outside the stream. -/
theorem sample_clean : CleanOf sample (feed (Log.ofList (construct sampleList))) :=
  store_route sampleList

/-- The far-future bar, read before its window began, is not in the sample's clean data. -/
theorem sample_clean_no_future (n : Nat) (k : KLine)
    (h : (Log.ofList (construct sampleList)).get n = some k) : barOf k ≠ bFuture := by
  intro hb
  obtain ⟨m, st, hst, hbg, hsb, _⟩ := (cleanOf_construct sampleList).last n k h
  have hall : ∀ st ∈ sampleList, st.bar.date = bFuture.date → st.begun = false := by decide
  rw [hb] at hsb
  have := hall st (List.mem_of_getElem? hst) (by rw [hsb])
  rw [hbg] at this
  cases this

/-- The construction is no process: no process gives, for every snapshot, what `construct` makes of
it (`no_process_finite`). -/
theorem construct_not_process :
    ¬ ∃ P : Process Feed (Log KLine), ∀ l, P (Log.ofList l) = Log.ofList (construct l) := by
  rintro ⟨P, hP⟩
  exact no_process_finite (b := b₀) (b' := b₀') t₀ t₀ rfl (Ne.symm b₀_ne_b₀') (by decide) (by decide)
    ⟨by decide, by decide, by decide⟩ P fun l => by rw [hP]; exact cleanOf_construct l

/-! ## Route 2: the vendor's data in the stream

The raw topic is the log of acquisition's records: the vendor's statements as read, and watermarks
(`Record`). The settling rule gives, of each window, its last version read by the first watermark at
or after the window's end plus the settling delay `d`, if it keeps market's rules (`settle`; as a
process, `settleP`). On any raw topic, endless ones among them, it gives a clean k-line stream
(`settleP_valid`). With a period above 0: of a finite raw topic with no late word, it gives exactly the last words that keep
market's rules on the windows a due watermark has been read for (`settle_settled`); of one on time,
the clean data (`settle_clean`, `settleP_clean`), which is what `construct` makes
(`settle_eq_construct`); and it gives whatever a rule that gives the clean data of every raw topic on
time gives (`settle_earliest`). A settled window said again, changed, makes it differ from the clean
data (`settle_late`); no process gives the clean data of every finite raw topic (`no_process_raw`), and
none is both live and final (`no_live_final`). -/

/-- A record of the raw topic: a statement of the vendor, as read, or a watermark. -/
inductive Record where
  /-- a statement of the vendor, as read -/
  | said (st : Statement)
  /-- a watermark: a time up to which acquisition has read the vendor with no gap. That it is so is
  acquisition's to make true: the Lean takes each watermark as written, a modelling choice. -/
  | mark (t : Nat)

/-- When a window settles: its date, plus the period `p` (its end), plus the settling delay `d`. -/
def due (p d : Nat) (b : Bar) : Nat := b.date + p + d

/-- The settling rule's state, after what has been read so far. -/
structure Settling where
  /-- the greatest watermark read, 0 before any -/
  mark : Nat
  /-- the last version read of each window not yet settled -/
  pending : List Bar
  /-- the settled series so far -/
  out : List KLine

/-- The bars of `pending` that settle at the watermark `t` and keep market's rules, in date order. -/
def settling (p d t : Nat) (pending : List Bar) : List Bar :=
  ((pending.filter fun b => decide (due p d b ≤ t)).filter keepsB).mergeSort
    fun a b => decide (a.date ≤ b.date)

theorem mem_settling {p d t : Nat} {pending : List Bar} {b : Bar} :
    b ∈ settling p d t pending ↔ (b ∈ pending ∧ due p d b ≤ t) ∧ (b.kline 0).Keeps := by
  unfold settling
  rw [List.mem_mergeSort, List.mem_filter, List.mem_filter, keepsB_iff, decide_eq_true_eq]

/-- One record read. A statement read before its window began is no word, and is left out. A statement
of a window no due watermark has been read for replaces the window's version; one of a window a due
watermark has been read for is a correction, which the settled series does not take. A watermark
settles each window due by it: those that keep market's rules join the settled series, in date order,
each at its place. -/
def Settling.step (p d : Nat) (σ : Settling) : Record → Settling
  | .said st =>
    if st.begun = true ∧ σ.mark < due p d st.bar then
      { σ with pending := st.bar :: σ.pending.filter fun b => b.date != st.bar.date }
    else σ
  | .mark t =>
    { mark := max σ.mark t
      pending := σ.pending.filter fun b => !decide (due p d b ≤ t)
      out := σ.out ++ (settling p d t σ.pending).mapIdx fun i b => b.kline (σ.out.length + i) }

/-- Nothing read yet. -/
def Settling.init : Settling := ⟨0, [], []⟩

/-- The settled series of what has been read: the settling rule on a finite list of records. -/
def settle (p d : Nat) (l : List Record) : List KLine :=
  (l.foldl (Settling.step p d) Settling.init).out

theorem step_out (p d : Nat) (σ : Settling) (r : Record) :
    ∃ x, (σ.step p d r).out = σ.out ++ x := by
  cases r with
  | said st =>
    refine ⟨[], ?_⟩
    simp only [Settling.step]
    split <;> simp
  | mark t => exact ⟨_, rfl⟩

theorem foldl_out (p d : Nat) (r : List Record) (σ : Settling) :
    ∃ x, (r.foldl (Settling.step p d) σ).out = σ.out ++ x := by
  induction r generalizing σ with
  | nil => exact ⟨[], by simp⟩
  | cons x r ih =>
    obtain ⟨y, hy⟩ := step_out p d σ x
    obtain ⟨z, hz⟩ := ih (σ.step p d x)
    exact ⟨y ++ z, by simp only [List.foldl_cons]; rw [hz, hy, List.append_assoc]⟩

theorem eq_append_of_ofList_le {α : Type} {l l' : List α} (h : Log.ofList l ≤ Log.ofList l') :
    l' = l ++ l'.drop l.length := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < l.length
  · rw [List.getElem?_append_left hn]
    obtain ⟨a, ha⟩ : ∃ a, l[n]? = some a := ⟨l[n], List.getElem?_eq_getElem hn⟩
    rw [ha]
    exact h n a ha
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
    congr 1
    omega

/-- The settling rule only adds to the settled series as more is read. -/
theorem settle_extends (p d : Nat) : Log.Extends (settle p d) := by
  intro l l' h
  rw [eq_append_of_ofList_le h]
  unfold settle
  rw [List.foldl_append]
  obtain ⟨x, hx⟩ := foldl_out p d (l'.drop l.length) (l.foldl (Settling.step p d) Settling.init)
  rw [hx]
  exact Log.ofList_le_append _ _

/-- The settling rule as a process on the raw topic: acquisition's part on route 2. -/
noncomputable def settleP (p d : Nat) : Process (Log Record) (Log KLine) :=
  Log.ofPrefix (settle p d) (settle_extends p d)

/-- What the settling rule keeps true of its state. -/
structure Settling.Good (p d : Nat) (σ : Settling) : Prop where
  index : ∀ (i : Nat) (k : KLine), σ.out[i]? = some k → k.index = i
  ascending : ∀ (i j : Nat) (k k' : KLine), i < j → σ.out[i]? = some k → σ.out[j]? = some k' →
    k.date < k'.date
  keeps : ∀ (i : Nat) (k : KLine), σ.out[i]? = some k → k.Keeps
  outDue : ∀ (i : Nat) (k : KLine), σ.out[i]? = some k → k.date + p + d ≤ σ.mark
  pendingDue : ∀ b ∈ σ.pending, σ.mark < due p d b
  pendingDates : σ.pending.Pairwise fun a b => a.date ≠ b.date

theorem good_init (p d : Nat) : Settling.init.Good p d where
  index _ _ h := by cases h
  ascending _ _ _ _ _ h := by cases h
  keeps _ _ h := by cases h
  outDue _ _ h := by cases h
  pendingDue _ h := by cases h
  pendingDates := List.Pairwise.nil

theorem get_out_mark {σ : Settling} {p d t i : Nat} {k : KLine}
    (h : (σ.out ++ (settling p d t σ.pending).mapIdx fun i b => b.kline (σ.out.length + i))[i]? = some k) :
    (i < σ.out.length ∧ σ.out[i]? = some k) ∨
      (σ.out.length ≤ i ∧ ∃ b, (settling p d t σ.pending)[i - σ.out.length]? = some b ∧ k = b.kline i) := by
  by_cases hi : i < σ.out.length
  · rw [List.getElem?_append_left hi] at h
    exact Or.inl ⟨hi, h⟩
  · rw [List.getElem?_append_right (by omega), List.getElem?_mapIdx] at h
    cases hb : (settling p d t σ.pending)[i - σ.out.length]? with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      refine Or.inr ⟨by omega, b, rfl, ?_⟩
      have := (Option.some.inj h).symm
      rw [this, show σ.out.length + (i - σ.out.length) = i by omega]

theorem good_step {p d : Nat} {σ : Settling} (h : σ.Good p d) (r : Record) : (σ.step p d r).Good p d := by
  cases r with
  | said st =>
    simp only [Settling.step]
    split
    · next hlt =>
      exact {
        index := h.index, ascending := h.ascending, keeps := h.keeps, outDue := h.outDue
        pendingDue := fun b hb => by
          cases hb with
          | head => exact hlt.2
          | tail _ hb => exact h.pendingDue b (List.mem_filter.mp hb).1
        pendingDates := by
          refine List.pairwise_cons.mpr ⟨fun b hb => ?_, h.pendingDates.filter _⟩
          have := (List.mem_filter.mp hb).2
          simp only [bne_iff_ne, ne_eq] at this
          exact Ne.symm this }
    · exact h
  | mark t =>
    have hS := mergeSort_ascending (((h.pendingDates.filter (fun b => decide (due p d b ≤ t)))).filter keepsB)
    have hmemS : ∀ j b, (settling p d t σ.pending)[j]? = some b →
        (b ∈ σ.pending ∧ due p d b ≤ t) ∧ (b.kline 0).Keeps :=
      fun j b hb => mem_settling.mp (List.mem_of_getElem? hb)
    exact {
      index := fun i k hk => by
        rcases get_out_mark hk with ⟨_, hk⟩ | ⟨_, b, _, rfl⟩
        · exact h.index i k hk
        · rfl
      ascending := fun i j k k' hij hi hj => by
        rcases get_out_mark hi with ⟨_, hi⟩ | ⟨hi1, b, hb, rfl⟩
        · rcases get_out_mark hj with ⟨_, hj⟩ | ⟨_, b', hb', rfl⟩
          · exact h.ascending i j k k' hij hi hj
          · have h1 := h.outDue i k hi
            have h2 := h.pendingDue b' (hmemS _ b' hb').1.1
            unfold due at h2
            show k.date < b'.date
            omega
        · rcases get_out_mark hj with ⟨hj1, _⟩ | ⟨_, b', hb', rfl⟩
          · omega
          · obtain ⟨hl, hbb⟩ := List.getElem?_eq_some_iff.mp hb
            obtain ⟨hl', hbb'⟩ := List.getElem?_eq_some_iff.mp hb'
            have := List.pairwise_iff_getElem.mp hS (i - σ.out.length) (j - σ.out.length) hl hl' (by omega)
            unfold settling at hbb hbb'
            rw [hbb, hbb'] at this
            exact this
      keeps := fun i k hk => by
        rcases get_out_mark hk with ⟨_, hk⟩ | ⟨_, b, hb, rfl⟩
        · exact h.keeps i k hk
        · exact keeps_kline (hmemS _ b hb).2 i
      outDue := fun i k hk => by
        rcases get_out_mark hk with ⟨_, hk⟩ | ⟨_, b, hb, rfl⟩
        · exact Nat.le_trans (h.outDue i k hk) (Nat.le_max_left _ _)
        · have := (hmemS _ b hb).1.2
          unfold due at this
          exact Nat.le_trans this (Nat.le_max_right _ _)
      pendingDue := fun b hb => by
        obtain ⟨hb, hnot⟩ := List.mem_filter.mp hb
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hnot
        exact Nat.max_lt.mpr ⟨h.pendingDue b hb, hnot⟩
      pendingDates := h.pendingDates.filter _ }

theorem good_foldl (p d : Nat) (r : List Record) {σ : Settling} (h : σ.Good p d) :
    (r.foldl (Settling.step p d) σ).Good p d := by
  induction r generalizing σ with
  | nil => exact h
  | cons x r ih => exact ih (good_step h x)

/-- The settled series of a finite list of records is a clean k-line stream. -/
theorem settle_valid (p d : Nat) (l : List Record) : Valid (Log.ofList (settle p d l)) :=
  let h := good_foldl p d l (good_init p d)
  { index := h.index, ascending := h.ascending, keeps := h.keeps }

/-- The limit of a chain of clean k-line streams is one. -/
theorem Valid.sup (c : Chain (Log KLine)) (h : ∀ i, Valid (c i)) : Valid (Domain.sup c) where
  index n k hk := by
    obtain ⟨i, hi⟩ := (Log.get_sup c n k).mp hk
    exact (h i).index n k hi
  ascending m n k k' hmn hm hn := by
    obtain ⟨i, hi⟩ := (Log.get_sup c m k).mp hm
    obtain ⟨j, hj⟩ := (Log.get_sup c n k').mp hn
    exact (h (max i j)).ascending m n k k' hmn (c.mono (Nat.le_max_left i j) m k hi)
      (c.mono (Nat.le_max_right i j) n k' hj)
  keeps n k hk := by
    obtain ⟨i, hi⟩ := (Log.get_sup c n k).mp hk
    exact (h i).keeps n k hi

/-- Whatever the raw topic holds, the settling rule gives a clean k-line stream. -/
theorem settleP_valid (p d : Nat) (s : Log Record) : Valid (settleP p d s) :=
  Valid.sup _ fun k => settle_valid p d (Log.toList s k)

/-! ### How the settled series relates to the clean data -/

/-- The vendor's statements among the records, in order. -/
def feedOf (l : List Record) : List Statement :=
  l.filterMap fun r => match r with
    | .said st => some st
    | .mark _ => none

theorem feedOf_said (l : List Record) (st : Statement) : feedOf (l ++ [.said st]) = feedOf l ++ [st] := by
  simp [feedOf, List.filterMap_append]

theorem feedOf_mark (l : List Record) (t : Nat) : feedOf (l ++ [.mark t]) = feedOf l := by
  simp [feedOf, List.filterMap_append]

theorem mem_feedOf {l : List Record} {st : Statement} : st ∈ feedOf l ↔ Record.said st ∈ l := by
  unfold feedOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, h⟩
    cases r with
    | said st' => cases h; exact hr
    | mark _ => cases h
  · intro h
    exact ⟨_, h, rfl⟩

/-- The vendor says nothing of a window once a watermark due for it has been read: of no statement is
a watermark read before it due. -/
def NoLateWord (p d : Nat) (l : List Record) : Prop :=
  ∀ (i j t : Nat) (st : Statement), i < j → l[i]? = some (Record.mark t) →
    l[j]? = some (Record.said st) → t < due p d st.bar

/-- The raw topic is on time: the vendor says nothing of a window once it has settled, and every window
it speaks of settles. -/
structure OnTime (p d : Nat) (l : List Record) : Prop where
  /-- nothing is said of a window once a watermark due for it has been read -/
  noLateWord : NoLateWord p d l
  /-- a watermark due for every window spoken of, by a statement read once it had begun, is read -/
  settles : ∀ st, Record.said st ∈ l → st.begun = true → ∃ t, Record.mark t ∈ l ∧ due p d st.bar ≤ t

/-- What the settled series of what has been read is, in terms of the vendor's last words. -/
structure Settling.Inv (p d : Nat) (pre : List Record) (σ : Settling) : Prop where
  markOf : σ.mark = 0 ∨ Record.mark σ.mark ∈ pre
  markGe : ∀ t, Record.mark t ∈ pre → t ≤ σ.mark
  pending : ∀ b, b ∈ σ.pending ↔ b ∈ lastWords (feedOf pre) ∧ σ.mark < due p d b
  out : ∀ b, (∃ (i : Nat) (k : KLine), σ.out[i]? = some k ∧ barOf k = b) ↔
    b ∈ lastWords (feedOf pre) ∧ (b.kline 0).Keeps ∧ due p d b ≤ σ.mark

theorem inv_init (p d : Nat) : Settling.init.Inv p d [] where
  markOf := Or.inl rfl
  markGe _ h := by cases h
  pending b := by simp [Settling.init, feedOf, lastWords]
  out b := by
    constructor
    · rintro ⟨i, k, h, _⟩; cases h
    · rintro ⟨h, _⟩; simp [feedOf, lastWords] at h

theorem due_ne_of_date {p d : Nat} {a b : Bar} (h : due p d a ≠ due p d b) : a.date ≠ b.date := by
  intro hd; unfold due at h; rw [hd] at h; exact h rfl

theorem inv_step_said {p d : Nat} (hp : 0 < p) {pre : List Record} {σ : Settling}
    (h : σ.Inv p d pre) (st : Statement) (hlate : ∀ t, Record.mark t ∈ pre → t < due p d st.bar) :
    (σ.step p d (.said st)).Inv p d (pre ++ [.said st]) := by
  have hlt : σ.mark < due p d st.bar := by
    rcases h.markOf with h0 | hm
    · rw [h0]; unfold due; omega
    · exact hlate _ hm
  have hmarkOf : σ.mark = 0 ∨ Record.mark σ.mark ∈ pre ++ [.said st] := by
    rcases h.markOf with h0 | hm
    · exact Or.inl h0
    · exact Or.inr (List.mem_append_left _ hm)
  have hmarkGe : ∀ t, Record.mark t ∈ pre ++ [.said st] → t ≤ σ.mark := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact h.markGe t ht
    · simp at ht
  by_cases hb : st.begun = true
  · simp only [Settling.step, hb, hlt, and_self, ↓reduceIte]
    refine ⟨hmarkOf, hmarkGe, fun b => ?_, fun b => ?_⟩
    · show b ∈ st.bar :: σ.pending.filter _ ↔ _
      rw [feedOf_said, mem_lastWords_snoc, List.mem_cons, List.mem_filter, h.pending]
      simp only [bne_iff_ne, ne_eq, hb, true_and, true_implies]
      constructor
      · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨Or.inl rfl, hlt⟩
        · exact ⟨Or.inr ⟨h1, fun hd => h3 hd.symm⟩, h2⟩
      · rintro ⟨h1 | ⟨h1, h3⟩, h2⟩
        · exact Or.inl h1.symm
        · exact Or.inr ⟨⟨h1, h2⟩, fun hd => h3 hd.symm⟩
    · show (∃ (i : Nat) (k : KLine), σ.out[i]? = some k ∧ barOf k = b) ↔ _
      rw [h.out, feedOf_said, mem_lastWords_snoc]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have hne : st.bar.date ≠ b.date :=
          Ne.symm (due_ne_of_date (p := p) (d := d) (by omega))
        exact ⟨Or.inr ⟨h1, fun _ => hne⟩, h2, h3⟩
      · rintro ⟨⟨_, h1⟩ | ⟨h1, _⟩, h2, h3⟩
        · subst h1; exact absurd (show due p d st.bar ≤ σ.mark from h3) (Nat.not_le.mpr hlt)
        · exact ⟨h1, h2, h3⟩
  · simp only [Settling.step, hb]
    have hsame : ∀ b, b ∈ lastWords (feedOf (pre ++ [.said st])) ↔ b ∈ lastWords (feedOf pre) := by
      intro b
      rw [feedOf_said, mem_lastWords_snoc]
      simp [hb]
    refine ⟨hmarkOf, hmarkGe, fun b => ?_, fun b => ?_⟩
    · rw [hsame]; exact h.pending b
    · rw [hsame]; exact h.out b

theorem inv_step_mark {p d : Nat} {pre : List Record} {σ : Settling} (h : σ.Inv p d pre) (t : Nat) :
    (σ.step p d (.mark t)).Inv p d (pre ++ [.mark t]) := by
  simp only [Settling.step]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show max σ.mark t = 0 ∨ Record.mark (max σ.mark t) ∈ pre ++ [.mark t]
    rcases Nat.le_total σ.mark t with hle | hle
    · rw [Nat.max_eq_right hle]; exact Or.inr (by simp)
    · rw [Nat.max_eq_left hle]
      rcases h.markOf with h0 | hm
      · exact Or.inl h0
      · exact Or.inr (List.mem_append_left _ hm)
  · intro t' ht'
    show t' ≤ max σ.mark t
    rcases List.mem_append.mp ht' with ht' | ht'
    · exact Nat.le_trans (h.markGe t' ht') (Nat.le_max_left _ _)
    · simp at ht'; rw [ht']; exact Nat.le_max_right _ _
  · intro b
    show b ∈ σ.pending.filter _ ↔ b ∈ lastWords (feedOf (pre ++ [.mark t])) ∧ max σ.mark t < due p d b
    rw [feedOf_mark, List.mem_filter, h.pending, Nat.max_lt]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  · intro b
    show (∃ i k, (σ.out ++ (settling p d t σ.pending).mapIdx fun i b => b.kline (σ.out.length + i))[i]? =
        some k ∧ barOf k = b) ↔ b ∈ lastWords (feedOf (pre ++ [.mark t])) ∧ (b.kline 0).Keeps ∧
        due p d b ≤ max σ.mark t
    rw [feedOf_mark]
    constructor
    · rintro ⟨i, k, hk, rfl⟩
      rcases get_out_mark hk with ⟨_, hk⟩ | ⟨_, b', hb', rfl⟩
      · obtain ⟨h1, h2, h3⟩ := (h.out (barOf k)).mp ⟨i, k, hk, rfl⟩
        exact ⟨h1, h2, Nat.le_trans h3 (Nat.le_max_left _ _)⟩
      · obtain ⟨⟨hp, hdue⟩, hkeeps⟩ := mem_settling.mp (List.mem_of_getElem? hb')
        exact ⟨((h.pending b').mp hp).1, hkeeps, Nat.le_trans hdue (Nat.le_max_right _ _)⟩
    · rintro ⟨h1, h2, h3⟩
      by_cases hm : due p d b ≤ σ.mark
      · obtain ⟨i, k, hk, hb⟩ := (h.out b).mpr ⟨h1, h2, hm⟩
        exact ⟨i, k, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]; exact hk, hb⟩
      · have hdt : due p d b ≤ t := by
          rcases Nat.le_total σ.mark t with hle | hle
          · rw [Nat.max_eq_right hle] at h3; exact h3
          · rw [Nat.max_eq_left hle] at h3; exact absurd h3 hm
        have hmem : b ∈ settling p d t σ.pending :=
          mem_settling.mpr ⟨⟨(h.pending b).mpr ⟨h1, by omega⟩, hdt⟩, h2⟩
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
        refine ⟨σ.out.length + j, b.kline (σ.out.length + j), ?_, rfl⟩
        rw [List.getElem?_append_right (by omega), List.getElem?_mapIdx,
          show σ.out.length + j - σ.out.length = j by omega, hj]
        rfl

theorem inv_foldl {p d : Nat} (hp : 0 < p) (r : List Record) (pre : List Record) (σ : Settling)
    (h : σ.Inv p d pre) (hl : NoLateWord p d (pre ++ r)) :
    (r.foldl (Settling.step p d) σ).Inv p d (pre ++ r) := by
  induction r generalizing pre σ with
  | nil => simpa using h
  | cons x r ih =>
    simp only [List.foldl_cons]
    have hx : (σ.step p d x).Inv p d (pre ++ [x]) := by
      cases x with
      | said st =>
        refine inv_step_said hp h st fun t ht => ?_
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
        have hil := (List.getElem?_eq_some_iff.mp hi).1
        apply hl i pre.length t st hil
        · rw [List.getElem?_append_left hil]; exact hi
        · rw [List.getElem?_append_right (Nat.le_refl _)]; simp
      | mark t => exact inv_step_mark h t
    have := ih (pre ++ [x]) _ hx (by simpa using hl)
    simpa using this

/-- On a finite raw topic with no late word, the period above 0, the settled series holds exactly the vendor's
last words that keep market's rules on the windows a due watermark has been read for: the clean data
of the windows settled so far. -/
theorem settle_settled {p d : Nat} (hp : 0 < p) {l : List Record} (hl : NoLateWord p d l) (b : Bar) :
    (∃ (i : Nat) (k : KLine), (settle p d l)[i]? = some k ∧ barOf k = b) ↔
      LastWord (Log.ofList (feedOf l)) b ∧ (b.kline 0).Keeps ∧
        ∃ t, Record.mark t ∈ l ∧ due p d b ≤ t := by
  have hinv := inv_foldl hp l [] Settling.init (inv_init p d) (by simpa using hl)
  simp only [List.nil_append] at hinv
  rw [show settle p d l = (l.foldl (Settling.step p d) Settling.init).out from rfl, hinv.out,
    mem_lastWords]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rcases hinv.markOf with h0 | hm
    · rw [h0] at h3; unfold due at h3; omega
    · exact ⟨_, hm, h3⟩
  · rintro ⟨h1, h2, t, ht, h3⟩
    exact ⟨h1, h2, Nat.le_trans h3 (hinv.markGe t ht)⟩

/-- On a finite raw topic on time, the period above 0, the settled series is the clean data of the
vendor's feed. -/
theorem settle_clean {p d : Nat} (hp : 0 < p) {l : List Record} (h : OnTime p d l) :
    CleanOf (Log.ofList (feedOf l)) (Log.ofList (settle p d l)) where
  valid := settle_valid p d l
  last n k hk := ((settle_settled hp h.noLateWord (barOf k)).mp ⟨n, k, hk, rfl⟩).1
  complete b hb hk := by
    obtain ⟨st, hst, hbg, rfl⟩ := mem_lastWords_bar ((mem_lastWords _ _).mpr hb)
    obtain ⟨t, ht, hdue⟩ := h.settles st (mem_feedOf.mp hst) hbg
    exact (settle_settled hp h.noLateWord st.bar).mpr ⟨hb, hk, t, ht, hdue⟩

/-- The settling process, on a finite raw topic, gives the settling rule's series. -/
theorem settleP_ofList (p d : Nat) (l : List Record) :
    settleP p d (Log.ofList l) = Log.ofList (settle p d l) :=
  Log.ofPrefix_ofList _ _ l

/-- On a finite raw topic on time, the period above 0, the settling process gives the clean data of the
vendor's feed. -/
theorem settleP_clean {p d : Nat} (hp : 0 < p) {l : List Record} (h : OnTime p d l) :
    CleanOf (Log.ofList (feedOf l)) (settleP p d (Log.ofList l)) := by
  rw [settleP_ofList]
  exact settle_clean hp h

/-- On a finite raw topic on time, the period above 0, the settled series is what `construct` makes of
the vendor's feed: route 2 then gives what route 1 makes. -/
theorem settle_eq_construct {p d : Nat} (hp : 0 < p) {l : List Record} (h : OnTime p d l) :
    Log.ofList (settle p d l) = Log.ofList (construct (feedOf l)) :=
  (settle_clean hp h).unique (cleanOf_construct (feedOf l))

/-- A bar of a window already in the settled series, said again changed, makes the settled series no
longer the clean data. -/
theorem settle_late {p d : Nat} {l : List Record} {b b' : Bar} (t : Nat)
    (hin : ∃ (i : Nat) (k : KLine), (settle p d l)[i]? = some k ∧ barOf k = b) (hd : b'.date = b.date)
    (hne : b' ≠ b) (hb' : (⟨b', t⟩ : Statement).begun = true) :
    ¬ CleanOf (Log.ofList (feedOf (l ++ [.said ⟨b', t⟩])))
      (Log.ofList (settle p d (l ++ [.said ⟨b', t⟩]))) := by
  intro hc
  obtain ⟨i, k, hk, rfl⟩ := hin
  have hle : Log.ofList (settle p d l) ≤ Log.ofList (settle p d (l ++ [.said ⟨b', t⟩])) :=
    settle_extends p d l _ (Log.ofList_le_append _ _)
  have hlw := (mem_lastWords _ _).mpr (hc.last i k (hle i k hk))
  rw [feedOf_said, mem_lastWords_snoc] at hlw
  rcases hlw with ⟨_, h⟩ | ⟨_, h⟩
  · exact hne h
  · exact h hb' hd

/-- A watermark, as late as every window of a list of statements is due. -/
def bound (p d : Nat) : List Statement → Nat
  | [] => 0
  | st :: L => max (due p d st.bar) (bound p d L)

theorem le_bound {p d : Nat} {L : List Statement} {st : Statement} (h : st ∈ L) :
    due p d st.bar ≤ bound p d L := by
  induction L with
  | nil => cases h
  | cons x L ih =>
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ h => exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- A rule that gives the clean data of every finite raw topic on time gives a window's bar, on a finite
raw topic with no late word, only once a watermark due for its window has been read: before that, the vendor may
still say the window again, changed, and stay on time. -/
theorem correct_waits {p d : Nat} (P : Process (Log Record) (Log KLine))
    (hP : ∀ l, OnTime p d l → CleanOf (Log.ofList (feedOf l)) (P (Log.ofList l)))
    {l : List Record} (hl : NoLateWord p d l) {n : Nat} {k : KLine}
    (hk : (P (Log.ofList l)).get n = some k) :
    ∃ t, Record.mark t ∈ l ∧ due p d (barOf k) ≤ t := by
  apply Classical.byContradiction
  intro hno
  have hlt : ∀ t, Record.mark t ∈ l → t < due p d (barOf k) := fun t ht =>
    Nat.lt_of_not_le fun hle => hno ⟨t, ht, hle⟩
  obtain ⟨b', hd, hne⟩ := exists_other (barOf k)
  have hb' : (⟨b', b'.date⟩ : Statement).begun = true := by simp [Statement.begun]
  let M := bound p d (feedOf l ++ [⟨b', b'.date⟩])
  let l' := l ++ [Record.said ⟨b', b'.date⟩, Record.mark M]
  have hon : OnTime p d l' := by
    refine ⟨fun i j t st hij hi hj => ?_, fun st hst _ => ?_⟩
    · by_cases hjl : j < l.length
      · rw [List.getElem?_append_left hjl] at hj
        rw [List.getElem?_append_left (by omega)] at hi
        exact hl i j t st hij hi hj
      · rw [List.getElem?_append_right (by omega)] at hj
        have hj' : j - l.length = 0 := by
          match h : j - l.length with
          | 0 => rfl
          | 1 => rw [h] at hj; simp at hj
          | _ + 2 => rw [h] at hj; simp at hj
        rw [hj'] at hj
        simp at hj
        subst hj
        have hil : i < l.length := by omega
        rw [List.getElem?_append_left hil] at hi
        have := hlt t (List.mem_of_getElem? hi)
        unfold due at this ⊢
        simpa [hd] using this
    · refine ⟨M, by simp [l'], le_bound ?_⟩
      rcases List.mem_append.mp hst with hst | hst
      · exact List.mem_append_left _ (mem_feedOf.mpr hst)
      · simp at hst
        subst hst
        simp
  have hc := hP l' hon
  have hle : Log.ofList l ≤ Log.ofList l' := Log.ofList_le_append _ _
  have hlw := (mem_lastWords _ _).mpr (hc.last n k (P.mono hle n k hk))
  have hfeed : feedOf l' = feedOf l ++ [⟨b', b'.date⟩] := by
    simp [l', feedOf, List.filterMap_append]
  rw [hfeed, mem_lastWords_snoc] at hlw
  rcases hlw with ⟨_, h⟩ | ⟨_, h⟩
  · exact hne h
  · exact h hb' hd

/-- No correct rule is earlier than the settling rule. The settling process gives the clean data of
every finite raw topic on time (`settleP_clean`); and whatever a rule that does so gives on a finite raw
topic with no late word, the period above 0, the settled series of it gives too, the same k-line at the
same place. -/
theorem settle_earliest {p d : Nat} (hp : 0 < p) (P : Process (Log Record) (Log KLine))
    (hP : ∀ l, OnTime p d l → CleanOf (Log.ofList (feedOf l)) (P (Log.ofList l)))
    {l : List Record} (hl : NoLateWord p d l) {n : Nat} {k : KLine}
    (hk : (P (Log.ofList l)).get n = some k) : (Log.ofList (settle p d l)).get n = some k := by
  obtain ⟨t, ht, hdue⟩ := correct_waits P hP hl hk
  let l'' := l ++ [Record.mark (bound p d (feedOf l))]
  have hon : OnTime p d l'' := by
    refine ⟨fun i j t' st hij hi hj => ?_, fun st hst _ => ?_⟩
    · have hjl : j < l.length := by
        apply Classical.byContradiction
        intro hjl
        rw [List.getElem?_append_right (by omega)] at hj
        match h : j - l.length with
        | 0 => rw [h] at hj; simp at hj
        | _ + 1 => rw [h] at hj; simp at hj
      rw [List.getElem?_append_left hjl] at hj
      rw [List.getElem?_append_left (by omega)] at hi
      exact hl i j t' st hij hi hj
    · refine ⟨bound p d (feedOf l), by simp [l''], le_bound ?_⟩
      rcases List.mem_append.mp hst with hst | hst
      · exact mem_feedOf.mpr hst
      · simp at hst
  have hc := hP l'' hon
  have hk'' := P.mono (Log.ofList_le_append l [Record.mark (bound p d (feedOf l))]) n k hk
  have hlw := hc.last n k hk''
  rw [show feedOf l'' = feedOf l from feedOf_mark l _] at hlw
  obtain ⟨i, k', hi, hbk'⟩ := (settle_settled hp hl (barOf k)).mpr
    ⟨hlw, keeps_barOf (hc.valid.keeps n k hk''), t, ht, hdue⟩
  have hsame : P (Log.ofList l'') = Log.ofList (settle p d l'') := hc.unique (settle_clean hp hon)
  rw [hsame] at hk''
  have hi'' : (Log.ofList (settle p d l'')).get i = some k' :=
    settle_extends p d l l'' (Log.ofList_le_append _ _) i k' hi
  have hin : i = n := (settle_valid p d l'').date_inj hi'' hk''
    (by rw [← barOf_date, hbk', barOf_date])
  subst hin
  rw [hi''] at hk''
  cases hk''
  exact hi

/-- On the raw topic too, a process each of whose k-lines is always the vendor's last word on its
window gives nothing. -/
theorem final_gives_nothing_raw (P : Process (Log Record) (Log KLine))
    (hP : ∀ l n k, (P (Log.ofList l)).get n = some k → LastWord (Log.ofList (feedOf l)) (barOf k))
    (l : List Record) (n : Nat) : (P (Log.ofList l)).get n = none := by
  cases hk : (P (Log.ofList l)).get n with
  | none => rfl
  | some k =>
    exfalso
    obtain ⟨b', hd, hne⟩ := exists_other (barOf k)
    have hk' := P.mono (Log.ofList_le_append l [Record.said ⟨b', b'.date⟩]) n k hk
    have hlw := hP _ n k hk'
    rw [feedOf_said, lastWord_snoc_iff] at hlw
    have hb : (⟨b', b'.date⟩ : Statement).begun = true := by simp [Statement.begun]
    rcases hlw with ⟨_, h⟩ | ⟨_, h⟩
    · exact hne h
    · exact h hb hd

/-- No process gives the clean data of every finite raw topic: it would give only last words, so
nothing (`final_gives_nothing_raw`), and the raw topic of one statement has a last word to give. -/
theorem no_process_raw (P : Process (Log Record) (Log KLine)) :
    ¬ ∀ l, CleanOf (Log.ofList (feedOf l)) (P (Log.ofList l)) := by
  intro hP
  have hnone := final_gives_nothing_raw P fun l n k hk => (hP l).last n k hk
  have hf : feedOf [Record.said ⟨b₀, t₀⟩] = [⟨b₀, t₀⟩] := rfl
  obtain ⟨n, k, hk, _⟩ := (hP [Record.said ⟨b₀, t₀⟩]).complete b₀
    (by rw [hf]; exact lastWord_one b₀ t₀ (by decide)) ⟨by decide, by decide, by decide⟩
  rw [hnone] at hk
  cases hk

/-- Live and final cannot both be had, whatever the delay `d`: no process gives, on every finite raw
topic, only the vendor's last words (final), and, on every finite raw topic with no late word, each
last word that keeps market's rules once a watermark due for its window has been read (live within
`d`). The settling process is live, with a period above 0 (`settle_settled`); it is final that fails. -/
theorem no_live_final (p d : Nat) (P : Process (Log Record) (Log KLine))
    (hfinal : ∀ l n k, (P (Log.ofList l)).get n = some k → LastWord (Log.ofList (feedOf l)) (barOf k))
    (hlive : ∀ l, NoLateWord p d l → ∀ b, LastWord (Log.ofList (feedOf l)) b → (b.kline 0).Keeps →
      (∃ t, Record.mark t ∈ l ∧ due p d b ≤ t) →
        ∃ n k, (P (Log.ofList l)).get n = some k ∧ barOf k = b) : False := by
  let l := [Record.said ⟨b₀, t₀⟩, Record.mark (due p d b₀)]
  have hnl : NoLateWord p d l := fun i j t st hij hi hj => by
    match j, hj with
    | 0, _ => omega
    | 1, hj => simp [l] at hj
    | _ + 2, hj => simp [l] at hj
  have hf : feedOf l = [⟨b₀, t₀⟩] := rfl
  have hlw : LastWord (Log.ofList (feedOf l)) b₀ := by
    rw [hf]
    exact lastWord_one b₀ t₀ (by decide)
  obtain ⟨n, k, hk, _⟩ :=
    hlive l hnl b₀ hlw ⟨by decide, by decide, by decide⟩ ⟨_, by simp [l], Nat.le_refl _⟩
  rw [final_gives_nothing_raw P hfinal l n] at hk
  cases hk

end CleanStream
