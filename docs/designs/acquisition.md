# Acquisition: the published stream's axioms against the vendor's stream

Acquisition reads the vendor's bars of one series and publishes them as a clean series. Everything downstream builds on the clean series and checks nothing again. This document sets the axioms the published stream must hold against the stream the vendor actually provides, states the gap, proves what cannot be had, and gives the two routes that remain. The Lean is `lean/CleanStream.lean`. The evidence, with its sources, is `docs/designs/research/stream.md`; the vendor is Massive, its bars of US stocks.

## The axioms of the published stream

The axioms are read from Kafka's topic partition, as the model of a stream (`docs/designs/research/stream.md`, Part 1). Kafka itself is not in the definition: in the Lean a stream is a Kahn log, which holds A1 to A4 by what a log is (`Kahn.Log`), and an implementation that carries a log, on Kafka say, shows that it keeps A5 to A7, so that each reader reads the log that was written.

- **A1.** One ordered sequence, which only grows at its end.
- **A2.** A record, once written, is never changed.
- **A3.** Each record has a fixed position, and positions increase along the sequence.
- **A4.** Every reader sees the same sequence, from any position it starts at, as often as it likes.
- **A5.** One writer's records are in the order it wrote them, also when a write is retried.
- **A6.** No record is in the sequence twice.
- **A7.** A record written is not lost.

The clean series adds one axiom of its own:

- **S.** The bars are in date order, one bar for each date, each bar's `index` is its position, and each bar keeps market's rules. The market contract states what a valid bar is, and its records are the form the components exchange bars in. In the Lean: `CleanStream.Valid`, with `CleanStream.Valid.date_inj` (one bar for each date).

## The vendor's stream

How the vendor's stream behaves (`docs/designs/research/stream.md`, Part 2, which gives the evidence for each). In the Lean the vendor's feed is the log of its statements as read (`CleanStream.Feed`). Features 1, 2, 4 and 7 are stated of a feed (`Resent`, `OutOfOrder`, `Missing`, `RevisedAfter`), and two kinds of error besides: a bar that breaks market's rules (`Broken`), and a statement read before its window began (`NotYetBegun`), the reading error feature 9 warns of, which is no word of the vendor's (`Statement.begun`). Each is shown on a sample feed of invented bars (`CleanStream.sample`, `sample_resent`, …). Feature 6, a bar wrong in its values, keeps market's rules: it shows only when the vendor says the window again (`RevisedAfter`).

1. One bar is sent several times, each time a new version, for up to 15 minutes after its window.
2. Bars do not arrive in date order: a re-sent bar is dated up to 15 minutes before bars already received.
3. No message says a bar is final, and its first version may be incomplete.
4. A window with no eligible trade has no bar. A missing bar is normal: one busy stock had bars in 885 of its 960 minutes.
5. There is no sequence number and no replay. A client that was disconnected gets nothing of what it missed, and the connection is reset every night.
6. A bar on the stream can be wrong: a trade reported more than 15 minutes late is left out, and a trade cancelled later stays in.
7. Corrections are never sent after 15 minutes. The history takes in late trades at the end of the day and drops cancelled trades a few days later. Nothing announces either: a client learns of a correction only by asking again and comparing.
8. A split rewrites the whole adjusted history, at any later time. The unadjusted history is the one the vendor advises keeping as a permanent record. A ticker can be renamed or reused.
9. A timestamp is the start of the bar's window, in UTC: milliseconds on the stream and in the history, nanoseconds in the daily files. A daily bar is stamped at midnight Eastern.
10. Only some trades count toward a bar, and price and volume count different trades.
11. The stream is real-time or 15 minutes delayed, by the plan.
12. The same bar differs in form, and can differ in value, between the stream, the history and the daily files.

## The gap

The vendor's stream holds none of the axioms. The one thing it gives is that the messages of one connection arrive in the order they were sent. Each row below is what acquisition has to do so that the published stream holds the axiom.

| Axiom | The vendor's stream | What acquisition has to do |
|---|---|---|
| A1 one sequence | each connection starts a new one; re-sent bars go back in time (1, 2, 5) | join every connection and the history into one sequence that outlives them, its order fixed by a rule |
| A2 never changed | the vendor tells clients to overwrite; the history changes later (1, 6, 7, 8) | publish a change of a bar as a further record, never as an edit; read unadjusted prices |
| A3 fixed positions | a bar has no number, only its start time, with holes where no trade counted (1, 4, 5) | give each bar its position by its own count; the date stays a field, never the position |
| A4 same for every reader | no replay; two clients see different things (5, 7, 8, 11) | read the vendor once, into one log; everything downstream reads that log, never the vendor |
| A5 the writer's order | no order of sending is stated (2) | rest the published order on nothing the vendor sends in |
| A6 no duplicate | the same bar is re-sent on purpose; the history repeats what the stream gave (1, 5, 12) | decide which version of a bar is the bar of the series, and where the other versions go |
| A7 nothing lost | nightly resets, nothing re-sent; a lost bar looks like a quiet minute (4, 5) | fill every gap of the connection from the history before going on |
| S date order, valid bars | out of date order, unnumbered, some bars wrong (2, 3, 6) | keep date order and number the bars itself; refuse and record a bar that breaks market's rules |

## What cannot be had

Three things are wanted of the clean series:

- **Live:** each bar is published within a fixed delay after its window closes.
- **Final:** each published bar is the vendor's last version of that bar.
- **Fixed:** a published bar is never changed, and the series keeps axiom S: one bar for each date, in date order.

All three at once cannot be had, and the Lean proves it on the raw topic of statements and watermarks (Route 2, below): no process gives, on every finite raw topic, only the vendor's last words, and, on every finite raw topic with no late word, each last word that keeps market's rules once a watermark due for its window has been read, whatever the delay (`CleanStream.no_live_final`); and a process that gives only last words gives nothing, on any finite feed or finite raw topic (`CleanStream.final_gives_nothing`, `final_gives_nothing_raw`). In the Lean, Fixed is being a process, Final is giving only last words, and Live is giving each such bar once a watermark due for its window has been read. Route 2's settling process is live and fixed (`CleanStream.settle_settled`): it is final that fails. The clean data of a feed is the clean stream holding, of each window whose last word keeps market's rules, that last word (`CleanStream.CleanOf`); a feed has one at most (`CleanOf.unique`), every finite feed has it (`cleanOf_construct`), and no process gives it for every feed (`CleanStream.no_process`). The reason is one: whatever a process gives as a window's bar, the vendor may say that window again, changed, and a process never takes back what it has given. A bar's life on the vendor's side has no moment at which it is final:

```mermaid
flowchart LR
  W["the window closes"] --> S1["first version on the stream<br/>per-second bar: 2 s after<br/>per-minute bar: not stated"]
  S1 --> S2["re-sent versions on the stream<br/>up to 15 min after"]
  S2 --> H1["the history takes in trades reported late<br/>at the end of the day"]
  H1 --> H2["the history drops cancelled trades<br/>a few days after"]
  H2 --> H3["corrections of an earlier day<br/>no limit stated"]
  H3 -.-> N["no message ever says the bar is final"]
```

The argument, in three steps:

1. **Final is never known.** The vendor can revise a bar within 15 minutes, at the end of the day and days later, states no last revision, and marks no bar final (features 1, 3, 7). So for any delay, a bar published at that delay may still be revised after it. Most bars are never revised after 15 minutes: that needs a trade reported more than 15 minutes late, or a trade cancelled or corrected, and the vendor counts a cancel in roughly one of 100,000 to 400,000 trades. What cannot be had is a guarantee that a bar is final, not a bar that is right.
2. **Live and Final exclude each other under Fixed.** A bar published within a fixed delay may be revised after it (step 1). Under Fixed the published bar cannot take the revision: changing it breaks A2, and a second bar of the same date breaks S. So the clean series holds the bar as known when it was published, not its last version.
3. **Without Fixed, the series is no stream.** A series whose bars are overwritten as revisions come breaks A2. A view that replaces a record already given is not a process (`Kafka.compaction_not_process`), so every reader of such a series has to check its bars again and take in corrections itself: the checking and re-checking all over the platform that the axioms are there to prevent.

So each way of building acquisition gives up one of the three:

```mermaid
flowchart TD
  L(("Live"))
  F(("Final"))
  X(("Fixed"))
  L ---|"A: publish soon and never change;<br/>later versions go on a stream of their own"| X
  F ---|"B: publish from the history once it has settled;<br/>days late, and no moment is known final"| X
  L ---|"C: overwrite as versions come;<br/>no stream, and every reader checks again"| F
```

- **A, Live and Fixed.** The clean series is each bar as known at a fixed delay after its window, never changed: in the Lean, route 2's settling process (`CleanStream.settle_settled`). The versions after that delay, and the history's later revisions, are published apart, on the corrections stream. The cost: a clean bar can differ from the vendor's last version. By the vendor's account, a trade is cancelled in roughly one of 100,000 to 400,000 trades, and every settled session checked had at least one. The delay is a parameter: at the close, the stream's re-sends all become corrections; 15 minutes after the close, the stream's last word is taken and only the history's revisions are corrections, at the cost of every clean bar being 15 minutes late.
- **B, Final and Fixed.** The clean series is read from the history once it has settled. It is not live, and even then no moment is known to be final (step 1), so it is final only as far as anyone can know. As a process it gives nothing (`CleanStream.final_gives_nothing`): it is made outside the stream, which is route 1.
- **C, Live and Final.** It breaks the axioms (step 3). It is listed to show why it is not taken.

Two more limits follow from the vendor's stream, whichever way is taken:

- **A lost bar and a quiet minute look the same on the stream** (features 4, 5). Only the history tells them apart, so completeness rests on reading the history for every gap of the connection, and on the history itself being whole, which is an assumption.
- **A bar first seen late cannot join the clean series in date order** (features 2, 4): a bar the history shows for a window the stream had nothing for, after later bars were published, would break S. Under A or B it is a correction too.

## The corollary: two routes

The theorem leaves two routes. On the first, the clean data is made outside the streaming system and the stream is fed from its store: the stream holds the clean data of a snapshot, and acquisition cleans nothing. On the second, acquisition works on the vendor's data in the stream: by the theorem, what the stream then holds is not the clean data but each bar as known at a fixed delay. The first is way B above, made again at each snapshot; the second is way A. Both give the components downstream a stream that never changes, so nothing downstream checks again.

## Route 1: the clean data made outside the stream

- **Recording.** The vendor's statements are appended, as read, to a raw store: each bar as the vendor gave it, on the stream or from the history, with the time it was read, prices unadjusted. Nothing in it is refused, merged or overwritten.
- **Construction, outside the streaming system.** From a snapshot of the raw store, a finite list of statements taken as complete, a function makes the snapshot's clean data: its last words on each window, those that keep market's rules, in date order, each at its place (`CleanStream.construct`). What it makes is the snapshot's clean data (`CleanStream.cleanOf_construct`). It is a function, and no process gives what it makes of every snapshot (`CleanStream.construct_not_process`): run again on a later snapshot, it may give a series that does not extend the earlier one, which a process cannot. A statement read before its window began is no word of the vendor's, and is left out. It is written to the clean store, with the time of its snapshot. All the cleaning work in `docs/designs/research/acquisition.md` belongs here.
- **Acquisition feeds the stream from the clean store** and cleans nothing (`CleanStream.feed`, in the Lean the process that passes its input on). The stream then holds the snapshot's clean data (`CleanStream.store_route`; on the sample feed, `CleanStream.sample_clean`; the bar read before its window began is not in it, `CleanStream.sample_clean_no_future`).
- **Versions,** the design's, not in the Lean. While the clean store is only extended, the stream follows it, as a process does. A construction that changes bars already fed makes a new version of the stream, which its readers read from its start: a stream cannot follow a rewrite of its store.
- **The bar still forming,** for the live chart, comes from the vendor's live statements, not from the clean store: it is for display, not clean data.
- **What it gives:** the stream holds the clean data, as of its snapshot. **What it costs:** the stream is as fresh as the last construction, and a construction that revises bars already fed costs a new version.
- **Its parameters:** how often the construction runs, on what snapshot; when a revision makes a new version, and how far back a construction reaches.

## Route 2: the vendor's data in the stream

On this route the stream cannot hold the clean data of every raw topic (`CleanStream.no_process_raw`). What it can hold is the clean data relative to a revision horizon: the data is right if the vendor says nothing of a window once a watermark due for it has been read, and it is published as early as that allows. Earlier is measured by the watermarks, the model's one clock.

- **The raw topic** is the log of acquisition's records (`CleanStream.Record`): the vendor's statements as read, each bar with the time it was read, prices unadjusted, nothing refused, merged or overwritten; and watermarks, each a time up to which acquisition has read the vendor with no gap. At the start and after each disconnect, acquisition reads the history for the gap, and writes no watermark until it has. That a watermark is true, everything up to it read, is acquisition's to make so: the Lean takes each watermark as written, a modelling choice.
- **The settled series** is computed from the raw topic by one rule (`CleanStream.settle`, as a process `CleanStream.settleP`). A window is due at its end plus `d` (`CleanStream.due`). At a watermark, each window due by it settles: its last version read so far enters the settled series if it keeps market's rules, in date order, each at its place. A statement of a window a due watermark has been read for is a correction: the settled series does not take it. A statement read before its window began is no word, and is left out. Before a window settles, its versions are its bar still forming, which the chart reads.
- **It is always a clean k-line stream,** whatever the raw topic holds, endless ones among them (`CleanStream.settleP_valid`): date order comes from settling, with no rule on dates.
- **At each moment it is the clean data of the windows settled so far** (`CleanStream.settle_settled`): on a finite raw topic with no late word, nothing said of a window once a watermark due for it has been read (`CleanStream.NoLateWord`), the settled series holds exactly the last words that keep market's rules on the windows a due watermark has been read for. This is the statement for the running stream. It needs a period above 0.
- **It is the clean data on a finite raw topic on time** (`CleanStream.settle_clean`, `CleanStream.settleP_clean`): with no late word, and every window spoken of settled (`CleanStream.OnTime`), the period above 0. It is then what route 1 makes of the same statements (`CleanStream.settle_eq_construct`).
- **No correct rule is earlier** (`CleanStream.settle_earliest`): the settling process gives the clean data of every finite raw topic on time, and whatever a rule that does so gives on a finite raw topic with no late word, the period above 0, the settled series gives too, the same k-line at the same place. Such a rule waits for a due watermark (`CleanStream.correct_waits`). A rule that took its time from the statements' reading times as well is outside this statement.
- **Past the horizon it differs** (`CleanStream.settle_late`): a window already in the settled series, said again changed, makes the settled series no longer the clean data. Those statements are corrections. That the two differ nowhere else but on windows not yet settled and on windows first spoken of after a due watermark is argued, not proved.
- **Time is in the data:** a process sees only its input, so a rule that waits needs the time in the log, and the watermark is that time.
- **What the Lean does not yet cover:** the clean data of an endless feed; the corrections and the refused bars as topics computed from the raw topic.
- **Its parameters:** the settling delay `d`, the horizon assumed of the vendor: 15 minutes for this vendor's real-time stream, the time in which it re-sends a bar; the watermark interval; the feed, real-time or delayed.

## How the two routes work together

- **Live,** the components run on the settled series of route 2: at each moment the clean data of the windows settled so far, while the vendor says nothing of a settled window (`CleanStream.settle_settled`), `d` behind the market, never changed and never checked again.
- **Past the horizon,** each later statement of a settled window is a correction, on the corrections stream. How many there are, and how large, says how well the horizon holds, and so how `d` is chosen.
- **Outside the stream,** the clean store is made as route 1 makes it, from a snapshot of the recorded statements (`CleanStream.construct`). It differs from the settled series on the windows the corrections name and on those not yet settled, and on no others: it is the settled series with those windows' last words put in their places, made outside the stream because it changes bars already published. This is argued here, not proved in the Lean: the Lean proves the two the same on a raw topic on time (`CleanStream.settle_eq_construct`), and different once a settled window is said again changed (`CleanStream.settle_late`).
- **Reconciliation:** when the clean store differs from the settled series in a way that matters, a price rather than a volume say, a new version of the stream is fed from the clean store (route 1), and the components run again on it. When that is done is a parameter.

## Parameters of both routes

- **The series' signature:** the security, the market, the exchange, the source and the period (`Acquisition.Signature`). It sets which series the working space is, and the names of its streams.
- **The feed:** the vendor's real-time stream or its 15-minute delayed one (feature 11).

## What it means for the design so far

- The raw topic held the vendor's raw series of k-lines, and the corrections came from an input of their own. On either route the vendor's data is recorded as statements, with the time each was read.
- The cleaner's rule on dates, to keep a bar only if it is dated after every kept bar, goes. On route 1 there is no cleaner in the stream; on route 2 date order comes from settling, and a later version of a bar is a correction, not an error.
- The streams are logs, not Kafka topics: the implementation that carries them on Kafka shows that each reader reads the log written. The rest of the Lean still has Kafka's topic in it.
- `docs/designs/spec.md` and the rest of the Lean follow once a route is taken.

## What is left

- When a difference between the clean store and the settled series makes a new version of the stream.
- On route 1: when the construction runs, and when a revision makes a new version.
- On route 2: the value of `d` for the delayed stream, whose handling of re-sent bars the vendor does not state; the corrections, and the refused bars, as topics computed from the raw topic, in the Lean.
- When the vendor's history is read again to find its later revisions (at the end of the day, days later), and how far back: the vendor announces none (feature 7).
- Whether a statement records which feed it came from, the stream or the history.
- Whether a per-minute bar is first sent before its minute ends. Only watching the stream settles it.
