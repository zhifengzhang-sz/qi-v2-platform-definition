# Acquisition, in words

This explains `lean/Acquisition.lean`, statement by statement; a statement of the same shape as one already explained is not explained again. The topic's shape is in `lean/Kafka.lean`, the base in `lean/Kahn/`. Each k-line contract defines an acquisition, and a working space has one; several working spaces may work side by side, one for each acquisition (`lean/Workspace.lean`).

## Preamble

```lean
import Kahn
import Kafka

noncomputable section

open Kahn
```

### `import Kahn`, `import Kafka`
The file builds on the base (`lean/Kahn/`: logs, processes, networks) and on Kafka's topic shape (`lean/Kafka.lean`).

### `noncomputable section`
`noncomputable section` tells Lean not to turn the definitions after it into runnable programs. They are still checked and can be used in proofs; they just can't be run, for example with `#eval`. The section lasts until the matching `end` at the bottom of the file.

1. Why it's needed:
   - Lean normally compiles every definition into code. It can't do that for a definition that uses classical choice, which says "some value exists, take it" without giving a way to compute it.
   - The base uses classical choice in one place: the limit of a growing log (`Log.lim` in `lean/Kahn/Log.lean`). That definition says position $n$ of the limit holds the message some stage holds there, if any stage does.
   - For a log that never ends, "does some stage ever fill position $n$?" can't be answered in finite time, because every stage would have to be looked at. So the limit, and with it the domain of logs (`Domain (Log α)`), is noncomputable; the order itself is a statement, not a computation.
   - Every process on logs uses that domain, so every definition that mentions one inherits the mark. The file marks them all at once instead of one by one.
2. What it costs: nothing for our purpose. These files define and prove things. They aren't the components' code, which is written in each project.
3. The alternative: Paulin-Mohring's Coq version builds the limit constructively, with no choice, so it can be computed. We could do the same, but the definitions would get more complex, and we gain nothing unless we want to run the Lean.

### `open Kahn`
The base's names can be written without their prefix: `Log` for `Kahn.Log`, `Process` for `Kahn.Process`.

## The kinds of data, and the clean series

```lean
/-- The four kinds of data acquisition publishes. -/
inductive Acquisition.Kind where
  | raw
  | corrected
  | clean
  | corrections

/-- A message of a clean series: a k-line, or a reset, after which the clean series starts again. -/
inductive Acquisition.Clean (K : Type) where
  | reset
  | kline (b : K)

namespace Acquisition.Clean

variable {K : Type}

/-- The clean series as it stands, of a finite clean log: the k-lines since the last reset. -/
def sinceReset (l : List (Clean K)) : List K :=
  l.foldl (fun acc m => match m with
    | .reset => []
    | .kline b => acc ++ [b]) []

/-- No process gives the clean series as it stands. A reset after a k-line `b` would take `b` back:
the k-lines since the last reset are `b` for the log `b`, and none for the log `b`, reset. -/
theorem sinceReset_not_process (b : K) (g : Process (Log (Clean K)) (Log K))
    (h : ∀ l, g (Log.ofList l) = Log.ofList (sinceReset l)) : False := by
  have hle : Log.ofList [Clean.kline b] ≤ Log.ofList ([Clean.kline b] ++ [Clean.reset]) :=
    Log.ofList_le_append _ _
  have h₁ : (g (Log.ofList [Clean.kline b])).get 0 = some b := by
    rw [h]
    rfl
  have h₂ := g.mono hle 0 b h₁
  rw [h] at h₂
  cases h₂

end Acquisition.Clean
```

### `inductive Acquisition.Kind`
An `inductive` lists every form a value can take, and nothing else is one. $\mathrm{Kind}$ has four: the raw series, the corrected raw series, the clean series and the vendor's corrections. Each of acquisition's topics carries one kind.

### `inductive Acquisition.Clean (K : Type)`
A message of a clean series of k-lines $K$ is one of two: $\mathrm{kline}\,b$, a k-line $b$; or $\mathrm{reset}$, after which the clean series starts again. A reset is how the clean series catches up with corrections without taking anything back: nothing before the reset is changed, and what follows it is the clean series made again.

### `def sinceReset`
The clean series as it stands, for a finite clean log $l$: the k-lines after the last reset in $l$ (all of them, if $l$ has no reset). `foldl` goes through $l$ from its start, keeping a list: a reset empties it, a k-line is added at its end. For example

$$\mathrm{sinceReset}\,[\mathrm{kline}\,a,\ \mathrm{kline}\,b,\ \mathrm{reset},\ \mathrm{kline}\,c] = [c]$$

### `theorem sinceReset_not_process`
No process gives the clean series as it stands: there is no process $g$ with

$$g\,(\mathrm{ofList}\,l) = \mathrm{ofList}\,(\mathrm{sinceReset}\,l) \quad \text{for every finite log } l$$

The log $[\mathrm{kline}\,b]$ is a prefix of $[\mathrm{kline}\,b,\ \mathrm{reset}]$, so $g$ of the first is a prefix of $g$ of the second (more input never takes back output). But the first gives $[b]$, and the second gives $[\,]$: the reset took $b$ back. So the clean series as it stands is a view, read off the clean log; a component reads the clean log, resets included. The same holds for the corrected raw series: the k-line as it stands now, its latest version, replaces a version already given, and no process gives that either (`Kafka.compaction_not_process`).

## The data

```lean
/-- The kinds of data an acquisition works on, which its k-line contract defines. -/
structure Acquisition.Data where
  /-- the contract's k-line. Raw, corrected raw and clean k-lines are all this. -/
  Kline : Type
  /-- what the reader reads -/
  Source : Type
  /-- a message of the vendor's corrections stream: what it looks like is not known -/
  Correction : Type
  /-- what the reset's reader replays: left open -/
  History : Type
  /-- the topics that carry data of kind `κ` -/
  Topic : Kind → Type
  /-- each one a Kafka topic -/
  topic : (κ : Kind) → Topic κ → Kafka.Topic

namespace Acquisition

variable (D : Data)

/-- A k-line series. -/
abbrev Series := Log D.Kline

/-- A clean series: k-lines and resets. -/
abbrev CleanSeries := Log (Clean D.Kline)

/-- The topics of kind `κ`. -/
abbrev Topics (κ : Kind) := ∀ t : D.Topic κ, (D.topic κ t).Logs

/-- All the topics, of every kind. -/
abbrev AllTopics := ∀ κ : Kind, Topics D κ

/-- What acquisition reads: its source, the vendor's corrections stream, and the history the reset
replays. -/
abbrev In := Log D.Source × Log D.Correction × Log D.History

end Acquisition
```

### `structure Acquisition.Data`
A structure is a record of named fields. Every field of `Data` is a placeholder: it says what kind of thing goes there, not what it is. A k-line contract, with its k-line, its source, its vendor's corrections and its topics, fills them in.

- $\mathrm{Kline} : \mathrm{Type}$: the contract's k-line is some type. $\mathrm{Source}$, $\mathrm{Correction}$ and $\mathrm{History}$ have the same shape: the type of the source's records, of the vendor's corrections, and of what the reset's reader replays. What the history is (a file, a database, or acquisition's own topics read back) is left open.
- $\mathrm{Topic} : \mathrm{Kind} \to \mathrm{Type}$: for each kind $\kappa$, $\mathrm{Topic}\,\kappa$ is the type of the topics that carry kind $\kappa$.
- $\mathrm{topic} : (\kappa : \mathrm{Kind}) \to \mathrm{Topic}\,\kappa \to \mathrm{Kafka.Topic}$: each of them is a Kafka topic. The second argument's type depends on the first: $t$ must be one of the topics of kind $\kappa$.

### `namespace Acquisition` … `end Acquisition`
The names defined in between get the prefix `Acquisition.`: `Acquisition.Series`, `Acquisition.Topics` and the others.

### `variable (D : Data)`
Every definition after it takes a $D$ as its first argument: one filling of the placeholders. $D.\mathrm{Kline}$ is $D$'s field $\mathrm{Kline}$.

### `abbrev Series := Log D.Kline`
An `abbrev` is a shorthand:

$$\mathrm{Series}\,D := \mathrm{Log}\,D.\mathrm{Kline}$$

a log of the contract's k-lines. The others are shorthands of the same kind:

- $\mathrm{CleanSeries}\,D := \mathrm{Log}\,(\mathrm{Clean}\,D.\mathrm{Kline})$: a clean series, k-lines and resets.
- $\mathrm{Topics}\,D\,\kappa := \forall\, t : D.\mathrm{Topic}\,\kappa,\ (D.\mathrm{topic}\,\kappa\,t).\mathrm{Logs}$: for every topic $t$ of kind $\kappa$, what that Kafka topic holds, one log of records for each of its partitions (`Topic.Logs` in `lean/Kafka.lean`).
- $\mathrm{AllTopics}\,D := \forall\, \kappa : \mathrm{Kind},\ \mathrm{Topics}\,D\,\kappa$: all the topics, of every kind.
- $\mathrm{In}\,D := \mathrm{Log}\,D.\mathrm{Source} \times \mathrm{Log}\,D.\mathrm{Correction} \times \mathrm{Log}\,D.\mathrm{History}$, where $A \times B$ puts two things side by side: here the source's log, the corrections' log and the history's log, read together. $A \times B \times C$ is $A \times (B \times C)$.

## Acquisition

```lean
open Acquisition

/-- The acquisition of a k-line contract. -/
structure Acquisition (D : Acquisition.Data) where
  /-- the vendor's reader: reads the source (a feed, a file or a database), gives the raw series -/
  reader : Process (Log D.Source) (Series D)
  /-- the reset's reader: replays the history -/
  replayer : Process (Log D.History) (Series D)
  /-- corrections + raw ⇒ corrected raw, a log of revisions: unspecified -/
  correct : Process (Series D × Log D.Correction) (Series D)
  /-- the cleaner: the corrected raw series and the replay ⇒ clean, with its resets -/
  cleaner : Process (Series D × Series D) (CleanSeries D)
  /-- the publisher, in four parts, each publishing one kind to the topics of that kind only: the raw
  series -/
  publishRaw : Process (Series D) (Topics D .raw)
  /-- the corrected raw series -/
  publishCorrected : Process (Series D) (Topics D .corrected)
  /-- the clean series -/
  publishClean : Process (CleanSeries D) (Topics D .clean)
  /-- the vendor's corrections -/
  publishCorrections : Process (Log D.Correction) (Topics D .corrections)
```

### `open Acquisition`
`Series`, `Topics` and the other shorthands can be written without the prefix.

### `structure Acquisition (D : Acquisition.Data)`
The acquisition of a k-line contract, for a given $D$: its two readers, the vendor's and the reset's; the step that takes in the corrections; the cleaner; and the publisher in four parts. Each field is a process; how each is made is the implementation's.

### `reader : Process (Log D.Source) (Series D)`
The vendor's reader reads the source (a feed, a file or a database) and gives the raw series.

- $\mathrm{Log}\,D.\mathrm{Source}$: the source as a log. Its records are in the order they arrive, appended and never changed. At any moment it holds the records received so far. No record is marked as the last: more can always come.
- $\mathrm{Series}\,D$: the raw series, a log of the contract's k-lines.
- $\mathrm{Process}\,A\,B$: a function $f : A \to B$ that meets Kahn's condition. Here it goes from a log to a log. It works on the whole log, not record by record: given all the source records so far, it says which k-lines exist so far. In Lean it is three things: the function (`fn`), and proofs of the two conditions (`mono`, `cont`). Write $s \le s'$ when log $s$ is a prefix of log $s'$:
  1. More input never takes back output: $$s \le s' \implies f\,s \le f\,s'$$ When more source records arrive, the series only grows at its end. A k-line once given is never removed or changed.
  2. Nothing waits for the end: for every chain of logs $s_0 \le s_1 \le s_2 \le \cdots$, with $\bigsqcup_n s_n$ the log it grows to, $$f\Big(\bigsqcup_n s_n\Big) = \bigsqcup_n f\,s_n$$ Every log is the limit of its finite prefixes, so $f\,s = \bigsqcup_n f\,(\mathrm{take}\,n\,s)$, where $\mathrm{take}\,n\,s$ is the first $n$ records of $s$ (`Process.eq_sup_take` in `lean/Kahn/Log.lean`). Each k-line is given after finitely many source records. More can always come, so a reader that waited for the end would give nothing.

What it leaves free:

- How records become k-lines: several records can make one k-line, and a record can make none.
- When a k-line is given, as long as it comes after finitely many records.

One consequence: a reader that builds 1-minute bars from trades can give the bar for 10:00 only once something in its input shows that 10:00 is over, such as a trade at 10:01. A process can't react to nothing arriving. If the reader should also close a bar on the clock, the clock has to be one of its input logs.

### `replayer`, `correct`, `cleaner`
The same shape as $\mathrm{reader}$: each is a process, and the two conditions hold for each. They differ in what they read and what they write:

- $\mathrm{replayer}$, the reset's reader, reads $\mathrm{Log}\,D.\mathrm{History}$, the history, and gives a series: the replay.

- $\mathrm{correct}$ reads $\mathrm{Series}\,D \times \mathrm{Log}\,D.\mathrm{Correction}$, the raw series and the vendor's corrections side by side, and writes the corrected raw series, a log of revisions: a k-line's first version, then each corrected version as a message of its own. How it does so is unspecified.
- $\mathrm{cleaner}$ reads $\mathrm{Series}\,D \times \mathrm{Series}\,D$, the corrected raw series and the replay, and writes the clean series, $\mathrm{CleanSeries}\,D$: k-lines, and a reset whenever the clean series starts again. A reset is a replay: the clean series is made again from the replay, and when the replay is over the corrected raw series takes over. When a reset comes, when the replay is over and the switch, are acquisition's own state: the implementation's.

### `publishRaw`, `publishCorrected`, `publishClean`, `publishCorrections`
The publisher, in four parts of the same shape, one for each kind. Each reads one series and writes the topics of its kind alone: $\mathrm{publishClean}$ reads the clean series and writes $\mathrm{Topics}\,D\,\mathrm{clean}$, and so on. A part cannot write a topic of another kind: its type does not allow it.

## How the parts are wired

```lean
namespace Acquisition

variable {D : Data}

/-- Acquisition as one process: from the source, the corrections and the history to every topic. -/
def run (a : Acquisition D) : Process (In D) (AllTopics D) :=
  let corrections : Process (In D) (Log D.Correction) := Process.fst ⊚ Process.snd
  let history : Process (In D) (Log D.History) := Process.snd ⊚ Process.snd
  let raw : Process (In D) (Series D) := a.reader ⊚ Process.fst
  let corrected : Process (In D) (Series D) := a.correct ⊚ Process.pair raw corrections
  let replay : Process (In D) (Series D) := a.replayer ⊚ history
  let clean : Process (In D) (CleanSeries D) := a.cleaner ⊚ Process.pair corrected replay
  Process.pi fun κ => match κ with
    | .raw => a.publishRaw ⊚ raw
    | .corrected => a.publishCorrected ⊚ corrected
    | .clean => a.publishClean ⊚ clean
    | .corrections => a.publishCorrections ⊚ corrections

/-- The raw topics hold what the publisher makes of the raw series alone. -/
theorem raw_topics (a : Acquisition D) (s : Log D.Source) (c : Log D.Correction)
    (h : Log D.History) :
    a.run (s, c, h) .raw = a.publishRaw (a.reader s) :=
  rfl

/-- The corrected raw topics hold what the publisher makes of the corrected raw series alone. -/
theorem corrected_topics (a : Acquisition D) (s : Log D.Source) (c : Log D.Correction)
    (h : Log D.History) :
    a.run (s, c, h) .corrected = a.publishCorrected (a.correct (a.reader s, c)) :=
  rfl

/-- The clean topics hold what the publisher makes of the clean series alone: the cleaner's, on the
corrected raw series and the replay. -/
theorem clean_topics (a : Acquisition D) (s : Log D.Source) (c : Log D.Correction)
    (h : Log D.History) :
    a.run (s, c, h) .clean = a.publishClean (a.cleaner (a.correct (a.reader s, c), a.replayer h)) :=
  rfl

/-- The corrections topics hold what the publisher makes of the vendor's corrections alone. -/
theorem corrections_topics (a : Acquisition D) (s : Log D.Source) (c : Log D.Correction)
    (h : Log D.History) :
    a.run (s, c, h) .corrections = a.publishCorrections c :=
  rfl

end Acquisition

end
```

### `variable {D : Data}`
As `variable (D : Data)`, but in braces: Lean works out $D$ from the acquisition it is given, so it isn't written.

### `def run (a : Acquisition D) : Process (In D) (AllTopics D)`
Acquisition $a$ as one process, from what it reads to all its topics. It is a process because wiring processes together gives a process (Kahn). The wiring uses these operations:

$$(g \circledcirc f)\,x = g\,(f\,x) \qquad \mathrm{fst}\,(x, y) = x \qquad \mathrm{snd}\,(x, y) = y \qquad (\mathrm{pair}\,f\,g)\,x = (f\,x,\ g\,x) \qquad (\mathrm{pi}\,F)\,x\,\kappa = F\,\kappa\,x$$

$g \circledcirc f$ sends the output of $f$ into $g$; $\mathrm{fst}$ and $\mathrm{snd}$ take one of two things side by side; $\mathrm{pair}\,f\,g$ lets $f$ and $g$ read the same input and puts their outputs side by side; $\mathrm{pi}\,F$ gives, for each kind $\kappa$, what $F\,\kappa$ gives, and `match κ with` says which part that is for each kind. Each `let` names one part of the wiring for the lines after it. For the source $s$, the corrections $c$ and the history $h$, with $r = \mathrm{reader}\,s$ the raw series, $r' = \mathrm{correct}\,(r, c)$ the corrected raw series and $p = \mathrm{replayer}\,h$ the replay:

$$\mathrm{run}\,a\,(s, c, h)\,\kappa = \begin{cases} \mathrm{publishRaw}\,r & \kappa = \mathrm{raw} \\ \mathrm{publishCorrected}\,r' & \kappa = \mathrm{corrected} \\ \mathrm{publishClean}\,(\mathrm{cleaner}\,(r', p)) & \kappa = \mathrm{clean} \\ \mathrm{publishCorrections}\,c & \kappa = \mathrm{corrections} \end{cases}$$

### `theorem raw_topics`, `corrected_topics`, `clean_topics`, `corrections_topics`
The four lines of that equation, one theorem each: the topics of each kind hold what the publisher's part for that kind makes of its own series alone. So the clean topics hold the clean series and nothing else. Each proof is `rfl`: the two sides are the same once the definitions are unfolded.

### `end`
Closes the `noncomputable section`.
