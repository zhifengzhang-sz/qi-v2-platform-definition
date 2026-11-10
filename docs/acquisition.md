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

## The kinds of data

```lean
/-- The three kinds of data acquisition publishes. -/
inductive Acquisition.Kind where
  | raw
  | clean
  | corrections
```

### `inductive Acquisition.Kind`
An `inductive` lists every form a value can take, and nothing else is one. $\mathrm{Kind}$ has three: the raw series, the clean series and the vendor's corrections. Each of acquisition's topics carries one kind. No kind is a corrected raw series: acquisition publishes the vendor's corrections as they come and applies them to nothing.

## The data

```lean
/-- The kinds of data an acquisition works on, which its k-line contract defines. -/
structure Acquisition.Data where
  /-- the contract's k-line. Raw, corrected raw and clean k-lines are all this. -/
  Kline : Type
  /-- what the reader reads: the vendor's corrected raw series first, then its raw series -/
  Source : Type
  /-- a message of the vendor's corrections stream: what it looks like is not known -/
  Correction : Type
  /-- the topics that carry data of kind `κ` -/
  Topic : Kind → Type
  /-- each one a Kafka topic -/
  topic : (κ : Kind) → Topic κ → Kafka.Topic

namespace Acquisition

variable (D : Data)

/-- A k-line series. -/
abbrev Series := Log D.Kline

/-- The topics of kind `κ`. -/
abbrev Topics (κ : Kind) := ∀ t : D.Topic κ, (D.topic κ t).Logs

/-- All the topics, of every kind. -/
abbrev AllTopics := ∀ κ : Kind, Topics D κ

/-- What acquisition reads: its source, and the vendor's corrections stream. -/
abbrev In := Log D.Source × Log D.Correction

end Acquisition
```

### `structure Acquisition.Data`
A structure is a record of named fields. Every field of `Data` is a placeholder: it says what kind of thing goes there, not what it is. A k-line contract, with its k-line, its source, its vendor's corrections and its topics, fills them in.

- $\mathrm{Kline} : \mathrm{Type}$: the contract's k-line is some type. $\mathrm{Source}$ and $\mathrm{Correction}$ have the same shape: the type of the records the reader reads, and of the vendor's corrections.
- $\mathrm{Topic} : \mathrm{Kind} \to \mathrm{Type}$: for each kind $\kappa$, $\mathrm{Topic}\,\kappa$ is the type of the topics that carry kind $\kappa$.
- $\mathrm{topic} : (\kappa : \mathrm{Kind}) \to \mathrm{Topic}\,\kappa \to \mathrm{Kafka.Topic}$: each of them is a Kafka topic. The second argument's type depends on the first: $t$ must be one of the topics of kind $\kappa$.

### `namespace Acquisition` … `end Acquisition`
The names defined in between get the prefix `Acquisition.`: `Acquisition.Series`, `Acquisition.Topics` and the others.

### `variable (D : Data)`
Every definition after it takes a $D$ as its first argument: one filling of the placeholders. $D.\mathrm{Kline}$ is $D$'s field $\mathrm{Kline}$.

### `abbrev Series := Log D.Kline`
An `abbrev` is a shorthand:

$$\mathrm{Series}\,D := \mathrm{Log}\,D.\mathrm{Kline}$$

a log of the contract's k-lines. The raw series and the clean series are both one. The others are shorthands of the same kind:

- $\mathrm{Topics}\,D\,\kappa := \forall\, t : D.\mathrm{Topic}\,\kappa,\ (D.\mathrm{topic}\,\kappa\,t).\mathrm{Logs}$: for every topic $t$ of kind $\kappa$, what that Kafka topic holds, one log of records for each of its partitions (`Topic.Logs` in `lean/Kafka.lean`).
- $\mathrm{AllTopics}\,D := \forall\, \kappa : \mathrm{Kind},\ \mathrm{Topics}\,D\,\kappa$: all the topics, of every kind.
- $\mathrm{In}\,D := \mathrm{Log}\,D.\mathrm{Source} \times \mathrm{Log}\,D.\mathrm{Correction}$, where $A \times B$ puts two things side by side: here the source's log and the corrections' log, read together.

## Acquisition

```lean
open Acquisition

/-- The acquisition of a k-line contract. -/
structure Acquisition (D : Acquisition.Data) where
  /-- the reader: reads the source, gives the raw series -/
  reader : Process (Log D.Source) (Series D)
  /-- the cleaner: raw ⇒ clean -/
  cleaner : Process (Series D) (Series D)
  /-- the publisher, in three parts, each publishing one kind to the topics of that kind only: the raw
  series -/
  publishRaw : Process (Series D) (Topics D .raw)
  /-- the clean series -/
  publishClean : Process (Series D) (Topics D .clean)
  /-- the vendor's corrections -/
  publishCorrections : Process (Log D.Correction) (Topics D .corrections)
```

### `open Acquisition`
`Series`, `Topics` and the other shorthands can be written without the prefix.

### `structure Acquisition (D : Acquisition.Data)`
The acquisition of a k-line contract, for a given $D$: the reader, the cleaner, and the publisher in three parts. Each field is a process; how each is made is the implementation's.

### `reader : Process (Log D.Source) (Series D)`
The reader reads the source and gives the raw series.

- $\mathrm{Log}\,D.\mathrm{Source}$: the source as a log. Its records are in the order the reader reads them, appended and never changed. At any moment it holds the records read so far. No record is marked as the last: more can always come.
- $\mathrm{Series}\,D$: the raw series, a log of the contract's k-lines.
- $\mathrm{Process}\,A\,B$: a function $f : A \to B$ that meets Kahn's condition. Here it goes from a log to a log. It works on the whole log, not record by record: given all the source records so far, it says which k-lines exist so far. In Lean it is three things: the function (`fn`), and proofs of the two conditions (`mono`, `cont`). Write $s \le s'$ when log $s$ is a prefix of log $s'$:
  1. More input never takes back output: $$s \le s' \implies f\,s \le f\,s'$$ When more source records arrive, the series only grows at its end. A k-line once given is never removed or changed.
  2. Nothing waits for the end: for every chain of logs $s_0 \le s_1 \le s_2 \le \cdots$, with $\bigsqcup_n s_n$ the log it grows to, $$f\Big(\bigsqcup_n s_n\Big) = \bigsqcup_n f\,s_n$$ Every log is the limit of its finite prefixes, so $f\,s = \bigsqcup_n f\,(\mathrm{take}\,n\,s)$, where $\mathrm{take}\,n\,s$ is the first $n$ records of $s$ (`Process.eq_sup_take` in `lean/Kahn/Log.lean`). Each k-line is given after finitely many source records. More can always come, so a reader that waited for the end would give nothing.

What it leaves free:

- How records become k-lines: several records can make one k-line, and a record can make none.
- When a k-line is given, as long as it comes after finitely many records.

One consequence: a reader that builds 1-minute bars from trades can give the bar for 10:00 only once something in its input shows that 10:00 is over, such as a trade at 10:01. A process can't react to nothing arriving. If the reader should also close a bar on the clock, the clock's ticks have to be records of the source, in the order the reader reads them. A clock as a second log beside the source would not do: a process is a function of its logs, and two logs side by side do not say which of their records came first.

The raw series has two parts: first the vendor's corrected raw series, then the vendor's raw series, appended to it. The reader reads both parts; how (a replayer in it, say) is the implementation's, and so is the switch from the first part to the second. In the definition the source is one log, holding what the reader reads in the order it reads it, and the reader is one process of that log. That the source holds the corrected raw series first is a modelling choice, not a theorem. A reset, which reads the corrected raw series again, is outside the working space: within one, nothing starts again.

### `cleaner : Process (Series D) (Series D)`
The same shape as $\mathrm{reader}$: a process, and the two conditions hold for it. It reads the raw series and writes the clean series, both a $\mathrm{Series}\,D$. How it cleans is the implementation's.

### `publishRaw`, `publishClean`, `publishCorrections`
The publisher, in three parts of the same shape, one for each kind. Each reads one log and writes the topics of its kind alone: $\mathrm{publishClean}$ reads the clean series and writes $\mathrm{Topics}\,D\,\mathrm{clean}$, $\mathrm{publishCorrections}$ reads the vendor's corrections and writes $\mathrm{Topics}\,D\,\mathrm{corrections}$. A part cannot write a topic of another kind: its type does not allow it.

## How the parts are wired

```lean
namespace Acquisition

variable {D : Data}

/-- Acquisition as one process: from the source and the corrections to every topic. -/
def run (a : Acquisition D) : Process (In D) (AllTopics D) :=
  let corrections : Process (In D) (Log D.Correction) := Process.snd
  let raw : Process (In D) (Series D) := a.reader ⊚ Process.fst
  let clean : Process (In D) (Series D) := a.cleaner ⊚ raw
  Process.pi fun κ => match κ with
    | .raw => a.publishRaw ⊚ raw
    | .clean => a.publishClean ⊚ clean
    | .corrections => a.publishCorrections ⊚ corrections

/-- The raw topics hold what the publisher makes of the raw series alone. -/
theorem raw_topics (a : Acquisition D) (s : Log D.Source) (c : Log D.Correction) :
    a.run (s, c) .raw = a.publishRaw (a.reader s) :=
  rfl

/-- The clean topics hold what the publisher makes of the clean series alone: the cleaner's, on the
raw series. -/
theorem clean_topics (a : Acquisition D) (s : Log D.Source) (c : Log D.Correction) :
    a.run (s, c) .clean = a.publishClean (a.cleaner (a.reader s)) :=
  rfl

/-- The corrections topics hold what the publisher makes of the vendor's corrections alone. -/
theorem corrections_topics (a : Acquisition D) (s : Log D.Source) (c : Log D.Correction) :
    a.run (s, c) .corrections = a.publishCorrections c :=
  rfl

end Acquisition

end
```

### `variable {D : Data}`
As `variable (D : Data)`, but in braces: Lean works out $D$ from the acquisition it is given, so it isn't written.

### `def run (a : Acquisition D) : Process (In D) (AllTopics D)`
Acquisition $a$ as one process, from what it reads to all its topics. It is a process because wiring processes together gives a process (Kahn). The wiring uses these operations:

$$(g \circledcirc f)\,x = g\,(f\,x) \qquad \mathrm{fst}\,(x, y) = x \qquad \mathrm{snd}\,(x, y) = y \qquad (\mathrm{pi}\,F)\,x\,\kappa = F\,\kappa\,x$$

$g \circledcirc f$ sends the output of $f$ into $g$; $\mathrm{fst}$ and $\mathrm{snd}$ take one of two things side by side; $\mathrm{pi}\,F$ gives, for each kind $\kappa$, what $F\,\kappa$ gives, and `match κ with` says which part that is for each kind. Each `let` names one part of the wiring for the lines after it. For the source $s$ and the corrections $c$, with $r = \mathrm{reader}\,s$ the raw series:

$$\mathrm{run}\,a\,(s, c)\,\kappa = \begin{cases} \mathrm{publishRaw}\,r & \kappa = \mathrm{raw} \\ \mathrm{publishClean}\,(\mathrm{cleaner}\,r) & \kappa = \mathrm{clean} \\ \mathrm{publishCorrections}\,c & \kappa = \mathrm{corrections} \end{cases}$$

### `theorem raw_topics`, `clean_topics`, `corrections_topics`
The three lines of that equation, one theorem each: the topics of each kind hold what the publisher's part for that kind makes of its own series alone. So the clean topics are made from the clean series and nothing else. Each proof is `rfl`: the two sides are the same once the definitions are unfolded.

### `end`
Closes the `noncomputable section`.
