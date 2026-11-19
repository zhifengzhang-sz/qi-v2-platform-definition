import Kahn
import Kafka
import Contract.Market

/-!
# Acquisition

Acquisition is composed of three parts: the reader, the cleaner and the publisher. Its k-line is
market's, `Market.KLine` (`lean/Contract/Market.lean`): raw, corrected raw and clean k-lines are all
one, and so is every message it reads and every value it publishes. This file gives the parts'
shape, what each reads and writes; how each is made is the implementation's. Cleaning happens in
acquisition, not in warehousing. A working space has one acquisition (`lean/Wiring.lean`); several
working spaces may work side by side, one for each acquisition (`Workspaces`, `lean/Wiring.lean`).

Each part is any process of its type, one that gives nothing among them (`Process.const`, at the
least output). The
definition holds a part to what it reads and writes, a part of the publisher to the topics of its
own kind, and to Kahn's condition: it never takes back output, and waits for no end. What a part
gives is the implementation's: that the reader gives the vendor's series, the cleaner a clean one,
and the topics of a kind hold their series, is not required here, and is not a theorem.

Acquisition publishes three kinds of data, each to topics of its own kind: the raw series, the clean
series and the vendor's corrections. Each topic is made with no key and values of `Market.KLine`
(`Kafka.TopicOf`). The clean series is made from the raw series. The vendor's corrections are
published as they come, and acquisition applies them to nothing: it makes no corrected raw series.
Nothing published is taken back (a process never takes back output).

What acquisition reads is two logs of k-lines: its source, and the vendor's corrections, a
correction being the bar as corrected. The vendor's own form is read into k-lines before the
system's input, which is a modelling choice, not a theorem. The raw series has two parts: first
the vendor's corrected raw series, then the vendor's raw series, appended to it. The reader reads
both parts; how (a replayer in it, say) is the implementation's, and so is the switch from the
first part to the second. Here the source is one log, what the reader reads in the order it reads
it, and the reader is one process of it. That the source holds the corrected raw series first is a
modelling choice, not a theorem.

A reset, which reads the corrected raw series again, is outside the working space: within one,
nothing starts again.
-/

noncomputable section

open Kahn

/-- The three kinds of data acquisition publishes. -/
inductive Acquisition.Kind where
  | raw
  | clean
  | corrections

/-- The topics an acquisition publishes. -/
structure Acquisition.Data where
  /-- the topics that carry data of kind `κ` -/
  Topic : Kind → Type
  /-- each one a Kafka topic of k-lines, with no key -/
  topic : (κ : Kind) → Topic κ → Kafka.TopicOf Market.KLine

namespace Acquisition

/-- A k-line series. -/
abbrev Series := Log Market.KLine

/-- What acquisition reads: its source, and the vendor's corrections stream, both of k-lines. -/
abbrev In := Log Market.KLine × Log Market.KLine

variable (D : Data)

/-- The topics of kind `κ`. -/
abbrev Topics (κ : Kind) := ∀ t : D.Topic κ, (D.topic κ t).toTopic.Logs

/-- All the topics, of every kind. -/
abbrev AllTopics := ∀ κ : Kind, Topics D κ

end Acquisition

open Acquisition

/-- An acquisition, of market's k-line. -/
structure Acquisition (D : Acquisition.Data) where
  /-- the reader: reads the source, gives the raw series -/
  reader : Process (Log Market.KLine) Series
  /-- the cleaner: raw ⇒ clean -/
  cleaner : Process Series Series
  /-- the publisher, in three parts, each publishing one kind to the topics of that kind only: the raw
  series -/
  publishRaw : Process Series (Topics D .raw)
  /-- the clean series -/
  publishClean : Process Series (Topics D .clean)
  /-- the vendor's corrections -/
  publishCorrections : Process (Log Market.KLine) (Topics D .corrections)

namespace Acquisition

variable {D : Data}

/-- Acquisition as one process: from the source and the corrections to every topic. -/
def run (a : Acquisition D) : Process In (AllTopics D) :=
  let corrections : Process In (Log Market.KLine) := Process.snd
  let raw : Process In Series := a.reader ⊚ Process.fst
  let clean : Process In Series := a.cleaner ⊚ raw
  Process.pi fun κ => match κ with
    | .raw => a.publishRaw ⊚ raw
    | .clean => a.publishClean ⊚ clean
    | .corrections => a.publishCorrections ⊚ corrections

/-- The raw topics hold what the publisher makes of the raw series alone. -/
theorem raw_topics (a : Acquisition D) (s c : Log Market.KLine) :
    a.run (s, c) .raw = a.publishRaw (a.reader s) :=
  rfl

/-- The clean topics hold what the publisher makes of the clean series alone: the cleaner's, on the
raw series. -/
theorem clean_topics (a : Acquisition D) (s c : Log Market.KLine) :
    a.run (s, c) .clean = a.publishClean (a.cleaner (a.reader s)) :=
  rfl

/-- The corrections topics hold what the publisher makes of the vendor's corrections alone. -/
theorem corrections_topics (a : Acquisition D) (s c : Log Market.KLine) :
    a.run (s, c) .corrections = a.publishCorrections c :=
  rfl

end Acquisition

end
