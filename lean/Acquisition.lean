import Kahn
import Kafka

/-!
# Acquisition

Each k-line contract defines an acquisition, composed of three parts: the reader, the cleaner and the
publisher. This file gives their shape, what each reads and writes; how each is made is the
implementation's. Cleaning happens in acquisition, not in warehousing. A working space has one
acquisition (`lean/Wiring.lean`); several working spaces may work side by side, one for each
acquisition (`Workspaces`, `lean/Workspace.lean`).

Acquisition publishes three kinds of data, each to topics of its own kind: the raw series, the clean
series and the vendor's corrections. The clean series is made from the raw series. The vendor's
corrections are published as they come, and acquisition applies them to nothing: it makes no
corrected raw series. Nothing published is taken back (a process never takes back output).

The raw series has two parts: first the vendor's corrected raw series, then the vendor's raw series,
appended to it. The reader reads both parts; how (a replayer in it, say) is the implementation's,
and so is the switch from the first part to the second. Here the source is one log, what the reader
reads in the order it reads it, and the reader is one process of it. That the source holds the
corrected raw series first is a modelling choice, not a theorem.

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
