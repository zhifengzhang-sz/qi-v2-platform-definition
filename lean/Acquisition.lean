import Kahn
import Kafka

/-!
# Acquisition

Each k-line contract defines an acquisition, composed of three parts: the reader, the cleaner and the
publisher. This file gives their shape, what each reads and writes; how each is made is the
implementation's. Cleaning happens in acquisition, not in warehousing. A working space has one
acquisition (`lean/Wiring.lean`); several working spaces may work side by side, one for each
acquisition (`Workspaces`, `lean/Workspace.lean`).

Acquisition publishes four kinds of data, each to topics of its own kind: the raw series, the
corrected raw series, the clean series and the vendor's corrections. Nothing published is taken back
(a process never takes back output), so a correction is added, never applied in place:

* the corrected raw series is a log of revisions: a k-line's first version, then each corrected
  version as a message of its own. The k-line as it stands now is a view of that log, and no process
  gives such a view (`Kafka.compaction_not_process`).
* the clean series may start again. A reset is a message of the clean series, and what follows it is
  the clean series made again. The clean series as it stands, the k-lines since the last reset, is a
  view, and no process gives it (`Acquisition.Clean.sinceReset_not_process`).

Acquisition has two readers: the vendor's, and the reset's. A reset is a replay: the reset's reader
reads the history again from its start, the clean series is made again from it, and when the replay
is over the vendor's series takes over. When a reset comes, when the replay is over and the switch to
the vendor's series, are acquisition's own state: the implementation's. What the history is (a file,
a database, or acquisition's own topics read back, a loop the base allows) is left open.
-/

noncomputable section

open Kahn

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
