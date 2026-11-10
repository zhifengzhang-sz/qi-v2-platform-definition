import Kahn
import Kafka
import Acquisition
import Warehousing
import Visualization
import MarketModelEngine
import Workspace

/-!
# The wiring

The components as one working space, wired by the topics:

* acquisition, one in a working space, reads its source, the vendor's corrections stream and the
  history its reset replays, and writes its topics of the four kinds: raw, corrected raw, clean,
  corrections;
* warehousing reads all of acquisition's topics, of every kind, and pushes them all into the database;
* the market model engine, when the working space has one, reads clean topics, and writes topics of
  its own;
* visualization reads clean topics and all of the engine's, and gives the chart in the HTML page.

The engine and visualization are given clean topics only: what they read is a clean topic by its
type. What leaves the system: warehousing's pushes and visualization's chart. The engine may be
missing: a working space without it has acquisition, warehousing and visualization alone, and then
the chart is drawn from the clean topics alone (`chart_without_engine`).
-/

noncomputable section

open Kahn

namespace Wiring

/-- The input logs: acquisition's source, the vendor's corrections stream, and the history the reset
replays. -/
inductive Feed where
  | source
  | corrections
  | history

/-- Acquisition's topics: every topic of every kind. -/
abbrev AcqTopic (A : Acquisition.Data) := Σ κ : Acquisition.Kind, A.Topic κ

/-- Each of acquisition's topics, a Kafka topic. -/
def acqTopic (A : Acquisition.Data) (t : AcqTopic A) : Kafka.Topic :=
  A.topic t.1 t.2

/-- Acquisition's topics, all of them. -/
abbrev AcqTopics (A : Acquisition.Data) := ∀ t : AcqTopic A, (acqTopic A t).Logs

/-- Acquisition's clean topics. -/
abbrev CleanTopic (A : Acquisition.Data) := A.Topic .clean

/-- A clean topic, as one of acquisition's topics. -/
def CleanTopic.toAcq {A : Acquisition.Data} (t : CleanTopic A) : AcqTopic A :=
  ⟨.clean, t⟩

/-- Warehousing reads all of acquisition's topics, of every kind. -/
def warehousingData (A : Acquisition.Data) (Push : (K V : Type) → Type) : Warehousing.Data where
  Topic := AcqTopic A
  topic := acqTopic A
  Push := Push

/-- The engine reads clean topics, and writes its own. -/
def engineData (A : Acquisition.Data) (Clean : Type) (clean : Clean → CleanTopic A) (Out : Type)
    (outTopic : Out → Kafka.Topic) : MarketModelEngine.Data where
  In := Clean
  inTopic t := acqTopic A (clean t).toAcq
  Out := Out
  outTopic := outTopic

/-- The market model engine in a working space: the clean topics it reads, the topics it writes (no
two of the same name), and the engine. -/
structure Engine (A : Acquisition.Data) where
  /-- the clean topics the engine reads -/
  Clean : Type
  clean : Clean → CleanTopic A
  /-- the engine's topics -/
  Out : Type
  outTopic : Out → Kafka.Topic
  /-- no two of the engine's topics have the same name -/
  names_distinct : ∀ t t' : Out, (outTopic t).name = (outTopic t').name → t = t'
  /-- the market model engine -/
  engine : MarketModelEngine (engineData A Clean clean Out outTopic)

/-- The engine's topics: none without the engine. -/
def engineOut {A : Acquisition.Data} : Option (Engine A) → Type
  | none => Empty
  | some e => e.Out

/-- Each one a Kafka topic. -/
def engineTopic {A : Acquisition.Data} : (o : Option (Engine A)) → engineOut o → Kafka.Topic
  | none, t => nomatch t
  | some e, t => e.outTopic t

/-- What the engine reads: its clean topics, from acquisition's. -/
def engineIn {A : Acquisition.Data} (e : Engine A) :
    Process (AcqTopics A) (∀ t : e.Clean, (acqTopic A (e.clean t).toAcq).Logs) :=
  Process.pi fun t => Process.proj (κ := fun t' => (acqTopic A t').Logs) (e.clean t).toAcq

/-- Nothing to write: a family over no index. -/
def nothing {α ι : Type} [Domain α] {κ : ι → Type} [∀ i, Domain (κ i)] (h : ι → Empty) :
    Process α (∀ i, κ i) :=
  Process.pi fun i => nomatch h i

/-- What the engine writes, from acquisition's topics: nothing without the engine. -/
def engineRun {A : Acquisition.Data} :
    (o : Option (Engine A)) → Process (AcqTopics A) (∀ t : engineOut o, (engineTopic o t).Logs)
  | none => nothing id
  | some e => e.engine.worker ⊚ engineIn e

/-- Visualization reads clean topics, and all of the engine's. -/
def visualizationData (A : Acquisition.Data) (Shown : Type) (shown : Shown → CleanTopic A)
    (o : Option (Engine A)) (View : Type) : Visualization.Data where
  Clean := Shown
  cleanTopic t := acqTopic A (shown t).toAcq
  Model := engineOut o
  modelTopic := engineTopic o
  View := View

end Wiring

open Wiring

/-- The components and how they connect. -/
structure Wiring where
  /-- what acquisition works on, which its k-line contract defines -/
  A : Acquisition.Data
  /-- the working space's one acquisition -/
  acquisition : Acquisition A
  /-- no two of acquisition's topics have the same name -/
  acq_names : ∀ t t' : AcqTopic A, (acqTopic A t).name = (acqTopic A t').name → t = t'
  /-- what the warehouse consumer pushes -/
  Push : (K V : Type) → Type
  /-- warehousing, on all of acquisition's topics -/
  warehousing : Warehousing (warehousingData A Push)
  /-- the table of the database each of acquisition's topics is pushed into -/
  table : AcqTopic A → String
  /-- the market model engine, if the working space has one -/
  engine : Option (Engine A)
  /-- no topic of the engine's has the name of one of acquisition's -/
  cross_names : ∀ (t : AcqTopic A) (t' : engineOut engine),
    (acqTopic A t).name ≠ (engineTopic engine t').name
  /-- the clean topics visualization reads -/
  Shown : Type
  shown : Shown → CleanTopic A
  /-- one update of the chart -/
  View : Type
  /-- visualization, on those clean topics and all of the engine's -/
  visualization : Visualization (visualizationData A Shown shown engine View)

namespace Wiring

variable (S : Wiring)

/-- The messages of each input log. -/
def InputMsg : Feed → Type
  | .source => S.A.Source
  | .corrections => S.A.Correction
  | .history => S.A.History

/-- The topics each component writes: acquisition's and the engine's; the others write none. -/
def Topic : Workspace.Component → Type
  | .acquisition => AcqTopic S.A
  | .marketModelEngine => engineOut S.engine
  | .warehousing => Empty
  | .visualization => Empty

/-- Each one a Kafka topic. -/
def topic : (c : Workspace.Component) → S.Topic c → Kafka.Topic
  | .acquisition, t => acqTopic S.A t
  | .marketModelEngine, t => engineTopic S.engine t
  | .warehousing, t => nomatch t
  | .visualization, t => nomatch t

/-- No two of the engine's topics have the same name. -/
theorem engineTopic_names {A : Acquisition.Data} :
    ∀ (o : Option (Engine A)) (t t' : engineOut o),
      (engineTopic o t).name = (engineTopic o t').name → t = t'
  | none, t, _, _ => nomatch t
  | some e, t, t', h => e.names_distinct t t' h

/-- No two topics of the working space have the same name. -/
theorem names_distinct : ∀ (c c' : Workspace.Component) (t : S.Topic c) (t' : S.Topic c'),
    (S.topic c t).name = (S.topic c' t').name → (⟨c, t⟩ : Σ c, S.Topic c) = ⟨c', t'⟩
  | .acquisition, .acquisition, t, t', h => by
      obtain rfl := S.acq_names t t' h
      rfl
  | .acquisition, .marketModelEngine, t, t', h => absurd h (S.cross_names t t')
  | .marketModelEngine, .acquisition, t, t', h => absurd h.symm (S.cross_names t' t)
  | .marketModelEngine, .marketModelEngine, t, t', h => by
      obtain rfl := engineTopic_names S.engine t t' h
      rfl
  | .warehousing, _, t, _, _ => nomatch t
  | .visualization, _, t, _, _ => nomatch t
  | _, .warehousing, _, t', _ => nomatch t'
  | _, .visualization, _, t', _ => nomatch t'

/-- The logs that leave the system: warehousing's pushes, one for each partition of each of
acquisition's topics, and visualization's chart. -/
def Output : Workspace.Component → Type
  | .warehousing => Σ t : AcqTopic S.A, Fin (acqTopic S.A t).partitions
  | .visualization => Unit
  | .acquisition => Empty
  | .marketModelEngine => Empty

/-- The messages of each of them. -/
def OutputMsg : (c : Workspace.Component) → S.Output c → Type
  | .warehousing, o => S.Push (acqTopic S.A o.1).Key (acqTopic S.A o.1).Value
  | .visualization, _ => S.View
  | .acquisition, o => nomatch o
  | .marketModelEngine, o => nomatch o

/-- The input logs. -/
abbrev Inputs := ∀ i : Feed, Log (S.InputMsg i)

/-- All the topics. -/
abbrev Topics := ∀ (c : Workspace.Component) (t : S.Topic c), (S.topic c t).Logs

/-- The input logs, side by side, as acquisition reads them. -/
def feeds : Process S.Inputs (Acquisition.In S.A) :=
  Process.pair (Process.proj (κ := fun i => Log (S.InputMsg i)) .source)
    (Process.pair (Process.proj (κ := fun i => Log (S.InputMsg i)) .corrections)
      (Process.proj (κ := fun i => Log (S.InputMsg i)) .history))

/-- Acquisition: from the inputs to all of its topics. -/
def acquisitions : Process S.Inputs (AcqTopics S.A) :=
  Process.pi fun t =>
    Process.proj (κ := fun t' => (S.A.topic t.1 t').Logs) t.2 ⊚
      (Process.proj (κ := Acquisition.Topics S.A) t.1 ⊚ (S.acquisition.run ⊚ S.feeds))

/-- Acquisition's topics, from all the topics. -/
def acqPart : Process S.Topics (AcqTopics S.A) :=
  Process.proj (κ := fun c => ∀ t : S.Topic c, (S.topic c t).Logs) .acquisition

/-- The engine's topics, from all the topics. -/
def enginePart : Process S.Topics (∀ t : engineOut S.engine, (engineTopic S.engine t).Logs) :=
  Process.proj (κ := fun c => ∀ t : S.Topic c, (S.topic c t).Logs) .marketModelEngine

/-- What visualization reads: its clean topics, from acquisition's, and the engine's topics. -/
def visualizationIn :
    Process S.Topics (Visualization.In (visualizationData S.A S.Shown S.shown S.engine S.View)) :=
  Process.pair
    (Process.pi fun t => Process.proj (κ := fun t' => (acqTopic S.A t').Logs) (S.shown t).toAcq ⊚ S.acqPart)
    S.enginePart

/-- Warehousing's pushes, one log for each partition of each of acquisition's topics. -/
def pushes : Process (AcqTopics S.A) (∀ o : S.Output .warehousing, Log (S.OutputMsg .warehousing o)) :=
  Process.pi fun o =>
    Process.proj (κ := fun _ : Fin (acqTopic S.A o.1).partitions =>
        Log (S.Push (acqTopic S.A o.1).Key (acqTopic S.A o.1).Value)) o.2 ⊚
      (Process.proj (κ := fun t => Fin (acqTopic S.A t).partitions →
          Log (S.Push (acqTopic S.A t).Key (acqTopic S.A t).Value)) o.1 ⊚
        S.warehousing.run)

/-- The working space the wiring makes. Acquisition reads the inputs; warehousing, the engine and
visualization read the topics. -/
def workspace : Workspace where
  Input := Feed
  InputMsg := S.InputMsg
  Topic := S.Topic
  topic := S.topic
  names_distinct := S.names_distinct
  Output := S.Output
  OutputMsg := S.OutputMsg
  table o := S.table o.1
  acquisition := Process.pair S.acquisitions (nothing id)
  warehousing := Process.pair (nothing id) (S.pushes ⊚ S.acqPart)
  visualization :=
    Process.pair (nothing id) (Process.pi fun _ => S.visualization.chart ⊚ S.visualizationIn)
  marketModelEngine := Process.pair (engineRun S.engine ⊚ S.acqPart) (nothing id)

/-- Acquisition's topics hold what acquisition writes from the inputs alone. -/
theorem acquisition_topics (i : S.Inputs) :
    S.workspace.topics i .acquisition = S.acquisitions i :=
  S.workspace.acquisition_topics i

/-- The clean topics hold what the publisher makes of the clean series alone: the cleaner on the
corrected raw series, from the source and the corrections, and on the replay of the history. -/
theorem clean_topics (i : S.Inputs) (t : S.A.Topic .clean) :
    S.workspace.topics i .acquisition ⟨.clean, t⟩ =
      S.acquisition.publishClean
        (S.acquisition.cleaner (S.acquisition.correct (S.acquisition.reader (i .source), i .corrections),
          S.acquisition.replayer (i .history)))
        t := by
  rw [S.acquisition_topics i]
  rfl

/-- The engine's topics hold what the engine writes from acquisition's topics: nothing without the
engine, and with it what its worker writes from its clean topics. -/
theorem engine_topics (i : S.Inputs) :
    S.workspace.topics i .marketModelEngine = engineRun S.engine (S.acquisitions i) := by
  rw [← S.workspace.topics_eq i .marketModelEngine]
  show engineRun S.engine (S.workspace.topics i .acquisition) = _
  rw [S.acquisition_topics i]

/-- Warehousing pushes, for partition `p` of acquisition's topic `t`, the consumer of `t`'s schema on
that partition of what acquisition writes. -/
theorem warehousing_pushes (i : S.Inputs) (t : AcqTopic S.A) (p : Fin (acqTopic S.A t).partitions) :
    (S.workspace.system i).2 .warehousing ⟨t, p⟩ =
      S.warehousing.consumer (acqTopic S.A t).Key (acqTopic S.A t).Value (S.acquisitions i t p) := by
  show S.warehousing.consumer _ _ (S.workspace.topics i .acquisition t p) = _
  rw [S.acquisition_topics i]
  rfl

/-- Visualization's chart is drawn from its clean topics and the engine's topics. -/
theorem visualization_chart (i : S.Inputs) :
    (S.workspace.system i).2 .visualization () =
      S.visualization.chart
        (fun t => S.acquisitions i (S.shown t).toAcq, engineRun S.engine (S.acquisitions i)) := by
  show S.visualization.chart
      (fun t => S.workspace.topics i .acquisition (S.shown t).toAcq,
        S.workspace.topics i .marketModelEngine) = _
  rw [S.acquisition_topics i, S.engine_topics i]

/-- Without the engine, the chart is drawn from its clean topics alone: it is the same whatever
stands for the engine's topics, of which there are none. -/
theorem chart_without_engine (h : S.engine = none) (i : S.Inputs)
    (x : ∀ t : engineOut S.engine, (engineTopic S.engine t).Logs) :
    (S.workspace.system i).2 .visualization () =
      S.visualization.chart (fun t => S.acquisitions i (S.shown t).toAcq, x) := by
  have empty : engineOut S.engine → False := by
    rw [h]
    exact fun t => nomatch t
  rw [S.visualization_chart i]
  congr 2
  funext t
  exact (empty t).elim

end Wiring

end
