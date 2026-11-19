import Kahn
import Kafka
import Contract.Market
import Acquisition
import Warehousing
import Visualization
import MarketModelEngine
import Workspace

/-!
# The wiring

The components as one working space, wired by the topics:

* acquisition, one in a working space, reads its source and the vendor's corrections stream, and
  writes its topics of the three kinds: raw, clean, corrections;
* warehousing reads all of acquisition's topics, of every kind, and pushes them all into the database:
  a topic's table holds what the consumer pushes for every one of its partitions, in no order
  (`table_rows`);
* the market model engine, when the working space has one, reads clean topics, and writes topics of
  its own;
* visualization reads clean topics and all of the engine's, and gives one log for each partition of
  each, of the type of its values, from which the chart in the HTML page is drawn.

Every message of the working space is a contract's record, or made of them: both input logs and
acquisition's topics are of market's `KLine`, and the engine's topics of its results
(`MarketModelEngine.Result`), each one of chanlun's records; no topic has a key (`Kafka.TopicOf`).
What warehousing pushes for a topic, and each of visualization's logs, are of the type of the topic's
values.

The engine and visualization are given clean topics only: what they read is a clean topic by its
type. What leaves the system: warehousing's pushes and visualization's logs. The engine may be
missing: a working space without it has acquisition, warehousing and visualization alone, and then
visualization's logs are drawn from the clean topics alone (`chart_without_engine`).

Several working spaces side by side are each one a wiring makes (`Workspaces`).
-/

noncomputable section

open Kahn

namespace Wiring

/-- The input logs: acquisition's source, and the vendor's corrections stream. -/
inductive Feed where
  | source
  | corrections

/-- The messages of each input log: market's k-lines. -/
abbrev InputMsg (_ : Feed) : Type := Market.KLine

/-- The input logs. -/
abbrev Inputs := ∀ i : Feed, Log (InputMsg i)

/-- Acquisition's topics: every topic of every kind. -/
abbrev AcqTopic (A : Acquisition.Data) := Σ κ : Acquisition.Kind, A.Topic κ

/-- Each of acquisition's topics, a Kafka topic. -/
def acqTopic (A : Acquisition.Data) (t : AcqTopic A) : Kafka.Topic :=
  (A.topic t.1 t.2).toTopic

/-- Acquisition's topics, all of them. -/
abbrev AcqTopics (A : Acquisition.Data) := ∀ t : AcqTopic A, (acqTopic A t).Logs

/-- Acquisition's clean topics. -/
abbrev CleanTopic (A : Acquisition.Data) := A.Topic .clean

/-- A clean topic, as one of acquisition's topics. -/
def CleanTopic.toAcq {A : Acquisition.Data} (t : CleanTopic A) : AcqTopic A :=
  ⟨.clean, t⟩

/-- Warehousing reads all of acquisition's topics, of every kind. -/
def warehousingData (A : Acquisition.Data) : Warehousing.Data where
  Topic := AcqTopic A
  topic := acqTopic A

/-- The engine reads clean topics, and writes its own. -/
def engineData (A : Acquisition.Data) (Clean : Type) (clean : Clean → CleanTopic A) (Out : Type)
    (outTopic : Out → Kafka.TopicOf MarketModelEngine.Result) : MarketModelEngine.Data where
  In := Clean
  inTopic t := A.topic .clean (clean t)
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
  outTopic : Out → Kafka.TopicOf MarketModelEngine.Result
  /-- no two of the engine's topics have the same name -/
  names_distinct : ∀ t t' : Out, (outTopic t).name = (outTopic t').name → t = t'
  /-- the market model engine -/
  engine : MarketModelEngine (engineData A Clean clean Out outTopic)

/-- The engine's topics: none without the engine. -/
def engineOut {A : Acquisition.Data} : Option (Engine A) → Type
  | none => Empty
  | some e => e.Out

/-- Each one a topic of the engine's results. -/
def engineTopic {A : Acquisition.Data} :
    (o : Option (Engine A)) → engineOut o → Kafka.TopicOf MarketModelEngine.Result
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
    (o : Option (Engine A)) →
      Process (AcqTopics A) (∀ t : engineOut o, (engineTopic o t).toTopic.Logs)
  | none => nothing id
  | some e => e.engine.worker ⊚ engineIn e

/-- Visualization reads clean topics, and all of the engine's. -/
def visualizationData (A : Acquisition.Data) (Shown : Type) (shown : Shown → CleanTopic A)
    (o : Option (Engine A)) : Visualization.Data where
  Clean := Shown
  cleanTopic t := A.topic .clean (shown t)
  Model := engineOut o
  modelTopic := engineTopic o

end Wiring

open Wiring

/-- The components and how they connect. -/
structure Wiring where
  /-- the topics acquisition publishes -/
  A : Acquisition.Data
  /-- the working space's one acquisition -/
  acquisition : Acquisition A
  /-- no two of acquisition's topics have the same name -/
  acq_names : ∀ t t' : AcqTopic A, (acqTopic A t).name = (acqTopic A t').name → t = t'
  /-- warehousing, on all of acquisition's topics -/
  warehousing : Warehousing (warehousingData A)
  /-- the table of the database each of acquisition's topics is pushed into, every partition of it;
  several topics may go into one table -/
  table : AcqTopic A → String
  /-- the market model engine, if the working space has one -/
  engine : Option (Engine A)
  /-- no topic of the engine's has the name of one of acquisition's -/
  cross_names : ∀ (t : AcqTopic A) (t' : engineOut engine),
    (acqTopic A t).name ≠ (engineTopic engine t').name
  /-- the clean topics visualization reads -/
  Shown : Type
  shown : Shown → CleanTopic A
  /-- visualization, on those clean topics and all of the engine's -/
  visualization : Visualization (visualizationData A Shown shown engine)

namespace Wiring

variable (S : Wiring)

/-- The topics each component writes: acquisition's and the engine's; the others write none. -/
def Topic : Workspace.Component → Type
  | .acquisition => AcqTopic S.A
  | .marketModelEngine => engineOut S.engine
  | .warehousing => Empty
  | .visualization => Empty

/-- Each one a Kafka topic. -/
def topic : (c : Workspace.Component) → S.Topic c → Kafka.Topic
  | .acquisition, t => acqTopic S.A t
  | .marketModelEngine, t => (engineTopic S.engine t).toTopic
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
acquisition's topics, and visualization's logs, one for each partition of each clean topic it reads
and of each of the engine's. -/
def Output : Workspace.Component → Type
  | .warehousing => Σ t : AcqTopic S.A, Fin (acqTopic S.A t).partitions
  | .visualization =>
      (Σ t : S.Shown, Fin (S.A.topic .clean (S.shown t)).partitions) ⊕
        (Σ t : engineOut S.engine, Fin (engineTopic S.engine t).partitions)
  | .acquisition => Empty
  | .marketModelEngine => Empty

/-- The messages of each of them, of the type of the values of the topic it is from: k-lines for each
of acquisition's topics, results for each of the engine's. -/
def OutputMsg : (c : Workspace.Component) → S.Output c → Type
  | .warehousing, _ => Market.KLine
  | .visualization, .inl _ => Market.KLine
  | .visualization, .inr _ => MarketModelEngine.Result
  | .acquisition, o => nomatch o
  | .marketModelEngine, o => nomatch o

/-- All the topics. -/
abbrev Topics := ∀ (c : Workspace.Component) (t : S.Topic c), (S.topic c t).Logs

/-- The input logs, side by side, as acquisition reads them. -/
def feeds : Process Inputs Acquisition.In :=
  Process.pair (Process.proj (κ := fun i => Log (InputMsg i)) .source)
    (Process.proj (κ := fun i => Log (InputMsg i)) .corrections)

/-- Acquisition: from the inputs to all of its topics. -/
def acquisitions : Process Inputs (AcqTopics S.A) :=
  Process.pi fun t =>
    Process.proj (κ := fun t' => (S.A.topic t.1 t').toTopic.Logs) t.2 ⊚
      (Process.proj (κ := Acquisition.Topics S.A) t.1 ⊚ (S.acquisition.run ⊚ feeds))

/-- Acquisition's topics, from all the topics. -/
def acqPart : Process S.Topics (AcqTopics S.A) :=
  Process.proj (κ := fun c => ∀ t : S.Topic c, (S.topic c t).Logs) .acquisition

/-- The engine's topics, from all the topics. -/
def enginePart :
    Process S.Topics (∀ t : engineOut S.engine, (engineTopic S.engine t).toTopic.Logs) :=
  Process.proj (κ := fun c => ∀ t : S.Topic c, (S.topic c t).Logs) .marketModelEngine

/-- What visualization reads: its clean topics, from acquisition's, and the engine's topics. -/
def visualizationIn :
    Process S.Topics (Visualization.In (visualizationData S.A S.Shown S.shown S.engine)) :=
  Process.pair
    (Process.pi fun t => Process.proj (κ := fun t' => (acqTopic S.A t').Logs) (S.shown t).toAcq ⊚ S.acqPart)
    S.enginePart

/-- Visualization's logs, one for each partition of each topic it reads, as logs that leave the
system. -/
def visualizationOut :
    Process (Visualization.Out (visualizationData S.A S.Shown S.shown S.engine))
      (∀ o : S.Output .visualization, Log (S.OutputMsg .visualization o)) :=
  Process.pi fun
    | .inl o =>
      Process.proj (κ := fun _ : Fin (S.A.topic .clean (S.shown o.1)).partitions => Log Market.KLine) o.2 ⊚
        (Process.proj (κ := fun t : S.Shown =>
            Fin (S.A.topic .clean (S.shown t)).partitions → Log Market.KLine) o.1 ⊚
          Process.fst)
    | .inr o =>
      Process.proj (κ := fun _ : Fin (engineTopic S.engine o.1).partitions =>
          Log MarketModelEngine.Result) o.2 ⊚
        (Process.proj (κ := fun t : engineOut S.engine =>
            Fin (engineTopic S.engine t).partitions → Log MarketModelEngine.Result) o.1 ⊚
          Process.snd)

/-- Warehousing's pushes, one log for each partition of each of acquisition's topics. -/
def pushes : Process (AcqTopics S.A) (∀ o : S.Output .warehousing, Log (S.OutputMsg .warehousing o)) :=
  Process.pi fun o =>
    Process.proj (κ := fun _ : Fin (acqTopic S.A o.1).partitions => Log Market.KLine) o.2 ⊚
      (Process.proj (κ := fun t => Fin (acqTopic S.A t).partitions → Log Market.KLine) o.1 ⊚
        S.warehousing.run)

/-- The working space the wiring makes. Acquisition reads the inputs; warehousing, the engine and
visualization read the topics. -/
def workspace : Workspace where
  Input := Feed
  InputMsg := InputMsg
  Topic := S.Topic
  topic := S.topic
  names_distinct := S.names_distinct
  Output := S.Output
  OutputMsg := S.OutputMsg
  table o := S.table o.1
  acquisition := Process.pair S.acquisitions (nothing id)
  warehousing := Process.pair (nothing id) (S.pushes ⊚ S.acqPart)
  visualization :=
    Process.pair (nothing id) (S.visualizationOut ⊚ S.visualization.chart ⊚ S.visualizationIn)
  marketModelEngine := Process.pair (engineRun S.engine ⊚ S.acqPart) (nothing id)

/-- Acquisition's topics hold what acquisition writes from the inputs alone. -/
theorem acquisition_topics (i : Inputs) :
    S.workspace.topics i .acquisition = S.acquisitions i :=
  S.workspace.acquisition_topics i

/-- The clean topics hold what the publisher makes of the clean series alone: the cleaner on the raw
series, the reader's from the source. -/
theorem clean_topics (i : Inputs) (t : S.A.Topic .clean) :
    S.workspace.topics i .acquisition ⟨.clean, t⟩ =
      S.acquisition.publishClean (S.acquisition.cleaner (S.acquisition.reader (i .source))) t := by
  rw [S.acquisition_topics i]
  rfl

/-- The engine's topics hold what the engine writes from acquisition's topics: nothing without the
engine, and with it what its worker writes from its clean topics. -/
theorem engine_topics (i : Inputs) :
    S.workspace.topics i .marketModelEngine = engineRun S.engine (S.acquisitions i) := by
  rw [← S.workspace.topics_eq i .marketModelEngine]
  show engineRun S.engine (S.workspace.topics i .acquisition) = _
  rw [S.acquisition_topics i]

/-- Warehousing pushes, for partition `p` of acquisition's topic `t`, the consumer of `t`'s schema, no
key and values of k-lines, on that partition of what acquisition writes. -/
theorem warehousing_pushes (i : Inputs) (t : AcqTopic S.A) (p : Fin (acqTopic S.A t).partitions) :
    (S.workspace.system i).2 .warehousing ⟨t, p⟩ =
      S.warehousing.consumer Empty Market.KLine (S.acquisitions i t p) := by
  show S.warehousing.consumer _ _ (S.workspace.topics i .acquisition t p) = _
  rw [S.acquisition_topics i]
  rfl

/-- The table named `name` holds, for partition `p` of a topic `t` pushed into it, exactly the
k-lines the consumer of `t`'s schema pushes for that partition of what acquisition writes, in no
order. -/
theorem table_rows (i : Inputs) (name : String) (t : AcqTopic S.A)
    (p : Fin (acqTopic S.A t).partitions) (h : S.table t = name) (m : Market.KLine) :
    (S.workspace.tableRows name i).has ⟨⟨⟨t, p⟩, h⟩, m⟩ ↔
      ∃ n, (S.warehousing.consumer Empty Market.KLine (S.acquisitions i t p)).get n = some m := by
  rw [← S.warehousing_pushes i t p]
  exact Iff.rfl

/-- Visualization's logs are what it gives from its clean topics and the engine's topics, one for
each partition of each. -/
theorem visualization_chart (i : Inputs) :
    (S.workspace.system i).2 .visualization =
      S.visualizationOut (S.visualization.chart
        (fun t => S.acquisitions i (S.shown t).toAcq, engineRun S.engine (S.acquisitions i))) := by
  show S.visualizationOut (S.visualization.chart
      (fun t => S.workspace.topics i .acquisition (S.shown t).toAcq,
        S.workspace.topics i .marketModelEngine)) = _
  rw [S.acquisition_topics i, S.engine_topics i]

/-- Without the engine, visualization's logs are given from its clean topics alone: they are the
same whatever stands for the engine's topics, of which there are none. -/
theorem chart_without_engine (h : S.engine = none) (i : Inputs)
    (x : ∀ t : engineOut S.engine, (engineTopic S.engine t).toTopic.Logs) :
    (S.workspace.system i).2 .visualization =
      S.visualizationOut (S.visualization.chart (fun t => S.acquisitions i (S.shown t).toAcq, x)) := by
  have empty : engineOut S.engine → False := by
    rw [h]
    exact fun t => nomatch t
  rw [S.visualization_chart i]
  congr 3
  funext t
  exact (empty t).elim

end Wiring

/-- Several working spaces side by side, each one a wiring makes, one for each acquisition. Each
topic has one writer and each table of the database one working space: no two topics of any of them
have the same name, and no table is written by two of them. -/
structure Workspaces (ι : Type) where
  /-- the wirings, each making one working space -/
  space : ι → Wiring
  /-- no two topics, of one working space or of two, have the same name -/
  topics_distinct : ∀ (i j : ι) (c c' : Workspace.Component) (t : (space i).Topic c)
      (t' : (space j).Topic c'),
    ((space i).topic c t).name = ((space j).topic c' t').name →
      (⟨i, c, t⟩ : Σ i, Σ c, (space i).Topic c) = ⟨j, c', t'⟩
  /-- no table is written by two working spaces: for working spaces `i` and `j`, a topic `t` of
  `i`'s acquisition and `t'` of `j`'s, pushed into one table, `i` and `j` are one -/
  tables_distinct : ∀ (i j : ι) (t : AcqTopic (space i).A) (t' : AcqTopic (space j).A),
    (space i).table t = (space j).table t' → i = j

namespace Workspaces

variable {ι : Type} (S : Workspaces ι)

/-- The working spaces as one process: each one's system, on its own input logs. -/
def system :
    Process (ι → Wiring.Inputs)
      (∀ i, (S.space i).workspace.Topics × (S.space i).workspace.Outputs) :=
  Process.pi fun i => (S.space i).workspace.system ⊚ Process.proj (κ := fun _ : ι => Wiring.Inputs) i

/-- What each working space gives depends on its own input logs alone. -/
theorem system_apply (x : ι → Wiring.Inputs) (i : ι) :
    S.system x i = (S.space i).workspace.system (x i) :=
  rfl

end Workspaces

end
