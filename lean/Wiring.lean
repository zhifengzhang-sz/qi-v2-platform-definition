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

The components as one working space, of one series, wired by the topics:

* acquisition, one in a working space, reads its source and the vendor's corrections stream, and
  writes its three topics, one of each kind: raw, clean, corrections;
* warehousing reads acquisition's three topics and pushes them all into the database: a topic's
  table holds what the consumer pushes for it, in no order (`table_rows`);
* the market model engine, when the working space has one, reads the clean topic and writes its own
  topic, its series' chanlun results;
* visualization reads the clean topic and the engine's, and gives one log for each, of the type of
  its values, from which the chart in the HTML page is drawn.

Each topic is named by the naming (`Naming`) from the series' signature and the topic's kind, and has
one partition, no key and its kind's message (`Kafka.Topic.ofName`): so no two topics of the working
space have one name (`names_distinct`, a theorem). Every message of the working space is a
contract's record, or made of them: both input logs and acquisition's topics are of market's
`KLine`, and the engine's topic of its results (`MarketModelEngine.Result`), each one of chanlun's
records. What warehousing pushes for a topic, and each of visualization's logs, are of the type of
the topic's values.

What leaves the system: warehousing's pushes and visualization's logs. The engine may be missing: a
working space without it has acquisition, warehousing and visualization alone, and then
visualization's logs are given from the clean topic alone (`chart_without_engine`).

Several working spaces side by side are each one a wiring makes, of one naming, no two of one
signature (`Workspaces`): so no two topics of any of them have one name (`Workspaces.topics_distinct`,
a theorem).
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

/-- A topic's kind: one of acquisition's three, or the engine's results. -/
inductive TopicKind where
  | acquisition (κ : Acquisition.Kind)
  | results

/-- The naming: one function of a series' signature and a topic's kind to the topic's name, losing
neither. -/
structure Naming where
  /-- the name of the topic of kind `k` of the series of signature `s` -/
  name : Acquisition.Signature → TopicKind → String
  /-- two pairs of one name are one pair -/
  injective : ∀ s s' k k', name s k = name s' k' → s = s' ∧ k = k'

variable (N : Naming)

/-- Acquisition's topic of kind `κ`, of the series of signature `s`. -/
abbrev acqTopic (s : Acquisition.Signature) (κ : Acquisition.Kind) : Kafka.Topic :=
  Kafka.Topic.ofName (N.name s (.acquisition κ)) Market.KLine

/-- The engine's topic, of the series of signature `s`: its results. -/
abbrev engineTopic (s : Acquisition.Signature) : Kafka.Topic :=
  Kafka.Topic.ofName (N.name s .results) MarketModelEngine.Result

/-- Warehousing reads acquisition's three topics. -/
def warehousingData (s : Acquisition.Signature) : Warehousing.Data where
  Topic := Acquisition.Kind
  topic := acqTopic N s

/-- The engine's topics: one with the engine, none without it. -/
def engineOut : Option MarketModelEngine → Type
  | none => Empty
  | some _ => Unit

/-- There is at most one of the engine's topics. -/
theorem engineOut_eq : ∀ (o : Option MarketModelEngine) (t t' : engineOut o), t = t'
  | none, t, _ => nomatch t
  | some _, (), () => rfl

/-- Nothing to write: a family over no index. -/
def nothing {α ι : Type} [Domain α] {κ : ι → Type} [∀ i, Domain (κ i)] (h : ι → Empty) :
    Process α (∀ i, κ i) :=
  Process.pi fun i => nomatch h i

end Wiring

open Wiring

/-- The components and how they connect, of the naming `N`. -/
structure Wiring (N : Naming) where
  /-- the signature of the working space's one series -/
  signature : Acquisition.Signature
  /-- the working space's one acquisition -/
  acquisition : Acquisition
  /-- warehousing, on acquisition's three topics -/
  warehousing : Warehousing (warehousingData N signature)
  /-- the table of the database each of acquisition's topics is pushed into; several topics may go
  into one table -/
  table : Acquisition.Kind → String
  /-- the market model engine, if the working space has one -/
  engine : Option MarketModelEngine
  /-- visualization, on the clean topic and the engine's -/
  visualization : Visualization (engineOut engine)

namespace Wiring

variable {N : Naming} (S : Wiring N)

/-- The topics each component writes: acquisition's three and the engine's; the others write none. -/
def Topic : Workspace.Component → Type
  | .acquisition => Acquisition.Kind
  | .marketModelEngine => engineOut S.engine
  | .warehousing => Empty
  | .visualization => Empty

/-- Each topic's kind. -/
def kindOf : (c : Workspace.Component) → S.Topic c → TopicKind
  | .acquisition, κ => .acquisition κ
  | .marketModelEngine, _ => .results
  | .warehousing, t => nomatch t
  | .visualization, t => nomatch t

/-- Each one a Kafka topic, named from the series' signature and its kind. -/
def topic : (c : Workspace.Component) → S.Topic c → Kafka.Topic
  | .acquisition, κ => acqTopic N S.signature κ
  | .marketModelEngine, _ => engineTopic N S.signature
  | .warehousing, t => nomatch t
  | .visualization, t => nomatch t

/-- Each topic's name is the naming's, of the series' signature and the topic's kind. -/
theorem topic_name :
    ∀ (c : Workspace.Component) (t : S.Topic c), (S.topic c t).name = N.name S.signature (S.kindOf c t)
  | .acquisition, _ => rfl
  | .marketModelEngine, _ => rfl
  | .warehousing, t => nomatch t
  | .visualization, t => nomatch t

/-- A topic of the working space is known by its kind. -/
theorem kindOf_inj : ∀ (c c' : Workspace.Component) (t : S.Topic c) (t' : S.Topic c'),
    S.kindOf c t = S.kindOf c' t' → (⟨c, t⟩ : Σ c, S.Topic c) = ⟨c', t'⟩
  | .acquisition, .acquisition, _, _, h => by cases h; rfl
  | .acquisition, .marketModelEngine, _, _, h => nomatch h
  | .marketModelEngine, .acquisition, _, _, h => nomatch h
  | .marketModelEngine, .marketModelEngine, t, t', _ => by
      obtain rfl := engineOut_eq S.engine t t'
      rfl
  | .warehousing, _, t, _, _ => nomatch t
  | .visualization, _, t, _, _ => nomatch t
  | _, .warehousing, _, t', _ => nomatch t'
  | _, .visualization, _, t', _ => nomatch t'

/-- No two topics of the working space have the same name: the naming loses no kind. -/
theorem names_distinct (c c' : Workspace.Component) (t : S.Topic c) (t' : S.Topic c')
    (h : (S.topic c t).name = (S.topic c' t').name) : (⟨c, t⟩ : Σ c, S.Topic c) = ⟨c', t'⟩ := by
  rw [S.topic_name, S.topic_name] at h
  exact S.kindOf_inj c c' t t' (N.injective _ _ _ _ h).2

/-- The logs that leave the system: warehousing's pushes, one for each of acquisition's topics, and
visualization's logs, one for the clean topic and one for the engine's. -/
def Output : Workspace.Component → Type
  | .warehousing => Acquisition.Kind
  | .visualization => Unit ⊕ engineOut S.engine
  | .acquisition => Empty
  | .marketModelEngine => Empty

/-- The messages of each of them, of the type of the values of the topic it is from: k-lines for
each of acquisition's topics, results for the engine's. -/
def OutputMsg : (c : Workspace.Component) → S.Output c → Type
  | .warehousing, _ => Market.KLine
  | .visualization, .inl _ => Market.KLine
  | .visualization, .inr _ => MarketModelEngine.Result
  | .acquisition, o => nomatch o
  | .marketModelEngine, o => nomatch o

/-- All the topics. -/
abbrev Topics := ∀ (c : Workspace.Component) (t : S.Topic c), (S.topic c t).Logs

/-- Acquisition's three topics. -/
abbrev AcqTopics := ∀ κ : Acquisition.Kind, (acqTopic N S.signature κ).Logs

/-- The input logs, side by side, as acquisition reads them. -/
def feeds : Process Inputs Acquisition.In :=
  Process.pair (Process.proj (κ := fun i => Log (InputMsg i)) .source)
    (Process.proj (κ := fun i => Log (InputMsg i)) .corrections)

/-- Acquisition: from the inputs to its three topics, each its one partition. -/
def acquisitions : Process Inputs S.AcqTopics :=
  Process.pi fun κ => Process.pi fun _ =>
    Process.proj (κ := fun _ : Acquisition.Kind => Kafka.Partition Market.KLine) κ ⊚
      (S.acquisition.run ⊚ feeds)

/-- Acquisition's topics, from all the topics. -/
def acqPart : Process S.Topics S.AcqTopics :=
  Process.proj (κ := fun c => ∀ t : S.Topic c, (S.topic c t).Logs) .acquisition

/-- The engine's topic, from all the topics: none without the engine. -/
def enginePart :
    Process S.Topics (engineOut S.engine → (engineTopic N S.signature).Logs) :=
  Process.proj (κ := fun c => ∀ t : S.Topic c, (S.topic c t).Logs) .marketModelEngine

/-- The clean topic's one partition, from acquisition's topics. -/
def cleanPart : Process S.AcqTopics (Kafka.Partition Market.KLine) :=
  Process.proj (κ := fun _ : Fin 1 => Kafka.Partition Market.KLine) 0 ⊚
    Process.proj (κ := fun κ => (acqTopic N S.signature κ).Logs) .clean

/-- What the engine writes, from acquisition's topics: nothing without the engine, and with it what
its worker writes from the clean topic. -/
def engineRun :
    (o : Option MarketModelEngine) →
      Process S.AcqTopics (engineOut o → (engineTopic N S.signature).Logs)
  | none => nothing id
  | some e => Process.pi fun _ => Process.pi fun _ => e.worker ⊚ S.cleanPart

/-- What visualization reads: the clean topic's one partition, and the engine's topic's. -/
def visualizationIn : Process S.Topics (Visualization.In (engineOut S.engine)) :=
  Process.pair (S.cleanPart ⊚ S.acqPart)
    (Process.pi fun t =>
      Process.proj (κ := fun _ : Fin 1 => Kafka.Partition MarketModelEngine.Result) 0 ⊚
        (Process.proj (κ := fun _ : engineOut S.engine => (engineTopic N S.signature).Logs) t ⊚
          S.enginePart))

/-- Visualization's logs, one for each topic it reads, as logs that leave the system. -/
def visualizationOut :
    Process (Visualization.Out (engineOut S.engine))
      (∀ o : S.Output .visualization, Log (S.OutputMsg .visualization o)) :=
  Process.pi fun
    | .inl _ => Process.fst
    | .inr t =>
      Process.proj (κ := fun _ : engineOut S.engine => Log MarketModelEngine.Result) t ⊚ Process.snd

/-- Warehousing's pushes, one log for each of acquisition's topics, from its one partition. -/
def pushes : Process S.AcqTopics (∀ o : S.Output .warehousing, Log (S.OutputMsg .warehousing o)) :=
  Process.pi fun κ =>
    Process.proj (κ := fun _ : Fin 1 => Log Market.KLine) 0 ⊚
      (Process.proj (κ := fun _ : Acquisition.Kind => Fin 1 → Log Market.KLine) κ ⊚
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
  table := S.table
  acquisition := Process.pair S.acquisitions (nothing id)
  warehousing := Process.pair (nothing id) (S.pushes ⊚ S.acqPart)
  visualization :=
    Process.pair (nothing id) (S.visualizationOut ⊚ S.visualization.chart ⊚ S.visualizationIn)
  marketModelEngine := Process.pair (S.engineRun S.engine ⊚ S.acqPart) (nothing id)

/-- Acquisition's topics hold what acquisition writes from the inputs alone. -/
theorem acquisition_topics (i : Inputs) :
    S.workspace.topics i .acquisition = S.acquisitions i :=
  S.workspace.acquisition_topics i

/-- The clean topic holds what the publisher makes of the clean series alone: the cleaner on the raw
series, the reader's from the source. -/
theorem clean_topics (i : Inputs) :
    S.workspace.topics i .acquisition .clean (0 : Fin 1) =
      S.acquisition.publishClean (S.acquisition.cleaner (S.acquisition.reader (i .source))) := by
  rw [S.acquisition_topics i]
  rfl

/-- The engine's topic holds what the engine writes from acquisition's topics: nothing without the
engine, and with it what its worker writes from the clean topic. -/
theorem engine_topics (i : Inputs) :
    S.workspace.topics i .marketModelEngine = S.engineRun S.engine (S.acquisitions i) := by
  rw [← S.workspace.topics_eq i .marketModelEngine]
  show S.engineRun S.engine (S.workspace.topics i .acquisition) = _
  rw [S.acquisition_topics i]

/-- Warehousing pushes, for acquisition's topic of kind `κ`, the consumer of its schema, no key and
values of k-lines, on that topic's one partition. -/
theorem warehousing_pushes (i : Inputs) (κ : Acquisition.Kind) :
    (S.workspace.system i).2 .warehousing κ =
      S.warehousing.consumer Empty Market.KLine (S.acquisitions i κ (0 : Fin 1)) := by
  show S.warehousing.consumer _ _ (S.workspace.topics i .acquisition κ (0 : Fin 1)) = _
  rw [S.acquisition_topics i]
  rfl

/-- The table named `name` holds, of the rows from acquisition's topic of kind `κ` pushed into it,
exactly the k-lines the consumer pushes for that topic, in no order. -/
theorem table_rows (i : Inputs) (name : String) (κ : Acquisition.Kind) (h : S.table κ = name)
    (m : Market.KLine) :
    (S.workspace.tableRows name i).has ⟨⟨κ, h⟩, m⟩ ↔
      ∃ n, (S.warehousing.consumer Empty Market.KLine (S.acquisitions i κ (0 : Fin 1))).get n =
        some m := by
  rw [← S.warehousing_pushes i κ]
  exact Iff.rfl

/-- Visualization's logs are what it gives from the clean topic and the engine's, one for each. -/
theorem visualization_chart (i : Inputs) :
    (S.workspace.system i).2 .visualization =
      S.visualizationOut (S.visualization.chart
        (S.acquisitions i .clean (0 : Fin 1),
          fun t => S.engineRun S.engine (S.acquisitions i) t (0 : Fin 1))) := by
  show S.visualizationOut (S.visualization.chart
      (S.workspace.topics i .acquisition .clean (0 : Fin 1),
        fun t => S.workspace.topics i .marketModelEngine t (0 : Fin 1))) = _
  rw [S.acquisition_topics i, S.engine_topics i]

/-- Without the engine, visualization's logs are given from the clean topic alone: they are the same
whatever stands for the engine's topic, of which there is none. -/
theorem chart_without_engine (h : S.engine = none) (i : Inputs)
    (x : engineOut S.engine → Kafka.Partition MarketModelEngine.Result) :
    (S.workspace.system i).2 .visualization =
      S.visualizationOut (S.visualization.chart (S.acquisitions i .clean (0 : Fin 1), x)) := by
  have empty : engineOut S.engine → False := by
    rw [h]
    exact fun t => nomatch t
  rw [S.visualization_chart i]
  congr 3
  funext t
  exact (empty t).elim

end Wiring

/-- Several working spaces side by side, each one a wiring makes, of the one naming `N`, one for each
acquisition. Each topic has one writer and each table of the database one working space: no two
topics of any of them have the same name (`Workspaces.topics_distinct`), and no table is written by
two of them. -/
structure Workspaces (N : Naming) (ι : Type) where
  /-- the wirings, each making one working space -/
  space : ι → Wiring N
  /-- no two working spaces of one signature -/
  signatures_distinct : ∀ i j : ι, (space i).signature = (space j).signature → i = j
  /-- no table is written by two working spaces: for working spaces `i` and `j`, a topic of kind `κ`
  of `i`'s acquisition and one of kind `κ'` of `j`'s, pushed into one table, `i` and `j` are one -/
  tables_distinct :
    ∀ (i j : ι) (κ κ' : Acquisition.Kind), (space i).table κ = (space j).table κ' → i = j

namespace Workspaces

variable {N : Naming} {ι : Type} (S : Workspaces N ι)

/-- No two topics, of one working space or of two, have the same name: the naming loses neither the
signature nor the kind, and no two working spaces have one signature. -/
theorem topics_distinct (i j : ι) (c c' : Workspace.Component) (t : (S.space i).Topic c)
    (t' : (S.space j).Topic c') (h : ((S.space i).topic c t).name = ((S.space j).topic c' t').name) :
    (⟨i, c, t⟩ : Σ i, Σ c, (S.space i).Topic c) = ⟨j, c', t'⟩ := by
  rw [Wiring.topic_name, Wiring.topic_name] at h
  obtain ⟨hs, hk⟩ := N.injective _ _ _ _ h
  obtain rfl := S.signatures_distinct i j hs
  rw [(S.space i).kindOf_inj c c' t t' hk]

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
