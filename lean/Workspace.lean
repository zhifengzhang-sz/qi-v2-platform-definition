import Kahn
import Kafka

/-!
# The working space

The system on Kahn's base: four components, acquisition, warehousing, visualization and the market
model engine (optional), wired by the topics. This file says only that much. What each component
reads, writes and does is defined in its own project.

Acquisition is the one component that reads the system's input logs (the vendor's); the others read
the topics, and nothing else. Each writes topics of its own, and logs that leave the system (what
warehousing pushes into the database, what visualization shows). Each topic has one writer and any
number of readers; no two topics have the same name. Two writers into one log would merge by
arrival, which is not a Kahn process (`Kahn.no_arrival_merge`). Only warehousing writes into the
database.

A working space has one acquisition. Several working spaces may work side by side, one for each
acquisition (`Workspaces`): each topic and each table of the database still has one writer, so no two
topics of any of them have the same name, and no table is written by two of them.
-/

noncomputable section

open Kahn

/-- The four components. -/
inductive Workspace.Component where
  | acquisition
  | warehousing
  | visualization
  | marketModelEngine

/-- The working space. The market model engine is optional: without it, it writes no topics and no
logs. -/
structure Workspace where
  /-- the input logs: what the system reads from outside it -/
  Input : Type
  /-- the messages of input log `i` -/
  InputMsg : Input → Type
  /-- the topics component `c` writes -/
  Topic : Workspace.Component → Type
  /-- each one a Kafka topic -/
  topic : (c : Workspace.Component) → Topic c → Kafka.Topic
  /-- one writer for each Kafka topic, and any number of readers: no two topics, of one component or
  of two, have the same name -/
  names_distinct : ∀ (c c' : Workspace.Component) (t : Topic c) (t' : Topic c'),
    (topic c t).name = (topic c' t').name → (⟨c, t⟩ : Σ c, Topic c) = ⟨c', t'⟩
  /-- the logs component `c` writes that leave the system -/
  Output : Workspace.Component → Type
  /-- the messages of log `o` of component `c` -/
  OutputMsg : (c : Workspace.Component) → Output c → Type
  /-- the table of the database each of warehousing's logs is pushed into. Only warehousing writes into
  the database. -/
  table : Output .warehousing → String
  /-- acquisition: from the input logs alone, to its topics and its logs -/
  acquisition :
    Process (∀ i : Input, Log (InputMsg i))
      ((∀ t : Topic .acquisition, (topic .acquisition t).Logs) ×
        (∀ o : Output .acquisition, Log (OutputMsg .acquisition o)))
  /-- warehousing: from the topics alone, to its topics and its logs -/
  warehousing :
    Process (∀ (d : Workspace.Component) (t : Topic d), (topic d t).Logs)
      ((∀ t : Topic .warehousing, (topic .warehousing t).Logs) ×
        (∀ o : Output .warehousing, Log (OutputMsg .warehousing o)))
  /-- visualization: from the topics alone, to its topics and its logs -/
  visualization :
    Process (∀ (d : Workspace.Component) (t : Topic d), (topic d t).Logs)
      ((∀ t : Topic .visualization, (topic .visualization t).Logs) ×
        (∀ o : Output .visualization, Log (OutputMsg .visualization o)))
  /-- the market model engine: from the topics alone, to its topics and its logs -/
  marketModelEngine :
    Process (∀ (d : Workspace.Component) (t : Topic d), (topic d t).Logs)
      ((∀ t : Topic .marketModelEngine, (topic .marketModelEngine t).Logs) ×
        (∀ o : Output .marketModelEngine, Log (OutputMsg .marketModelEngine o)))

namespace Workspace

variable (W : Workspace)

/-- The input logs. -/
abbrev Inputs := ∀ i : W.Input, Log (W.InputMsg i)

/-- All the topics. -/
abbrev Topics := ∀ (c : Component) (t : W.Topic c), (W.topic c t).Logs

/-- All the logs that leave the system. -/
abbrev Outputs := ∀ (c : Component) (o : W.Output c), Log (W.OutputMsg c o)

/-- What component `c` writes: its topics and its logs. -/
abbrev Own (c : Component) := (∀ t : W.Topic c, (W.topic c t).Logs) × (∀ o : W.Output c, Log (W.OutputMsg c o))

/-- Each component, from the inputs and the topics: acquisition reads the inputs alone, the others
the topics alone. -/
def run : (c : Component) → Process (W.Inputs × W.Topics) (W.Own c)
  | .acquisition => W.acquisition ⊚ Process.fst
  | .warehousing => W.warehousing ⊚ Process.snd
  | .visualization => W.visualization ⊚ Process.snd
  | .marketModelEngine => W.marketModelEngine ⊚ Process.snd

/-- The working space as a Kahn network: the topics are its wires. Each component's topics are what
it writes; the system gives the topics and the logs that leave it. -/
def network : Network W.Inputs W.Topics (W.Topics × W.Outputs) where
  wires := Process.pi fun c => Process.fst ⊚ W.run c
  out := Process.pair Process.snd (Process.pi fun c => Process.snd ⊚ W.run c)

/-- The system: one process from the input logs to the topics and the logs that leave it. -/
def system : Process W.Inputs (W.Topics × W.Outputs) :=
  W.network.denote

/-- The topics, as one process of the input logs. -/
def topics : Process W.Inputs W.Topics :=
  solve W.network.wires

/-- What the system gives: the topics, and what each component writes from the inputs and them. -/
theorem system_apply (i : W.Inputs) :
    W.system i = (W.topics i, fun c => (W.run c (i, W.topics i)).2) :=
  rfl

/-- Each component's topics hold what the component writes. -/
theorem topics_eq (i : W.Inputs) (c : Component) : (W.run c (i, W.topics i)).1 = W.topics i c :=
  congrFun (solve_eq W.network.wires i) c

/-- And nothing more: any topics that hold at least what the components write hold the system's. -/
theorem topics_least (i : W.Inputs) (t : W.Topics) (h : ∀ c, (W.run c (i, t)).1 ≤ t c) :
    W.topics i ≤ t :=
  solve_least W.network.wires i h

/-- Acquisition's topics hold what acquisition writes from the input logs alone. -/
theorem acquisition_topics (i : W.Inputs) : W.topics i .acquisition = (W.acquisition i).1 :=
  (W.topics_eq i .acquisition).symm

end Workspace

/-- Several working spaces side by side, one for each acquisition. Each topic and each table of the
database has one writer: no two topics of any of them have the same name, and no table is written by
two of them. -/
structure Workspaces (ι : Type) where
  /-- the working spaces -/
  space : ι → Workspace
  /-- no two topics, of one working space or of two, have the same name -/
  topics_distinct : ∀ (i j : ι) (c c' : Workspace.Component) (t : (space i).Topic c)
      (t' : (space j).Topic c'),
    ((space i).topic c t).name = ((space j).topic c' t').name →
      (⟨i, c, t⟩ : Σ i, Σ c, (space i).Topic c) = ⟨j, c', t'⟩
  /-- no table is written by two working spaces -/
  tables_distinct : ∀ (i j : ι) (o : (space i).Output .warehousing) (o' : (space j).Output .warehousing),
    (space i).table o = (space j).table o' → i = j

namespace Workspaces

variable {ι : Type} (S : Workspaces ι)

/-- The working spaces as one process: each one's system, on its own input logs. -/
def system : Process (∀ i, (S.space i).Inputs) (∀ i, (S.space i).Topics × (S.space i).Outputs) :=
  Process.pi fun i => (S.space i).system ⊚ Process.proj (κ := fun i => (S.space i).Inputs) i

/-- What each working space gives depends on its own input logs alone. -/
theorem system_apply (x : ∀ i, (S.space i).Inputs) (i : ι) : S.system x i = (S.space i).system (x i) :=
  rfl

end Workspaces

end
