import Kahn
import Kafka

/-!
# The working space

The system on Kahn's base: four components, acquisition, warehousing, visualization and the market
model engine (optional), wired by the topics. This file says that much, and what a table of the
database holds. What each component reads, writes and does is defined in its own project.

Acquisition is the one component that reads the system's input logs (the vendor's); the others read
the topics, and nothing else. Each writes topics of its own, and logs that leave the system (what
warehousing pushes into the database, what visualization shows). Each topic has one writer and any
number of readers; no two topics have the same name. Two writers into one log would merge by
arrival, which is not a Kahn process (`Kahn.no_arrival_merge`). Only warehousing writes into the
database.

A table of the database is a set of rows: it holds the rows of every log warehousing pushes into
it, in no order (`Workspace.tableRows`). Several logs into one table is a process
(`Kahn.Rows.ofLogs`), where two logs into one log, in the order their messages arrive, is not
(`Kahn.no_arrival_merge`): a set of rows does not say which came first. That a table is a set of
rows is a modelling choice, not a theorem, and so is what a row is: a message marked with the log
it is from, so that a message one log pushes twice is one row, and a message two logs push is two.

A working space has one acquisition. Several working spaces may work side by side, one for each
acquisition (`Workspaces`): each topic still has one writer, so no two topics of any of them have
the same name, and each table has one working space, so no table is written by two of them. A
topic's reason is its logs: two writers into one log would merge by arrival. A table keeps no
order and has no such reason: one working space to a table is a modelling choice, by which what a
table holds is defined within one working space.
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

/-- The logs warehousing pushes into the table named `name`. -/
abbrev TableLog (name : String) := { o : W.Output .warehousing // W.table o = name }

/-- What a row of the table named `name` can be: a message of one of the logs pushed into it,
marked with that log. Which rows the table holds is `tableRows`. -/
abbrev TableRow (name : String) := Σ o : W.TableLog name, W.OutputMsg .warehousing o.1

/-- What the table named `name` holds, from the logs that leave the system: the rows of every log
pushed into it, in no order. -/
def tableOf (name : String) : Process W.Outputs (Rows (W.TableRow name)) :=
  Rows.ofLogs ⊚ Process.pi fun o : W.TableLog name =>
    Process.proj (κ := fun o => Log (W.OutputMsg .warehousing o)) o.1 ⊚
      Process.proj (κ := fun c => ∀ o : W.Output c, Log (W.OutputMsg c o)) .warehousing

/-- The table named `name`, as one process of the input logs. -/
def tableRows (name : String) : Process W.Inputs (Rows (W.TableRow name)) :=
  W.tableOf name ⊚ Process.snd ⊚ W.system

/-- A table holds a row exactly when the log it is from holds its message, at some position. -/
theorem has_tableRows (i : W.Inputs) (name : String) (o : W.TableLog name)
    (m : W.OutputMsg .warehousing o.1) :
    (W.tableRows name i).has ⟨o, m⟩ ↔ ∃ n, ((W.system i).2 .warehousing o.1).get n = some m :=
  Iff.rfl

end Workspace

/-- Several working spaces side by side, one for each acquisition. Each topic has one writer and
each table of the database one working space: no two topics of any of them have the same name, and
no table is written by two of them. -/
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
