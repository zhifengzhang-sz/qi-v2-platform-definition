import Kahn

/-!
# Kafka's topic

Every topic has the same shape, Kafka's. A topic is seen as its log: everything ever appended to it.
What retention or compaction leave readable is a view of that log, not the log itself: no
process gives that view (`compaction_not_process`).

Taken as given, like replication and brokers: how records travel and are stored (batches,
compression, transactions, producer ids). A record's position in its log stands for its offset:
Kafka's offsets can skip numbers, but their order is the same. Which partition a record goes to is
the writer's choice, not the topic's.
-/

namespace Kafka

open Kahn

/-- A record, as Kafka gives it to a reader: a key and a value, either of which may be absent, a
timestamp, and headers. Its partition and offset are where it is: which log, and which position in
it. -/
structure Record (K V : Type) where
  key : Option K
  value : Option V
  timestamp : Int
  headers : List (String × Option ByteArray)

/-- A topic: its name, its number of partitions (at least one), and the types of its keys and values,
which its schema fixes. -/
structure Topic where
  name : String
  partitions : Nat
  /-- a topic has at least one partition -/
  partitions_pos : 0 < partitions
  Key : Type
  Value : Type

/-- What a topic holds: one log of records for each partition. Kafka keeps order within a partition
only. -/
abbrev Topic.Logs (t : Topic) := Fin t.partitions → Log (Record t.Key t.Value)

/-- No view that replaces a record already given is a process of the log. Compaction is one: for two
records `r₁`, `r₂` of the same key it leaves `r₁` from the log `r₁`, and only `r₂` from the log
`r₁ r₂`. Retention is another: dropping the oldest record moves what is at position 0. The theorem:
no process gives `r₁` at position 0 for `r₁` and `r₂` at position 0 for `r₁ r₂`. That is why a topic
here is the whole log, and what compaction or retention leave is a view of it. -/
theorem compaction_not_process {R : Type} {r₁ r₂ : R} (h : r₁ ≠ r₂) (g : Process (Log R) (Log R))
    (h₁ : (g (Log.ofList [r₁])).get 0 = some r₁)
    (h₂ : (g (Log.ofList [r₁, r₂])).get 0 = some r₂) : False := by
  have hle : Log.ofList [r₁] ≤ Log.ofList [r₁, r₂] := by
    intro n a ha
    cases n with
    | zero => exact ha
    | succ n => simp [Log.ofList] at ha
  have := g.mono hle 0 r₁ h₁
  rw [h₂] at this
  exact h (Option.some.inj this).symm

end Kafka
