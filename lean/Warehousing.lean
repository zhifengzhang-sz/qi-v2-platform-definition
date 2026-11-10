import Kahn
import Kafka

/-!
# Warehousing

The warehouse consumer takes the topic schema, reads the data and pushes to the db based on the topic
schema. Cleaning happens in acquisition, not in warehousing: the consumer is given by the schema
alone. What it pushes is left open.

The consumer reads one partition at a time. Reading all of a topic's partitions into one log, as
their records arrive, would be a merge by arrival, which is not a process (`Kahn.no_arrival_merge`).
-/

noncomputable section

open Kahn

/-- The kinds of data warehousing works on. -/
structure Warehousing.Data where
  /-- the topics warehousing reads -/
  Topic : Type
  /-- each one a Kafka topic -/
  topic : Topic → Kafka.Topic
  /-- what the consumer pushes into the database for a topic whose schema gives keys `K` and values
  `V`: left open -/
  Push : (K V : Type) → Type

namespace Warehousing

variable (D : Data)

/-- The topics warehousing reads. -/
abbrev Topics := ∀ t : D.Topic, (D.topic t).Logs

/-- What warehousing pushes into the database: for each topic, one log for each partition. -/
abbrev Pushes :=
  ∀ t : D.Topic, Fin (D.topic t).partitions → Log (D.Push (D.topic t).Key (D.topic t).Value)

end Warehousing

/-- Warehousing. -/
structure Warehousing (D : Warehousing.Data) where
  /-- the warehouse consumer: one for each schema, the same for every topic and partition of it -/
  consumer : (K V : Type) → Process (Log (Kafka.Record K V)) (Log (D.Push K V))

namespace Warehousing

variable {D : Data}

/-- Warehousing as one process: the consumer of each topic's schema, on every partition of it. -/
def run (w : Warehousing D) : Process (Topics D) (Pushes D) :=
  Process.pi fun t => Process.pi fun p =>
    w.consumer (D.topic t).Key (D.topic t).Value ⊚
      (Process.proj (κ := fun _ : Fin (D.topic t).partitions =>
          Log (Kafka.Record (D.topic t).Key (D.topic t).Value)) p ⊚
        Process.proj (κ := fun t => (D.topic t).Logs) t)

/-- What `run` comes to: partition `p` of topic `t` goes through the consumer of `t`'s schema. -/
theorem run_apply (w : Warehousing D) (x : Topics D) (t : D.Topic)
    (p : Fin (D.topic t).partitions) :
    w.run x t p = w.consumer (D.topic t).Key (D.topic t).Value (x t p) :=
  rfl

end Warehousing

end
