import Kahn
import Kafka

/-!
# The market model engine

Optional. A worker: it reads the clean k-line topics and publishes topics of its own. What their
messages are is left open: each topic's key and value types, which its schema fixes (`Kafka.Topic`).

The worker is a process of the topics it reads. Reading several topics or partitions into one log,
as their records arrive, would be a merge by arrival, which is not a process
(`Kahn.no_arrival_merge`). How the worker combines them is the implementation's.
-/

noncomputable section

open Kahn

/-- The kinds of data the engine works on. -/
structure MarketModelEngine.Data where
  /-- the clean k-line topics the engine reads -/
  In : Type
  /-- each one a Kafka topic -/
  inTopic : In → Kafka.Topic
  /-- the topics the engine publishes; what their messages are is left open -/
  Out : Type
  /-- each one a Kafka topic -/
  outTopic : Out → Kafka.Topic

/-- The market model engine. -/
structure MarketModelEngine (D : MarketModelEngine.Data) where
  /-- the worker: reads the clean k-line topics, publishes the engine's topics -/
  worker : Process (∀ t : D.In, (D.inTopic t).Logs) (∀ t : D.Out, (D.outTopic t).Logs)

end
