import Kahn
import Kafka

/-!
# The market model engine

Optional. A worker: it reads the clean k-line topics and publishes topics of its own, whose messages
derive from the chanlun contract 3.1.0.

Reading several topics or partitions is a process only if the worker combines them by content (for
example by bar time), not by arrival (`Kahn.no_arrival_merge`).
-/

noncomputable section

open Kahn

/-- The kinds of data the engine works on. -/
structure MarketModelEngine.Data where
  /-- the clean k-line topics the engine reads -/
  In : Type
  /-- each one a Kafka topic -/
  inTopic : In → Kafka.Topic
  /-- the topics the engine publishes; their messages derive from the chanlun contract 3.1.0 -/
  Out : Type
  /-- each one a Kafka topic -/
  outTopic : Out → Kafka.Topic

/-- The market model engine. -/
structure MarketModelEngine (D : MarketModelEngine.Data) where
  /-- the worker: reads the clean k-line topics, publishes the engine's topics -/
  worker : Process (∀ t : D.In, (D.inTopic t).Logs) (∀ t : D.Out, (D.outTopic t).Logs)

end
