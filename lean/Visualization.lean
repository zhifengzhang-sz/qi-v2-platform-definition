import Kahn
import Kafka

/-!
# Visualization

A pure consumer: it reads only from Kafka, the clean topics and, when the market model engine is
there, the engine's topics. It gives nothing in the Kafka sense: it displays the chart in the HTML
page. That display is its output, a log of chart updates that leaves the system; the chart on the
page at any moment is what the updates so far make.

Reading several topics into one log of updates is a process only if it combines them by content
(for example by bar time, waiting until every topic has passed it), not by arrival
(`Kahn.no_arrival_merge`).
-/

noncomputable section

open Kahn

/-- The kinds of data visualization works on. -/
structure Visualization.Data where
  /-- the clean topics visualization reads -/
  Clean : Type
  /-- each one a Kafka topic -/
  cleanTopic : Clean → Kafka.Topic
  /-- the market model engine's topics it reads, when the engine is there; none without it -/
  Model : Type
  /-- each one a Kafka topic -/
  modelTopic : Model → Kafka.Topic
  /-- one update of the chart in the HTML page: left open -/
  View : Type

namespace Visualization

variable (D : Data)

/-- What visualization reads: the clean topics, and the engine's topics. -/
abbrev In := (∀ t : D.Clean, (D.cleanTopic t).Logs) × (∀ t : D.Model, (D.modelTopic t).Logs)

end Visualization

/-- Visualization. -/
structure Visualization (D : Visualization.Data) where
  /-- from the topics it reads to the updates of the chart -/
  chart : Process (Visualization.In D) (Log D.View)

end
