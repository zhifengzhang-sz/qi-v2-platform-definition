import Kahn
import Kafka
import Contract.Market
import MarketModelEngine

/-!
# Visualization

A pure consumer: it reads only from Kafka, the clean topics, of market's `KLine`, and, when the market
model engine is there, the engine's topics, of its results (`MarketModelEngine.Result`). It gives
nothing in the Kafka sense: it displays the chart in the HTML page. Its output, which leaves the
system, is one log for each partition of each topic it reads, of the type of that topic's values;
the chart on the page at any moment is drawn from what its logs hold so far, how being the page's.

Visualization is a process of the topics it reads (`chart`). Putting the records of several of them
into one log as they arrive would be a merge by arrival, which is not a process
(`Kahn.no_arrival_merge`): it gives a log for each partition it reads.
-/

noncomputable section

open Kahn

/-- The topics visualization reads. -/
structure Visualization.Data where
  /-- the clean topics visualization reads -/
  Clean : Type
  /-- each one a Kafka topic of k-lines, with no key -/
  cleanTopic : Clean → Kafka.TopicOf Market.KLine
  /-- the market model engine's topics it reads, when the engine is there; none without it -/
  Model : Type
  /-- each one a Kafka topic of the engine's results, with no key -/
  modelTopic : Model → Kafka.TopicOf MarketModelEngine.Result

namespace Visualization

variable (D : Data)

/-- What visualization reads: the clean topics, and the engine's topics. -/
abbrev In := (∀ t : D.Clean, (D.cleanTopic t).toTopic.Logs) × (∀ t : D.Model, (D.modelTopic t).toTopic.Logs)

/-- What visualization gives: one log for each partition of each topic it reads, of the type of that
topic's values: k-lines for a clean topic, results for one of the engine's. -/
abbrev Out :=
  (∀ t : D.Clean, Fin (D.cleanTopic t).partitions → Log Market.KLine) ×
    (∀ t : D.Model, Fin (D.modelTopic t).partitions → Log MarketModelEngine.Result)

end Visualization

/-- Visualization. -/
structure Visualization (D : Visualization.Data) where
  /-- from the topics it reads to its logs, one for each partition of each of them -/
  chart : Process (Visualization.In D) (Visualization.Out D)

end
