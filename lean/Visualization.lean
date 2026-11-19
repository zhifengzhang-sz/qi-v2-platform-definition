import Kahn
import Kafka
import Contract.Market
import MarketModelEngine

/-!
# Visualization

A pure consumer: it reads only from Kafka, one clean topic, of market's `KLine`, and, when the market
model engine is there, the engine's topic, of its results (`MarketModelEngine.Result`). It gives
nothing in the Kafka sense: it displays the chart in the HTML page. Its output, which leaves the
system, is one log for each topic it reads, of the type of that topic's values; the chart on the
page at any moment is drawn from what its logs hold so far, how being the page's.

The engine's topics it reads are those of `Model`, of which there is at most one (`Subsingleton`):
one in a working space with the engine, none without it. Each topic has one partition (`Kafka.Topic.ofName`). Putting the records of two of them
into one log as they arrive would be a merge by arrival, which is not a process
(`Kahn.no_arrival_merge`): it gives a log for each topic it reads.
-/

noncomputable section

open Kahn

namespace Visualization

variable (Model : Type)

/-- What visualization reads: the clean topic's one partition, and each of the engine's topics'. -/
abbrev In := Kafka.Partition Market.KLine × (Model → Kafka.Partition MarketModelEngine.Result)

/-- What visualization gives: one log for each topic it reads, of the type of that topic's values:
k-lines for the clean topic, results for each of the engine's. -/
abbrev Out := Log Market.KLine × (Model → Log MarketModelEngine.Result)

end Visualization

/-- Visualization, reading the engine's topic of `Model`, if there is one. -/
structure Visualization (Model : Type) [Subsingleton Model] where
  /-- from the topics it reads to its logs, one for each of them -/
  chart : Process (Visualization.In Model) (Visualization.Out Model)

end
