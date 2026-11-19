import Kahn
import Kafka
import Contract.Market
import Contract.Chanlun

/-!
# The market model engine

Optional. A worker: it reads the clean k-line topics, of market's `KLine`, and publishes topics of
its own, of its results (`Result`), each one of chanlun's records (`lean/Contract/Chanlun.lean`). Each topic is made with no key (`Kafka.TopicOf`).

The worker is a process of the topics it reads. Reading several topics or partitions into one log,
as their records arrive, would be a merge by arrival, which is not a process
(`Kahn.no_arrival_merge`). How the worker combines them is the implementation's.
-/

noncomputable section

open Kahn

/-- A result of the engine, of which its topics' values are: one of chanlun's six records, which one said
by its case. It is the platform's message, made of the chanlun contract's records, not the
contract's. -/
inductive MarketModelEngine.Result where
  /-- 包含's merged bar -/
  | mergedBar (r : Chanlun.MergedBar)
  /-- a 分型 -/
  | fractal (r : Chanlun.Fractal)
  /-- a line, a 笔 -/
  | line (r : Chanlun.Line)
  /-- a 线段 -/
  | segment (r : Chanlun.Segment)
  /-- a 走势 -/
  | move (r : Chanlun.Move)
  /-- a 中枢 -/
  | consolidation (r : Chanlun.Consolidation)

/-- The topics the engine reads and writes. -/
structure MarketModelEngine.Data where
  /-- the clean k-line topics the engine reads -/
  In : Type
  /-- each one a Kafka topic of k-lines, with no key -/
  inTopic : In → Kafka.TopicOf Market.KLine
  /-- the topics the engine publishes -/
  Out : Type
  /-- each one a Kafka topic of its results, with no key -/
  outTopic : Out → Kafka.TopicOf MarketModelEngine.Result

/-- The market model engine. -/
structure MarketModelEngine (D : MarketModelEngine.Data) where
  /-- the worker: reads the clean k-line topics, publishes the engine's topics -/
  worker :
    Process (∀ t : D.In, (D.inTopic t).toTopic.Logs) (∀ t : D.Out, (D.outTopic t).toTopic.Logs)

end
