import Kahn
import Kafka
import Contract.Market
import Contract.Chanlun

/-!
# The market model engine

Optional. A worker: it reads one clean topic, of market's `KLine`, its series, and publishes one
topic of its own, of its results (`Result`), each one of chanlun's records
(`lean/Contract/Chanlun.lean`). Each topic has one partition and no key (`Kafka.Topic.ofName`), so
the worker reads one log and writes one log (`Kafka.Partition`): it merges none. How it computes its
results is the implementation's.
-/

noncomputable section

open Kahn

/-- A result of the engine, of which its topic's values are: one of chanlun's six records, which one said
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

/-- A result keeps its rules: its record keeps chanlun's contract. -/
def MarketModelEngine.Result.Keeps : MarketModelEngine.Result → Prop
  | .mergedBar r => r.Keeps
  | .fractal r => r.Keeps
  | .line r => r.Keeps
  | .segment r => r.Keeps
  | .move r => r.Keeps
  | .consolidation r => r.Keeps

/-- The market model engine. -/
structure MarketModelEngine where
  /-- the worker: reads the clean topic's one partition, its series, and writes its own topic's -/
  worker : Process (Kafka.Partition Market.KLine) (Kafka.Partition MarketModelEngine.Result)

end
