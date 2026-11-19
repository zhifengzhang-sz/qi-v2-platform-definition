# The contract specs and the component specs

The definition has two parts (`docs/decisions.md`): the contract specs, the formal definition of each contract, its records and its rules; and the component specs, each component's objectives, requirements and features. This design says what the definition holds of each contract, which record fixes each data type the definition left open, what each component must do, and what the design it replaces guaranteed, kept or lost. What in it is not yet decided is under Open in `docs/decisions.md`. The Lean follows in two steps: first the contract specs, `lean/Contract/Market.lean` and `lean/Contract/Chanlun.lean`, with the components taking their records; then the component specs.

## What this design guarantees

- Every message of a working space the wiring makes is a contract's record, or made of them: its input logs and acquisition's topics carry market's `KLine`, the engine's one topic its results, each one of chanlun's records, and what leaves the system is the values of the records read. No data type of a component is a parameter; what stays open is the topics' partitions and the form of a topic's name.
- A working space is one series, of one signature: the security, the market, the exchange, the source and the k-line's period. Acquisition has one topic of each kind and the engine one, its series' chanlun results; each is known by the signature, which its name carries, with its kind.
- Each component meets its spec, a structure of `Prop`s on its processes, one for each requirement. A component that gives nothing meets no spec: on some input it gives less than its spec asks, for the engine and the cleaner an input holding a k-line that keeps market's rules (a theorem for each component).
- Each spec is met by some component (a theorem for each), so no spec contradicts itself or Kahn's condition.
- Each series acquisition publishes is read back, in order, from one partition of its topic, its home; each k-line of the raw, the clean and the corrections series holds its place in its series as its `index`. The engine's results are read back from its topic's home in the order its worker gives them. Both rest on the system's facts of order (Order, below).
- Several working spaces side by side are each one a wiring makes, of one naming, no two of one signature, so that no two of their topics have one name (a theorem).
- What the replaced design guaranteed is kept, but for what is listed under What is lost (both below).

## Order

The system takes three facts of order as given, its axioms. None is a Lean `axiom`: the definition rests on Lean's three alone. Each stands in the definition so:
- The worker's library gives its results in the right order. That order is the library's, as whether its records are right by 缠论's lessons is: no contract states it, and the definition requires no order of the worker's results among themselves.
- The engine's publisher writes the worker's results, in the order the worker gives them, to one partition of its topic, its home: a requirement of the engine (`publish`, The market model engine).
- Kafka keeps the order of what is written to one partition: `lean/Kafka.lean` takes each partition as one log, a record's position in it standing for its offset.

The guarantees above, and the wiring's theorems (The working space), verified against them:

| Guarantee | What it rests on |
|---|---|
| Every message is a contract's record, or made of them | the types alone |
| A working space is one series; each topic is known by its signature | acquisition's one signature, its one topic of each kind and the engine's one topic; that each topic is known by the signature, the naming, which loses neither the signature nor the kind |
| Each component meets its spec; one that gives nothing meets no spec; each spec is met by some component | the requirements, the engine's `publish` among them, and no other fact of order |
| A series is read back in order from its home, each k-line's `index` its place | Kafka's order within a partition; acquisition's publishers, which write each series whole and in order to its home (`publishRaw`, `publishClean`, `publishCorrections`, requirements as the engine's `publish` is); the reader, which keeps the source's order, and the cleaner, which keeps the raw series' |
| The engine's results are read back in the order its worker gives them | Kafka's order within a partition, and the engine's publisher; that this order is right, the worker's library |
| The wiring's theorems: the engine's results are of its series in order, and each of the chart's logs is of a partition in order | Kafka's order within the clean home and within each partition read, and acquisition's publisher of the clean series |
| The wiring's theorems: a table holds every record of its topics | no fact of order: a table is a set of rows |
| No two topics of the working spaces side by side have one name | the one naming, and no two working spaces of one signature |
| What the replaced design guaranteed, but what is lost | the sources its table below names; of order, Kafka's within a partition alone |

## The contract specs

### What the definition holds of a contract

A contract is its records and its rules. A record is a structure, field for field the message of the contract's `.proto`. A rule is a name and what holds of a record that keeps it (`Rule`: `name`, `holds`, and `dec`, that `holds` is decidable); `broken rules x` gives the names of the rules of `rules` that `x` breaks, in their order. Each rule is of one record alone.

The records and rules the definition holds are those the tables below give, as the contract's Lean states them, in name and meaning unchanged; the commit that moves them names the releases they are read from. Each contract is a module of its own, in its own namespace: `Contract.Market` (`lean/Contract/Market.lean`, namespace `Market`) and `Contract.Chanlun` (`lean/Contract/Chanlun.lean`, namespace `Chanlun`), so that a contract's own module of its name, which keeps its reader, imports the definition's with no clash of names. They import nothing: the contract's Lean imports `Lean.Data.Json` for its reader alone. Each keeps its own `Rule` and `broken`, as the two contracts state them, so that a contract takes its records and rules by the names it has.

A field of type `Nat` holds a uint64. A value with a field past 2⁶⁴ − 1 is no record on the wire, which the contract's reader refuses; the definition, like the contract's Lean, holds that bound in the reader alone. That no field of a record the platform writes passes 2⁶⁴ − 1 is a modelling choice, not a theorem: a series' `index` reaches 2⁶⁴ only after 2⁶⁴ k-lines (Open).

`broken` and each rule's decision are computable, as the contracts state them, so that the contracts' program that checks their examples evaluates them. That program is the contracts' code; the definition's Lean is checked by its proofs.

What stays the contracts' project's (`qi-v2-contracts`): the `.proto`, the wire's form; the reader of Protobuf's JSON (`ProtoJson`, the `FromJson` instances), which is code to run; the examples and the program that checks them against the rules; Go and TypeScript. On the wire a record crosses as Protobuf, read and written by code generated from the `.proto` with a standard library, and a message is its shape alone: the rules are applied within the workers that use them, which is what the component specs say. The contracts take the records and rules from the definition at a release.

### Market

The K-line and the ongoing K-line, of whatever source gives them. A time is milliseconds since 1970-01-01 00:00:00 UTC (`date`, `asOf`); a position is a K-line's place in its series, from 0 (`index`); a price or a volume needs no more than 6 decimal places, and more is not refused.

| Record | Fields | Rules |
|---|---|---|
| `KLine`, a complete bar | `index`, `date` : `Nat`; `open`, `high`, `low`, `close`, `volume` : `Float` | `finite`: every price and the volume a finite number; `range`: `low ≤ open`, `low ≤ close`, `open ≤ high`, `close ≤ high`; `volumeNotNegative`: `0 ≤ volume` |
| `OngoingKLine`, a bar still going on | `KLine`'s, and `asOf` : `Nat`, when its values were last updated | its K-line's three, on `OngoingKLine.kline`, its fields as a K-line's; `asOfNotBeforeDate`: `date ≤ asOf` |

### Chanlun

The records the algorithm of 缠论 makes beyond the K-line. The contract says what a value is, not whether it is right by the lessons, and not how records are gathered: a run of them, their order, and which is still going on are their user's. A position is a K-line's place in its series, market's `KLine.index`; a bar is a merged bar's number, its `mIndex`, from 0; a price is as market's; a level is from 0. A `confirmEnd` not set means the record is still going on.

| Record | Fields | Rules |
|---|---|---|
| `MergedBar`, 包含's merged bar | `mIndex` : `Nat`, a bar; `up` : `Bool`; `start`, `end` : `Nat`, `confirmEnd` : `Option Nat`, `extremes` : `List Nat`, `index` : `Nat`, positions; `high`, `low` : `Float` | `finite`: its high and its low finite; `range`: `low ≤ high`; `extremesWithin`: each extreme from `start` to `end`; `extremesAscending`: its extremes ascending, none twice; `indexInExtremes`: `index` one of its extremes; `endBeforeConfirmEnd`: `end < confirmEnd` when it is set |
| `Fractal`, 分型 | `mIndex` : `Nat`, a bar | none |
| `Line`, a 笔 | `start`, `end` : `Nat`, `confirmEnd` : `Option Nat`, bars | `startBeforeEnd`: `start < end`; `endBeforeConfirmEnd` |
| `Segment`, 线段 of a level | `Line`'s, and `level` : `Nat` | `startBeforeEnd`; `endBeforeConfirmEnd` |
| `Move`, 走势 of a level | `Line`'s, and `level` : `Nat` | `startBeforeEnd`; `endBeforeConfirmEnd` |
| `Consolidation`, 中枢 of a level | `level` : `Nat`; `start`, `end` : `Nat`, `confirmEnd` : `Option Nat`, bars; `zg`, `zd`, `gg`, `dd` : `Float` | `finite`: its four prices finite; `startBeforeEnd`; `bands`: `dd ≤ zd ≤ zg ≤ gg`; `endBeforeConfirmEnd` |

A merged bar's `start` not after its `end` is no rule: it is a theorem, `MergedBar.startNotAfterEnd`, from `indexInExtremes` and `extremesWithin`.

## The data the definition left open

Of the 87 parts of the export at 0.2.0, 23 are types (`Type`, or a family of them). Eleven of them are data, each fixed here:

| Part at 0.2.0 | Fixed by | How |
|---|---|---|
| `Acquisition.Data.Kline` | market's `KLine` | the field goes: the raw, corrected raw and clean k-lines are `Market.KLine` |
| `Acquisition.Data.Source` | market's `KLine` (Open) | the field goes: the source is a log of k-lines, the vendor's corrected raw series, then its raw series |
| `Acquisition.Data.Correction` | market's `KLine` (Open) | the field goes: a correction is the bar as corrected, known by its `date`, and numbered by its place among the corrections |
| `Kafka.Topic.Key` | no contract: `Empty` (Open) | each topic of a working space is made with no key |
| `Kafka.Topic.Value` | the topic's kind | each topic of a working space is made with its kind's message: acquisition's topics `KLine`, the engine's its result, one of chanlun's six records (`MarketModelEngine.Result`, Open) |
| `Warehousing.Data.Push` | the topic's value (Open) | the field goes: what is pushed for a record is its value |
| `Wiring.Push` | as `Warehousing.Data.Push` | the field goes |
| `Visualization.Data.View` | the records it reads (Open) | the field goes: visualization gives one log for each partition of each topic it reads, of that partition's values |
| `Wiring.View` | as `Visualization.Data.View` | the field goes |
| `Workspace.InputMsg` | market's `KLine` | a field of the general working space, which `Wiring.workspace` fills: both input logs are of k-lines |
| `Workspace.OutputMsg` | the topics' values | as `InputMsg`: each log that leaves the system is of the value type of the topic it is from |

`Kafka.Topic.Key` and `Kafka.Topic.Value` stay fields of Kafka's topic, which is the same shape for every topic; what is fixed is every topic a working space has, which is made from its name, the naming's of its signature and its kind, and its partitions, with no key and its kind's message. `Workspace.InputMsg` and `Workspace.OutputMsg` stay fields of the general working space, over which the wiring builds; every working space the wiring makes has them fixed, and so does every working space of `Workspaces`, which holds wirings.

The other twelve say which topics and logs a working space has. Acquisition's one topic of each kind and the engine's one topic fix five: `Acquisition.Data.Topic` (the field goes: each kind has one topic, made from acquisition's signature and the kind's partitions, which its data names), `MarketModelEngine.Data.Out` and `Wiring.Engine.Out` (the fields go: the engine writes one topic, made from its series' signature and its partitions, which its data names), `Wiring.Engine.Clean` and `Wiring.Shown` (the fields go: the engine and visualization read acquisition's one clean topic). The other seven stay open, as a topic's partitions do: `MarketModelEngine.Data.In`, `Visualization.Data.Clean`, `Visualization.Data.Model` and `Warehousing.Data.Topic`, a component's own data, which the wiring fills; `Workspace.Input`, `Workspace.Output` and `Workspace.Topic`, the general working space's.

### The topics

A working space is one series: one k-line series, of one signature, the security (its ticker), the market (a symbol), the exchange (a symbol), the source (an id: Massive, say, is a source) and the k-line's period (1-minute or daily bars, say). Some tickers already carry the exchange. Acquisition has one topic of each kind, raw, clean and corrections, and the engine one topic, its series' chanlun results. A topic is known by its signature: its name carries the signature and its kind (acquisition's three, and the engine's results), so that no two topics have one name. A chanlun result series is derived from a k-line series, has no meaning apart from it, and is known by its signature: the engine's topic is named from its series' signature, its results name only k-lines of that series and merged bars among them (`refers`), and an engine reads one series. As each table is of one working space, a table holds the rows of one series' kinds alone; a chart and an engine are each of one series.

In the Lean (Open): the signature is `Acquisition.Signature`, its five fields strings, the exchange held even where the ticker carries it, a field of acquisition's data. The naming is one function of a signature and a topic's kind to a name, losing neither, a parameter of `Wiring` and of `Workspaces`, one for every working space side by side. Acquisition's data holds its signature and, for each kind, its topic's partitions and its home; the engine's data, its topic's partitions and its home. Each topic of a wiring is made from the naming of its signature and kind, its partitions, no key and its kind's message, so that no two of a wiring's topics have one name (`Wiring.acq_names` and `Wiring.cross_names` theorems, fields at 0.2.0). `Workspaces` holds wirings of the one naming, no two of one signature (a field of it), so that no two topics of any of them have one name (`Workspaces.topics_distinct` a theorem, a field at 0.2.0). Without them, two wirings of one signature, each of its own naming, would pass a check of names alone and make two topics of one signature and kind.

Market's `OngoingKLine` is held with its contract and carried by no topic: acquisition's three kinds carry complete k-lines (Open).

## The component specs

Each component's spec is a structure of `Prop`s on the component (`Acquisition.Spec`, `Warehousing.Spec`, `MarketModelEngine.Spec`, `Visualization.Spec`), one field for each requirement, its doc comment saying what the requirement asks. Its objectives and features are the doc comments of the component's file and structure. An input of a process is what has been read so far, so a requirement on every input says what is given at every moment: no output waits for more input than the requirement names. The requirements below are under Open, all but the engine's `publish` (Order).

### Acquisition

**Objectives.** Give the working space its k-lines on Kafka: the vendor's series, raw and clean, and the vendor's corrections, each kind on a topic of its own, known by the series' signature.

**Features.** The raw series in two parts, the vendor's corrected raw series and then its raw series, read as one source; how the reader reads both (a replayer in it, say) and when it switches is the reader's. Cleaning in acquisition, not in warehousing. The corrections published as they come and applied to nothing, so that the raw and clean topics do not depend on them (`Acquisition.clean_topics`). One acquisition to a working space, of its one series; several working spaces side by side, of one naming, no two of one signature (`Workspaces`). Each kind's series goes, whole and in order, to one partition of its topic, its home, which acquisition's data names: where a series goes is acquisition's, as its readers must know it to read the series back.

**Requirements** (`Acquisition.Spec`), for every input:
- `reader`: the raw series is the source's k-lines, in its order, each with its place in the series as its `index`: position `n` of the raw series holds the source's k-line at `n`, with `index` `n`. The `index` a k-line has in an input log is not read: the reader, and the publisher of the corrections, number each k-line by its place.
- `cleaner`: the clean series is `Acquisition.clean` of the raw series: in order, each raw k-line that breaks none of `KLine`'s rules (`Market.broken Market.KLine.rules k = []`) and whose `date` is after the date of every k-line kept before it, each with its place in the clean series as its `index`; its prices and its volume are as read, never repaired. So a k-line whose date is past those of the k-lines after it, one far in the future say, is kept, and the k-lines after it are dropped until one's date passes it.
- `publishRaw`, `publishClean`: the kind's home holds the series, in order, each record with its k-line as its value; every other partition of the kind's topic holds nothing.
- `publishCorrections`: the corrections' home holds the corrections, in order, as they come, each record's value its correction with its place among the corrections as its `index`; every other partition of the topic holds nothing.
- Each kind has its home, one partition of its one topic: acquisition's data names it, with the topic's partitions.

### Reading a series back from its topics

A kind's series is the values of its home, in order: Kafka keeps order within a partition, and the publisher writes the whole series there and nothing elsewhere. Each k-line of the raw, the clean and the corrections series holds its place in its series as its `index` (market's position), so whatever reads the series finds at each position `n` the k-line of index `n`; a correction is known by its `date`, the bar it corrects being the one of that date.

For acquisition's series, one partition is a choice, not a necessity. The decision that left this condition (`docs/decisions.md`) found that a series spread over several partitions would need its order written into its records; each k-line now holds it, its `index`. So a series spread over its topic's partitions by its `index`, the k-line of index `n` in partition `n mod P` say, is still read back in order, by a process: it gives position `n` once, for each `m ≤ n`, it has read the first k-line of index `m` in partition `m mod P`. `Kahn.no_arrival_merge` does not forbid it: that theorem is of a merge that passes a message on while nothing has come from the other log, and this process passes on no k-line before those of lower index. What no process does is read in order every series whose k-lines are placed by no rule its reader knows: which partition holds the next one is then known only as the records arrive. One partition is the proposal (Open): no reader merges, and Kafka's order within the partition is the series' order. The other way is the placement by index, each reader of the series taking it back by index.

The engine's results are read back alike: its topic's home holds them, in the order its worker gives them, and its other partitions hold nothing (`publish`). For them one partition is a requirement (Order). A result names k-lines of its series by their `index` and merged bars by their `mIndex`, so it is read with the series it is derived from.

### Warehousing

**Objectives.** Keep in the database every record of acquisition's topics, of every kind.

**Features.** One consumer for each schema, the same for every topic and partition of it, given by the schema alone; one partition at a time; a table may take several topics, and every partition of each (`Wiring.table`); cleaning is acquisition's, not warehousing's.

**Requirements** (`Warehousing.Spec`): `consumer`: for every schema and every log of records, what it pushes is the values of the records that have one, in order (`Log.filterMap Kafka.Record.value`, a process). What it pushes for a topic of values `V` is a `V`: the row is the record's value, by the topic's schema.

### The market model engine

**Objectives.** Give 缠论's records of its series on a topic of its own, for visualization: a result series derived from the clean series, known by its signature.

**Features.** Optional. It reads clean topics, and takes its series from one partition of them, which its data names: in a working space, acquisition's one clean topic, its series the clean home. It is a worker, which gives its results, and a publisher, which writes them to its one topic. Each message of that topic is one result, one of chanlun's records (`MarketModelEngine.Result`, its form Open), and the topic is named from its series' signature and its kind. How the worker computes its results, in what order it gives them, and when it gives again a record still going on are the worker's library's.

**Requirements** (`MarketModelEngine.Spec`), for every input, its series being the values of the partition its data names, and its results what its worker gives of it:
- `records`: every result keeps every rule of its record (`Chanlun.broken (its rules) r = []`).
- `refers`: each position a result names (a merged bar's `start`, `end`, `confirmEnd`, `extremes` and `index`) is the `index` of a k-line of its series it has read; each bar a result names (a 分型's `mIndex`; a line's, a 线段's, a 走势's and a 中枢's `start`, `end` and `confirmEnd`) is the `mIndex` of a merged bar among its results.
- `covers`: each k-line of its series it has read that keeps market's rules is, by its `index`, from the `start` to the `end` of a merged bar among its results: one still merging, its `confirmEnd` not set, at the least, so that no k-line waits for a later one.
- `publish`: its topic's home holds its results, in the order its worker gives them, each record's value its result; every other partition of its topic holds nothing.
- Its data names its series' partition, and its topic's partitions and its home.

Its series is one log, the partition its data names, and its requirements are of that log. With a series spread over partitions by its `index` (Reading a series back from its topics), they would be of the log taken back by index; with one partition, Kafka's log is the series.

Not required: that its results are right by 缠论's lessons (how k-lines merge, where a 分型 is), or that they come in the right order: both are the worker's library's, which no contract states (Order).

### Visualization

**Objectives.** Show the clean series, and the engine's results when the engine is there, as a chart in an HTML page.

**Features.** A pure consumer, writing no topic. Without the engine, the chart is drawn from the clean topic alone (`Wiring.chart_without_engine`). The chart on the page at any moment is the set of what its logs hold so far (`Rows.ofLogs`), each record placed by its own positions: a k-line by its `index` and `date`, a result by its record's positions and bars. Which record still going on it draws over which is the page's.

**Requirements** (`Visualization.Spec`), for every input:
- `chart`: for each partition of each topic it reads, its log is the values of that partition's records that have one, in order. It gives one log for each partition it reads: one log of several topics' records would merge by arrival (`Kahn.no_arrival_merge`), so no process with one log shows every record it reads.
- It reads a clean topic, a field of its data: in a working space, acquisition's one clean topic.

### The working space

`Wiring` holds each component's spec beside the component, and joins them: the engine and visualization read acquisition's one clean topic, the engine's series its home. `Workspaces` holds wirings of one naming, no two of one signature, each working space side by side one a wiring makes. The wiring's theorems then state what the system gives:
- the clean home holds the clean series: k-lines that keep market's rules, their dates ascending, each one's `index` its position;
- the table a kind's topic is pushed into holds, from its home, exactly the kind's series' k-lines, and from the topic's other partitions nothing;
- the engine's topic's home holds, in its worker's order, results that keep their rules, name only k-lines of the clean series and merged bars among them, and cover each k-line of the clean series, and its other partitions nothing;
- the chart shows exactly the records of the partitions it reads, the clean series among them; without the engine, of the clean topic alone.

Two theorems for each component besides: one that gives nothing (`Process.const`, at the least output) meets no spec, on some input; and some component meets its spec. In the pinned Lean, `Float`'s order and `isFinite` are defined through its logical model, `Float.Model`, a subtype of `UInt64`, and the core library states no law of them. So a requirement applies a rule on floats as it is, and a proof that a record keeps such a rule takes it from a record the rule was given of, never from a law: the merged bar the engine that meets its spec gives for a k-line takes its low and its high from a pair of the k-line's prices that its `range` orders. Where a theorem needs a k-line that keeps market's rules (that the engine or the cleaner that gives nothing meets no spec), it is stated for any such k-line, and a concrete one is shown to keep the rules by evaluation (`decide`) where the kernel evaluates the model.

The theorems of `lean/` on the components are kept, each restated with the new types: `Acquisition.raw_topics`, `clean_topics`, `corrections_topics`; `Warehousing.run_apply`; `Wiring.names_distinct`, `acquisition_topics`, `clean_topics`, `engine_topics`, `warehousing_pushes`, `table_rows`; `Workspaces.system_apply`, of wirings. `Wiring.acq_names`, `Wiring.cross_names` and `Workspaces.topics_distinct`, fields at 0.2.0, become theorems, of the naming; `Wiring.engineTopic_names` goes, the engine having one topic. `Wiring.visualization_chart` and `Wiring.chart_without_engine` are stated of visualization's logs. The base's theorems (`lean/Kahn/`, `Kafka.compaction_not_process`) and the general working space's (`Workspace.system_apply`, `topics_eq`, `topics_least`, `acquisition_topics`, `has_tableRows`) are unchanged.

## What the replaced design guaranteed, and how each is kept

| Guarantee | Its source | How it is kept |
|---|---|---|
| Every part is a Kahn process: more input never takes back output, and no output waits for the end of the input | `lean/Kahn/Process.lean`; `docs/decisions.md`, on Kahn process networks | every part keeps its `Process` type; a spec is a `Prop` beside it, and what the specs define (`Acquisition.clean`, `Log.filterMap`, the numbering of a series) are processes |
| The system is one process of the input logs, the topics the least solution of its equations | `Workspace.system`, `Workspace.topics_eq`, `Workspace.topics_least` | unchanged: the specs hold the components, not the network |
| Acquisition alone reads the input logs; the others read the topics alone | `Workspace.run`; `docs/decisions.md`, on the four components | unchanged |
| The engine and visualization read clean topics only, by type | `Wiring.engineData`, `Wiring.visualizationData` | unchanged; both read acquisition's one clean topic, the engine's series its home |
| Only warehousing writes into the database | `Workspace.table` | unchanged |
| Each kind's topics are made from its own series alone; the raw and clean topics do not depend on the corrections | `Acquisition.raw_topics`, `clean_topics`, `corrections_topics`, `Wiring.clean_topics` | `Acquisition.run` keeps its form, its types the contracts' records; the four theorems restated with them |
| No merge by arrival | `Kahn.no_arrival_merge` | no requirement asks a process to put several logs into one: a series goes to one partition, the engine reads its series from one and writes its results to one, and visualization gives one log for each partition it reads |
| One partition at a time | `Warehousing.run`; `docs/decisions.md`, on the clean topics | the consumer on each partition, as it is |
| `noncomputable` where the limit of logs needs it; the Lean a definition, not code to run | `docs/decisions.md`, on the Lean a definition | kept: the definition's Lean is checked by its proofs; the contracts' records and rules are computable, as the contracts state them, and the contracts' program that checks their examples evaluates them, which is the contracts' code, not the definition's |
| A topic is its whole log; no view that replaces a record already given is a process | `Kafka.compaction_not_process` | unchanged; no topic has a key, so none is compacted by one |
| Each topic has one writer, no two topics one name, each table one working space | `Workspace.names_distinct`, `Wiring.engineTopic_names`, `Wiring.names_distinct`, `Workspaces` | kept: `Wiring.names_distinct` restated; no two topics of a wiring, or of the working spaces side by side, have one name, by the one naming of their signature and kind and no two working spaces of one signature (`Wiring.acq_names`, `Wiring.cross_names`, `Workspaces.topics_distinct` theorems); the engine has one topic, so `Wiring.engineTopic_names` goes |
| Each working space depends on its own input logs alone | `Workspaces.system_apply` | kept, restated of wirings |
| A table is a set of rows, each a message marked with its log | `Kahn.Rows`, `Workspace.tableRows` | unchanged; a row's message is a record's value, and as every log into a table is of `KLine`, the mark tells two logs' rows apart |
| Two topics of one schema have one consumer, given by the schema alone | `docs/decisions.md`, on a topic's schema | unchanged: the consumer is one for each schema; acquisition's topics all have one, no key and `KLine` |
| The engine is optional; without it the chart is drawn from the clean topics alone | `Wiring.chart_without_engine` | kept, stated of visualization's logs |
| Every claim is proved, on Lean's three axioms | `dev/axioms.lean`, `make lean` | unchanged: the contracts' one theorem, `MergedBar.startNotAfterEnd`, is by `Nat.le_trans`, and `make lean` audits the moved Lean as every file of `lean/` |
| The export: one entry for every field of every structure of `lean/` | `dev/parts.lean`; `docs/decisions.md`, on the export | unchanged in form: the contracts' records and `Rule`, and each spec's requirements, are entries |
| What a component does in code is its own project's | `docs/decisions.md`, on the Lean a definition | kept: a spec says what a component gives, not how; how the reader switches, how the engine computes and how the page draws stay the implementation's |

## What is lost

- Any process of a part's type is one, one that gives nothing among them: a part is one only when it meets its spec.
- An acquisition of any k-line contract: the k-line is market's `KLine`, and a working space of another k-line contract is none of the definition's until that contract is held here.
- Several series in one working space: a working space is one series, of one signature; acquisition has one topic of each kind and the engine one, each known by the signature; market's `KLine` names no security and no period, the cleaner keeps a k-line only after the last kept one's date, and an `index` is a place in the one series. With it, as each table is of one working space: a table of several series, a table holding the rows of one series' kinds alone; a chart or an engine of several series, of two securities or of one security at two periods, say.
- A vendor's own form as the system's input, and a correction of any form: both input logs are of k-lines, and a correction that is no bar, a deletion say, has no form.
- A topic with a key.
- A kind of acquisition's with no topic, or with several: each has one.
- Several topics of the engine: it has one, its series' chanlun results. A topic for each of chanlun's records, or for each level of 线段, 走势 or 中枢 (each carries a `level`), is none; a reader of one record or one level alone, the merged bars say, reads the whole topic and passes over the others.
- A series spread over its topic's partitions: it goes to its home, and the topic's other partitions hold nothing; the placement by index would keep it (Open).
- The engine's results on any partition of any topic: they go to its one topic's home, and its other partitions hold nothing; no placement by index keeps a spread of them, as one partition is required of the engine (Order).
- An engine whose series is not the clean home, one that reads no clean topic say; and visualization in a working space showing no clean series.
- The engine's messages of any form: each is one result, one of chanlun's records, each record with a value.
- A bar still going on, on any topic: market's `OngoingKLine`, or a sum of complete and ongoing bars, is carried by no topic, as acquisition's kinds carry complete k-lines; so the engine works on no bar still going on, and the chart shows none.
- A push of any form: what warehousing pushes is the record's value; the record's timestamp, its headers and its offset are not in the table.
- Cleaning of any kind: the cleaner drops a k-line or keeps it, and repairs or fills none.
- Visualization's one log of chart updates: it gives a log for each partition it reads.
- A view of any form: visualization's logs are the values of the records it reads, and a view made of them in another form, an indicator say, is in none of its logs.
- Working spaces side by side that no wiring makes, of two namings, or two of one signature: `Workspaces` holds wirings of one naming, no two of one signature. And a topic's name of any form a wiring chooses for it: each is the one naming's, of its signature and kind.
- In the export, the entries of the fields that go, 21 of the 87: `Acquisition.Data.Correction`, `Acquisition.Data.Kline`, `Acquisition.Data.Source`, `Acquisition.Data.Topic`, `Acquisition.Data.topic`, `MarketModelEngine.Data.Out`, `MarketModelEngine.Data.outTopic`, `Visualization.Data.View`, `Warehousing.Data.Push`, `Wiring.Engine.Clean`, `Wiring.Engine.Out`, `Wiring.Engine.clean`, `Wiring.Engine.names_distinct`, `Wiring.Engine.outTopic`, `Wiring.Push`, `Wiring.Shown`, `Wiring.View`, `Wiring.acq_names`, `Wiring.cross_names`, `Wiring.shown`, `Workspaces.topics_distinct`; of them, `Wiring.acq_names`, `Wiring.cross_names` and `Workspaces.topics_distinct` become theorems. A field that stays with its type changed keeps its entry; the new fields have new entries (the signature's, the naming's, the partitions and homes, the engine's publisher, `Workspaces`' signatures, each spec's requirements).

## The files it shapes

- The contract specs: `lean/Contract/Market.lean` and `lean/Contract/Chanlun.lean`, new; `lean/Kafka.lean` (a topic of a working space, made with no key and its value); `lean/Acquisition.lean`, `lean/Warehousing.lean`, `lean/Visualization.lean`, `lean/MarketModelEngine.lean`, `lean/Wiring.lean`; `lean/Workspace.lean`, whose `Workspaces` moves beside `Wiring`; the list of modules, in `lean/lakefile.toml`, `dev/axioms.lean` and `dev/parts.lean`; `export/parts.json`; `README.md`, `PRODUCTS.md`, `docs/acquisition.md`.
- The component specs: the same files of the components, `lean/Kahn/Log.lean` (`Log.filterMap`), `lean/Wiring.lean`, `export/parts.json`, `README.md`, `docs/acquisition.md`.
