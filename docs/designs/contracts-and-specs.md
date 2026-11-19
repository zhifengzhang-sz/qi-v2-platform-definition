# The contract specs and the component specs

The definition has two parts (`docs/decisions.md`, the owner's two decisions of 2026-11-19): the contract specs, the formal definition of each contract, its records and its rules; and the component specs, each component's objectives, requirements and features. This design says what the definition holds of each contract, which record fixes each data type the definition left open, what each component must do, and what the design it replaces guaranteed, kept or lost. Its proposals that the owner has not decided are under Open in `docs/decisions.md`. The Lean follows in two steps: first the contract specs, `lean/Market.lean` and `lean/Chanlun.lean`, with the components taking their records; then the component specs.

## What this design guarantees

- Every message of a working space the wiring makes is a contract's record: its input logs and acquisition's topics carry market's `KLine`, the engine's topics chanlun's records, and what leaves the system is the values of the records read. No data type of a component is a parameter; what stays open is which topics and logs a working space has, their names and their partitions.
- Each component meets its spec, a structure of `Prop`s on its processes, one for each requirement. A component that gives nothing meets no spec: on some input it gives less than its spec asks (a theorem for each component).
- Each spec is met by some component (a theorem for each), so no spec contradicts itself or Kahn's condition.
- Each series acquisition publishes is read back from its topics, whatever partition each of its k-lines went to: each k-line holds its place in its series, its `index`.
- What the replaced design guaranteed is kept, but for what is listed under What is lost (both below).

## The contract specs

### What the definition holds of a contract

A contract is its records and its rules. A record is a structure, field for field the message of the contract's `.proto`. A rule is a name and what holds of a record that keeps it (`Rule`: `name`, `holds`, and `dec`, that `holds` is decidable); `broken rules x` gives the names of the rules of `rules` that `x` breaks, in their order. Each rule is of one record alone.

The definition holds each contract's records and rules as the contract's Lean states them, in name and meaning unchanged, each contract in its own file and namespace: `lean/Market.lean` (`Market`) and `lean/Chanlun.lean` (`Chanlun`). They import nothing: the contract's Lean imports `Lean.Data.Json` for its reader alone. Each keeps its own `Rule` and `broken`, as the two contracts state them, so that a contract takes its records and rules by the names it has.

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
| `Acquisition.Data.Correction` | market's `KLine` (Open) | the field goes: a correction is the bar as corrected, known by its `date` |
| `Kafka.Topic.Key` | no contract: `Empty` (Open) | each topic of a working space is made with no key |
| `Kafka.Topic.Value` | the topic's kind | each topic of a working space is made with its kind's record: acquisition's topics `KLine`, each of the engine's one of chanlun's six records (`MarketModelEngine.Kind`) |
| `Warehousing.Data.Push` | the topic's value (Open) | the field goes: what is pushed for a record is its value |
| `Wiring.Push` | as `Warehousing.Data.Push` | the field goes |
| `Visualization.Data.View` | the records it reads (Open) | the field goes: visualization gives one log for each partition of each topic it reads, of that topic's values |
| `Wiring.View` | as `Visualization.Data.View` | the field goes |
| `Workspace.InputMsg` | market's `KLine` | a field of the general working space, which `Wiring.workspace` fills: both input logs are of k-lines |
| `Workspace.OutputMsg` | the topics' values | as `InputMsg`: each log that leaves the system is of the value type of the topic it is from |

`Kafka.Topic.Key` and `Kafka.Topic.Value` stay fields of Kafka's topic, which is the same shape for every topic; what is fixed is every topic a working space has, which is made from its name and its partitions, with no key and its kind's value. `Workspace.InputMsg` and `Workspace.OutputMsg` stay fields of the general working space, over which the wiring builds; every working space the wiring makes has them fixed.

The other twelve say which topics and logs a working space has, and stay open, as a topic's name and its partitions do: `Acquisition.Data.Topic`, `MarketModelEngine.Data.In`, `MarketModelEngine.Data.Out`, `Visualization.Data.Clean`, `Visualization.Data.Model`, `Warehousing.Data.Topic`, `Wiring.Engine.Clean`, `Wiring.Engine.Out`, `Wiring.Shown`, `Workspace.Input`, `Workspace.Output`, `Workspace.Topic`. `MarketModelEngine.Data.Out` is which topics the engine writes; their messages are those topics' values.

Market's `OngoingKLine` is held with its contract and carried by no topic: acquisition's three kinds carry complete k-lines (Open).

## The component specs

Each component's spec is a structure of `Prop`s on the component (`Acquisition.Spec`, `Warehousing.Spec`, `MarketModelEngine.Spec`, `Visualization.Spec`), one field for each requirement, its doc comment saying what the requirement asks. Its objectives and features are the doc comments of the component's file and structure. The requirements below are the session's proposal (Open).

### Acquisition

**Objectives.** Give the working space its k-lines on Kafka: the vendor's series, raw and clean, and the vendor's corrections, each kind on topics of its own.

**Features.** The raw series in two parts, the vendor's corrected raw series and then its raw series, read as one source; how the reader reads both (a replayer in it, say) and when it switches is the reader's. Cleaning in acquisition, not in warehousing. The corrections published as they come and applied to nothing, so that the raw and clean topics do not depend on them (`Acquisition.clean_topics`). One acquisition to a working space, several working spaces side by side (`Workspaces`). Which topic of its kind a k-line goes to, and which partition, is the publisher's.

**Requirements** (`Acquisition.Spec`), for every input:
- `reader`: the raw series is the source's k-lines, in its order, each with its place in the series as its `index`: position `n` of the raw series holds the source's k-line at `n`, with `index` `n`.
- `cleaner`: the clean series is `Acquisition.clean` of the raw series: in order, each raw k-line that breaks none of `KLine`'s rules (`Market.broken Market.KLine.rules k = []`) and whose `date` is after the date of every k-line kept before it, each with its place in the clean series as its `index`. A k-line is dropped or kept, never repaired.
- `publishRaw`, `publishClean`: the topics of the kind hold the series and nothing else: every record written has a value, and a k-line is the value of a record of one of the kind's topics, at some partition and position, exactly when the series holds it.
- `publishCorrections`: the same, of the corrections, each with its place in the corrections stream as its `index`.
- Each kind has a topic, a field of `Acquisition.Data`: with none, no publisher holds its series.

### Reading a series back from its topics

A series in which each k-line's `index` is its position is read back from the set of its k-lines: position `n` holds the k-line whose index is `n`. So two such series with the same k-lines are one (a theorem), and a kind's topics, holding its series' k-lines in any partitions and in any order across them, give the series back. The reader, the cleaner and the corrections' publisher number their series so. Kafka's order, which holds within a partition only, is not needed. The decision that left this condition found that a publisher would have to write the order into its records (`docs/decisions.md`, overturned 2026-11-19): market's `index` is that order, in every k-line.

### Warehousing

**Objectives.** Keep in the database every record of acquisition's topics, of every kind.

**Features.** One consumer for each schema, the same for every topic and partition of it, given by the schema alone; one partition at a time; a table may take several topics, and every partition of each (`Wiring.table`); cleaning is acquisition's, not warehousing's.

**Requirements** (`Warehousing.Spec`): `consumer`: for every schema and every log of records, what it pushes is the values of the records that have one, in order (`Log.filterMap Kafka.Record.value`, a process). What it pushes for a topic of values `V` is a `V`: the row is the record's value, by the topic's schema.

### The market model engine

**Objectives.** Give 缠论's records of the clean series on topics of its own, for visualization.

**Features.** Optional. It reads clean topics. Each of its topics carries one of chanlun's six records (`MarketModelEngine.Kind`, the topic's kind). How it computes its records, how it combines the topics it reads, and when it writes again a record still going on are its own.

**Requirements** (`MarketModelEngine.Spec`), for every input:
- `records`: every record it writes has a value, which keeps every rule of its record (`Chanlun.broken (its rules) r = []`).
- `refers`: each position a record names (a merged bar's `start`, `end`, `confirmEnd`, `extremes` and `index`) is the `index` of a k-line it has read; each bar a record names (a 分型's `mIndex`; a line's, a 线段's, a 走势's and a 中枢's `start`, `end` and `confirmEnd`) is the `mIndex` of a merged bar it has written.
- `covers`: each k-line it has read that keeps market's rules is, by its `index`, from the `start` to the `end` of a merged bar it has written. Every input is what has been read so far, so no k-line waits for a later one to be in a merged bar: one still merging, its `confirmEnd` not set, at the least.
- It has a topic of merged bars, a field of its data: with none, it covers nothing.

Not required: that its records are right by 缠论's lessons (how k-lines merge, where a 分型 is), which no contract states.

### Visualization

**Objectives.** Show the clean series, and the engine's records when the engine is there, as a chart in an HTML page.

**Features.** A pure consumer, writing no topic. Without the engine, the chart is drawn from the clean topics alone (`Wiring.chart_without_engine`). The chart on the page at any moment is the set of what its logs hold so far (`Rows.ofLogs`), each record placed by its own positions: a k-line by its `index` and `date`, a chanlun record by its positions and bars. Which record still going on it draws over which is the page's.

**Requirements** (`Visualization.Spec`): `chart`: for each partition of each topic it reads, its log is the values of that partition's records that have one, in order. It gives one log for each partition it reads: one log of several topics' records would merge by arrival (`Kahn.no_arrival_merge`), so no process with one log shows every record it reads.

### The working space

`Wiring` holds each component's spec beside the component. Its theorems then state what the system gives:
- the clean topics hold k-lines that keep market's rules, their dates ascending, and give the clean series back;
- a table holds a k-line of a topic pushed into it exactly when that topic's series holds it;
- the engine's topics hold records that keep their rules, refer to the clean series and cover each of its k-lines;
- the chart shows exactly the records of the topics it reads; without the engine, of the clean topics alone.

Two theorems for each component besides: one that gives nothing (`Process.const`, at the least output) meets no spec, on some input; and some component meets its spec. Lean's `Float` is opaque: no law of its order is provable, not even `x ≤ x`. So a requirement applies a rule on floats as it is, and a proof that a record keeps such a rule takes it from a record the rule was given of, never derives it from another.

## What the replaced design guaranteed, and how each is kept

| Guarantee | Its source | How it is kept |
|---|---|---|
| Every part is a Kahn process: more input never takes back output, and no output waits for the end of the input | `lean/Kahn/Process.lean`; `docs/decisions.md`, 2026-11-10 | every part keeps its `Process` type; a spec is a `Prop` beside it, and what the specs define (`Acquisition.clean`, `Log.filterMap`, the numbering of a series) are processes |
| The system is one process of the input logs, the topics the least solution of its equations | `Workspace.system`, `Workspace.topics_eq`, `Workspace.topics_least` | unchanged: the specs hold the components, not the network |
| Each kind's topics are made from its own series alone; the raw and clean topics do not depend on the corrections | `Acquisition.raw_topics`, `clean_topics`, `corrections_topics`, `Wiring.clean_topics` | `Acquisition.run` unchanged |
| No merge by arrival | `Kahn.no_arrival_merge` | no requirement asks a process to put several logs into one; visualization gives one log for each partition it reads for that reason |
| One partition at a time | `Warehousing.run`; `docs/decisions.md`, 2026-11-10 | the consumer on each partition, unchanged |
| `noncomputable` where the limit of logs needs it; the Lean a definition, not code to run | `docs/decisions.md`, 2026-11-10 | unchanged; the contracts' records and rules need no `noncomputable`, and their reader, which is code to run, stays the contracts' |
| A topic is its whole log; no view that replaces a record already given is a process | `Kafka.compaction_not_process` | unchanged; no topic has a key, so none is compacted by one |
| Each topic has one writer, no two topics one name, each table one working space | `Workspace.names_distinct`, `Workspaces` | unchanged |
| A table is a set of rows, each a message marked with its log | `Kahn.Rows`, `Workspace.tableRows` | unchanged; a row's message is a record's value |
| Two topics of one schema have one consumer, given by the schema alone | `docs/decisions.md`, 2026-11-10 | unchanged: the consumer is still one for each schema; acquisition's topics all have one, no key and `KLine` |
| The engine is optional; without it the chart is drawn from the clean topics alone | `Wiring.chart_without_engine` | kept, stated of visualization's logs |
| Every claim is proved, on Lean's three axioms | `dev/axioms.lean`, `make lean` | unchanged: the contracts' one theorem, `MergedBar.startNotAfterEnd`, is by `Nat.le_trans`, and `make lean` audits the moved Lean as every file of `lean/` |
| The export: one entry for every field of every structure of `lean/` | `dev/parts.lean`; `docs/decisions.md`, 2026-11-12 | unchanged in form: the contracts' records and `Rule`, and each spec's requirements, are entries |
| What a component does in code is its own project's | `docs/decisions.md`, 2026-11-10 | kept: a spec says what a component gives, not how; how the reader switches, how the engine computes and how the page draws stay the implementation's |

## What is lost

- Any process of a part's type is one, one that gives nothing among them: a part is one only when it meets its spec.
- An acquisition of any k-line contract: the k-line is market's `KLine`, and a working space of another k-line contract is none of the definition's until that contract is held here.
- A vendor's own form as the system's input, and a correction of any form: both input logs are of k-lines, and a correction that is no bar, a deletion say, has no form.
- A topic with a key.
- A push of any form: what warehousing pushes is the record's value; the record's timestamp, its headers and its offset are not in the table.
- Cleaning of any kind: the cleaner drops a k-line or keeps it, and repairs or fills none.
- Visualization's one log of chart updates: it gives a log for each partition it reads.
- In the export, the entries of the fields that go: `Acquisition.Data.Kline`, `Acquisition.Data.Source`, `Acquisition.Data.Correction`, `Warehousing.Data.Push`, `Visualization.Data.View`, `Wiring.Push`, `Wiring.View`.

## The files it shapes

- The contract specs: `lean/Market.lean` and `lean/Chanlun.lean`, new; `lean/Kafka.lean` (a topic of a working space, made with no key and its value); `lean/Acquisition.lean`, `lean/Warehousing.lean`, `lean/Visualization.lean`, `lean/MarketModelEngine.lean`, `lean/Wiring.lean`; the list of modules, in `lean/lakefile.toml`, `dev/axioms.lean` and `dev/parts.lean`; `export/parts.json`; `README.md`, `PRODUCTS.md`, `docs/acquisition.md`.
- The component specs: the same files of the components, `lean/Kahn/Log.lean` (`Log.filterMap`), `lean/Wiring.lean`, `export/parts.json`, `README.md`, `docs/acquisition.md`.
