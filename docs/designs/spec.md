# The contract specs and the component specs

The platform's definition has two parts. The contract specs are the formal definition of each contract the platform uses, market's and chanlun's: its records and its rules. The component specs say what each component must do: its objectives, its features, and its requirements, each requirement a `Prop` its processes meet. This document gives the component specs, what the definition holds of a contract, and what the working space gives. What the Lean holds has its home there, each definition's doc comment its own, and this document points to it. The decisions behind it are in `docs/decisions.md`; how much of it the Lean holds is in `docs/milestones.md`; how an implementation follows each definition, and what is its own, is in `docs/guide/`.

## What it guarantees

- Every message of a working space is a contract's record or made of them. Both input logs and acquisition's three topics carry market's `KLine`; the engine's topic carries its results, each one of chanlun's records; what leaves the system is the values of the records read.
- A working space is one series, of one signature: the security, the market, the exchange, the source and the k-line's period. Acquisition has one topic of each kind, raw, clean and corrections, and the engine one, its series' chanlun results. Each topic is named from the signature and its kind, and has one partition and no key.
- Each component meets its spec, a structure of `Prop`s on its processes, one for each requirement. A component that gives nothing meets no spec: on some input it gives less than its spec asks. Each spec is met by some component, so no spec contradicts itself or Kahn's condition.
- Each series acquisition publishes is read back in order from its topic, each k-line holding its place in its series as its `index`; the engine's results are read back from its topic in the order its worker gives them (Order).
- Each topic has one writer and any number of readers, and each table of the database one working space. Working spaces side by side share one naming (a parameter of `Workspaces`) and no two have one signature (a field of `Workspaces`), so that no two of their topics have one name (a theorem); and no table is written by two of them (a field of `Workspaces`).
- Every part is a Kahn process: more input never takes back output, and no output waits for the end of the input. A working space is one process of its input logs, its topics the least solution of its equations. Acquisition alone reads the input logs, the others read the topics alone, and only warehousing writes into the database. No requirement asks a process to merge logs by arrival, which no process does (`Kahn.no_arrival_merge`), and a topic is its whole log, never compacted (`Kafka.compaction_not_process`).
- The Lean is a definition, not code to run: it is checked by its proofs, and `noncomputable` where the limit of logs needs it. What a component does in code is its own project's: a spec says what a component gives, not how.
- Every claim is proved, on Lean's three axioms alone (`dev/axioms.lean`); a statement that is a modelling choice, or taken as given, says so.
- The definition's parts are exported, one entry for every field of every structure of `lean/` (`export/parts.json`, `README.md`): the contracts' records and `Rule`, and each spec's requirements, among them.

## Order

The system obeys three axioms of order: the worker's library gives its results in the right order; the publisher publishes them in that order; the order of what is published is kept. They name no means: the table gives how the design satisfies each, and how what is built is verified to hold it. An axiom here is what the system obeys, not a Lean `axiom`: the definition's proofs rest on Lean's three alone.

| Axiom | How the design satisfies it | How what is built is verified to hold it |
|---|---|---|
| The worker's library gives its results in the right order | the engine's results are its worker's, in the order the worker gives them; of that order the definition asks only what `refers` asks, that a result is given no earlier than the merged bars it names, as no contract states what the right order is | of the library, by its own checks; of the worker, that it passes the library's results on in the library's order, reordering none |
| The publisher publishes them in that order | the engine's publisher writes each result as the worker gives it, in that order, to its topic (`publish`) | in the definition, `publish` is a field of the engine's spec, shown to be met by some engine; of what is built, the engine's code is verified to meet it: that it writes each result in turn, by a producer whose retries keep order (Kafka's idempotent producer, say) |
| The order of what is published is kept | each topic has one partition, and Kafka keeps order within a partition, which `lean/Kafka.lean` takes as a partition being one log, a record's position in it standing for its offset; every reader reads a topic's one log, merging none | in the definition, the wiring's theorems that the engine's topic holds its results in its worker's order and the clean topic the clean series; Kafka's order within a partition is taken as given, as its internals are; of what is built, that each topic has one partition, that each reader reads it from its start, that retention removes no record before it is read, and that what is read keeps the order written: at each position `n` of an acquisition topic a reader finds the k-line of index `n`, and the engine's topic read back is its results as its worker gave them |

Each of acquisition's series goes, whole and in order, to its topic, as the engine's results do: the design keeps the order of everything it publishes alike.

## The contract specs

### What the definition holds of a contract

A contract is its records and its rules. A record is a structure, field for field the message of the contract's `.proto`, each field's doc comment saying what it is and in what unit. A rule is a name and what holds of a record that keeps it (`Rule`: `name`, `holds`, and `dec`, that `holds` is decidable). A record's rules are a list, in their order, and `broken rules x` gives the names of the rules `x` breaks, in that order. Each rule is of one record alone.

That a record keeps its contract is a structure of `Prop`s, one field for each of its rules, by the rule's name: `KLine.Keeps`, `OngoingKLine.Keeps`, `MergedBar.Keeps`, `Fractal.Keeps`, `Line.Keeps`, `Segment.Keeps`, `Move.Keeps`, `Consolidation.Keeps`. A record keeps it exactly when it breaks none of its rules: `broken rules x = [] ↔ x.Keeps`, a theorem for each record.

The records and the rules were read from the contract's own Lean in name and meaning unchanged; their home is the definition, and the contract takes them from it at a release, by the names they have. Each contract is a module of its own, in its own namespace: `Contract.Market` (`lean/Contract/Market.lean`, namespace `Market`) and `Contract.Chanlun` (`lean/Contract/Chanlun.lean`, namespace `Chanlun`), so that a contract's own module of its name imports the definition's with no clash. They import nothing, and each has its own `Rule` and `broken`.

A field of type `Nat` holds a uint64: a value with a field past 2⁶⁴ − 1 is no record on the wire, which the contract's reader refuses. That bound is held by the contract's reader alone, not by the records. That no field of a record the platform writes passes it is a modelling choice, not a theorem: a series' `index` reaches 2⁶⁴ only after 2⁶⁴ k-lines.

`broken` and each rule's decision are computable, so that the contracts' program that checks their examples evaluates them. How an implementation of a contract is made from its definition, what is its own, and how it is checked: `docs/guide/market.md`, `docs/guide/chanlun.md`. On the wire a record crosses as Protobuf, a message of the `.proto`, its shape alone: the rules are applied within the workers that use them, which is what the component specs say.

### Market

The K-line and the ongoing K-line, of whatever source gives them: `Market.KLine`, a complete bar, and `Market.OngoingKLine`, a bar still going on, each with its rules and its `Keeps`, in `lean/Contract/Market.lean`, where each field's doc comment says what it is and in what unit.

### Chanlun

The records the algorithm of 缠论 makes beyond the K-line: `Chanlun.MergedBar` (包含's merged bar), `Chanlun.Fractal` (分型), `Chanlun.Line` (笔), `Chanlun.Segment` (线段), `Chanlun.Move` (走势) and `Chanlun.Consolidation` (中枢), each with its rules and its `Keeps`, in `lean/Contract/Chanlun.lean`, whose comment says what the contract says of a value and what it leaves to the records' user.

## The data

Every type a component works on is a contract's record, or made of them:

| What | Its type |
|---|---|
| a k-line, raw, corrected raw or clean | market's `KLine` |
| the source | a log of `KLine`: the vendor's corrected raw series, then its raw series |
| a correction | a `KLine`: the bar as corrected, known by its `date` |
| a topic's key | none: `Empty`, so that no record has one |
| the value of a record of acquisition's topics | `KLine` |
| the value of a record of the engine's topic | `MarketModelEngine.Result`, one of the engine's results |
| what warehousing pushes for a record | its value |
| what visualization gives | for each topic it reads, a log of its records' values |
| what leaves the system | warehousing's pushes and visualization's logs |

The engine's result, `MarketModelEngine.Result`, is one of chanlun's six records, which one said by its case: `mergedBar`, `fractal`, `line`, `segment`, `move` or `consolidation`, each holding its record. It keeps its rules when its record keeps its record's (`Result.Keeps`). It is the platform's message, made of the chanlun contract's records, not the contract's; on the wire it is a message whose one field of six (Protobuf's `oneof`) is chanlun's message of its record, its `.proto` not the definition's, as a contract's is not.

So a correction is a bar: one that is no bar, a deletion say, has no form. Each of acquisition's topics carries market's `KLine` alone, so a message holding the k-line with its signature, or with the vendor's own fields, is none: a k-line's series is known by its topic's signature.

Market's `OngoingKLine` is held with its contract and carried by no topic: acquisition's three kinds carry complete k-lines, so the engine works on no bar still going on, and the chart shows none.

Beside its components, each a process that meets its spec, a working space chooses its series' signature, the naming, one for every working space side by side, the table each of acquisition's topics is pushed into, and whether the engine is there. Every type of a working space, and each topic's name, partition, key and value, follow from these.

Kafka's topic has one shape for every topic, its key and value types and its number of partitions any (`Kafka.Topic`); warehousing reads topics of any schema, as its consumer is one for each (`Warehousing.Data`), which the wiring fills with acquisition's three; and the general working space has its input and output messages any (`Workspace`): what is fixed is every topic and every working space a wiring makes.

### The topics

A series' signature is its security (its ticker), its market (a symbol), its exchange (a symbol), its source (an id: Massive, say, is a source) and its k-line's period (1-minute or daily bars, say), each a string, the exchange held even where the ticker carries it (`Acquisition.Signature`, a field of the wiring: no process of acquisition's depends on it). A topic's kind is one of acquisition's three, raw, clean and corrections, or the engine's results. The naming is one function of a signature and a kind to a topic's name, losing neither: two pairs of one name are one pair (`Wiring.Naming`). It is a parameter of the wiring and of `Workspaces`, one for every working space side by side.

Each topic of a working space is made from the naming of its signature and its kind, with one partition, no key and its kind's message (`Kafka.Topic.ofName`), so that a topic's one partition holds a log of records of no key (`Kafka.Partition`). So no two topics of a working space have one name (`Wiring.names_distinct`, a theorem), and, as no two working spaces side by side have one signature, no two topics of any of them (`Workspaces.topics_distinct`, a theorem).

A chanlun result series is derived from a k-line series, has no meaning apart from it, and is known by its signature: the engine's topic is named from its series' signature, its results name only k-lines of that series and merged bars among them (`refers`), and an engine reads one series. Each table is of one working space, so a table holds rows of one series' kinds alone; a chart and an engine are each of one series.

## The component specs

Each component's spec is a structure of `Prop`s on the component (`Acquisition.Spec`, `Warehousing.Spec`, `MarketModelEngine.Spec`, `Visualization.Spec`), one field for each requirement, its doc comment saying what the requirement asks. Its objectives and features are the doc comments of the component's file and structure. An input of a process is what has been read so far, so a requirement on every input says what is given at every moment: no output waits for more input than the requirement names.

### Acquisition

**Objectives.** Give the working space its series' k-lines on Kafka: the vendor's series, raw and clean, and the vendor's corrections, each kind on a topic of its own, named from the series' signature.

**Features.** The raw series in two parts, the vendor's corrected raw series and then its raw series, read as one source; how the reader reads both (a replayer in it, say) and when it switches is the reader's, and that the source holds the corrected raw series first is a modelling choice, not a theorem. The vendor's own form is read into k-lines before the system's input. Cleaning in acquisition, not in warehousing. The corrections published as they come and applied to nothing, so that the raw and clean topics do not depend on them (`Acquisition.clean_topics`). A reset, which reads the corrected raw series again, is outside the working space: within one, nothing starts again. One acquisition to a working space.

**Requirements** (`Acquisition.Spec`), for every input:
- `reader`: the raw series is the source's k-lines, in its order, each with its place in the series as its `index`: position `n` of the raw series holds the source's k-line at `n`, with `index` `n`. The `index` a k-line has in an input log is not read: the reader, and the publisher of the corrections, number each k-line by its place.
- `cleaner`: the clean series is `Acquisition.clean` of the raw series: in order, each raw k-line that keeps market's rules (`KLine.Keeps`) and whose `date` is after the date of every k-line kept before it, each with its place in the clean series as its `index`; its prices and its volume are as read, never repaired. So a k-line whose date is past those of the k-lines after it, one far in the future say, is kept, and the k-lines after it are dropped until one's date passes it.
- `publishRaw`, `publishClean`: the kind's topic holds the series, in order, each record's value its k-line.
- `publishCorrections`: the corrections topic holds the corrections, in order, as they come, each record's value its correction with its place among the corrections as its `index`.

### Reading a series back from its topic

A kind's series is the values of its topic's one log, in order: the publisher writes the whole series there, and Kafka keeps order within a partition. Each k-line of the raw, the clean and the corrections series holds its place in its series as its `index` (market's position), so whatever reads the series finds at each position `n` the k-line of index `n`; a correction is known by its `date`, the bar it corrects being the one of that date.

The engine's results are read back alike: its topic holds them in the order its worker gives them (`publish`). A result names k-lines of its series by their `index` and merged bars by their `mIndex`, so it is read with the series it is derived from.

### Warehousing

**Objectives.** Keep in the database every record of acquisition's topics, of every kind.

**Features.** One consumer for each schema, the same for every topic and partition of it, given by the schema alone; one partition at a time; a table may take several topics (`Wiring.table`); cleaning is acquisition's, not warehousing's. A table is a set of rows, each a pushed value marked with the log it is from, in no order (`Workspace.tableRows`): several logs into one table is a process (`Kahn.Rows.ofLogs`), and as every log into a table is of `KLine`, the mark tells two logs' rows apart.

**Requirements** (`Warehousing.Spec`): `consumer`: for every schema and every log of records, what it pushes is the values of the records that have one, in order (`Log.filterMap Kafka.Record.value`, a process). What it pushes for a topic of values `V` is a `V`: the row is the record's value, by the topic's schema; the record's timestamp, its headers and its offset are not in the table.

### The market model engine

**Objectives.** Give 缠论's records of its series on a topic of its own, for visualization: a result series derived from the clean series, named from its signature.

**Features.** Optional: a working space may lack it. It reads one clean topic, its series: in a working space, acquisition's clean topic. It is a worker, which gives its results, and a publisher, which writes them to its topic. Each message of that topic is one result (`MarketModelEngine.Result`), and the topic is named from its series' signature and its kind. A reader of one record or one level alone, the merged bars say, reads the whole topic and passes over the others. How the worker computes its results, in what order it gives them, and when it gives again a record still going on are the worker's library's.

**Requirements** (`MarketModelEngine.Spec`), for every input, its series being the values of the topic it reads, and its results what its worker gives of it:
- `records`: every result keeps its rules (`Result.Keeps`).
- `refers`: each position a result names (a merged bar's `start`, `end`, `confirmEnd`, `extremes` and `index`) is the `index` of a k-line of its series it has read; each bar a result names (a 分型's `mIndex`; a line's, a 线段's, a 走势's and a 中枢's `start`, `end` and `confirmEnd`) is the `mIndex` of a merged bar among its results.
- `covers`: each k-line of its series it has read that keeps market's rules is, by its `index`, from the `start` to the `end` of a merged bar among its results: one still merging, its `confirmEnd` not set, at the least, so that no k-line waits for a later one.
- `publish`: its topic holds its results, in the order its worker gives them, each record's value its result.

Not required: that its results are right by 缠论's lessons (how k-lines merge, where a 分型 is), which no contract states; that they come in the right order is an axiom of the system, the library's to hold (Order).

### Visualization

**Objectives.** Show the clean series, and the engine's results when the engine is there, as a chart in an HTML page.

**Features.** A pure consumer, writing no topic. It reads one clean topic and, when the engine is there, the engine's topic: in a working space, acquisition's clean topic and the engine's. Without the engine, the chart is drawn from the clean topic alone (`Wiring.chart_without_engine`). The chart on the page at any moment is the set of what its logs hold so far (`Kahn.Rows.ofLogs`), each record placed by its own positions: a k-line by its `index` and `date`, a result by its record's positions and bars. Which record still going on it draws over which is the page's. A view made of its logs in another form, an indicator say, is in none of them.

**Requirements** (`Visualization.Spec`), for every input:
- `chart`: for each topic it reads, its log is the values of that topic's records that have one, in order. It gives one log for each topic it reads: one log of two topics' records would merge by arrival (`Kahn.no_arrival_merge`), so no process with one log shows every record it reads. So a visualization reads at least one topic, and one that gives nothing gives less than `chart` asks once the clean topic holds a record with a value.

### The working space

`Wiring` holds each component with its spec, and joins them: the engine and visualization read acquisition's clean topic, and visualization the engine's. The wiring's theorems state what the system gives:
- each kind's topic holds what acquisition makes of its own series alone, and the raw and clean topics do not depend on the corrections;
- the clean topic holds the clean series: k-lines that keep market's rules, their dates ascending, each one's `index` its position;
- the table each of acquisition's topics is pushed into holds, of the rows from that topic, exactly its kind's series' k-lines;
- the engine's topic holds, in its worker's order, results that keep their rules, name only k-lines of the clean series and merged bars among them, and cover each k-line of the clean series;
- the chart shows exactly the records of the topics it reads, the clean series among them; without the engine, of the clean topic alone.

Two theorems for each component besides: one that gives nothing (`Process.const`, at the least output) meets no spec, on some input; and some component meets its spec. In the Lean `lean/lean-toolchain` names, `Float`'s order and `isFinite` are defined through its logical model, `Float.Model`, a subtype of `UInt64`, and the core library states no law of them. So a requirement applies a rule on floats as it is, and a proof that a record keeps such a rule takes it from a record the rule was given of, never from a law: the merged bar the engine that meets its spec gives for a k-line takes its low and its high from a pair of the k-line's prices that its `range` orders. Where a theorem needs a k-line that keeps market's rules (that the engine or the cleaner that gives nothing meets no spec), it is stated for any such k-line, and a concrete one is shown to keep the rules by evaluation (`decide`) where the kernel evaluates the model.

`Workspaces` holds the working spaces side by side, each one a wiring makes: of one naming, no two of one signature (a field), so that no two topics of any of them have one name (a theorem); and no table is written by two of them (`Workspaces.tables_distinct`, a field: for working spaces `i` and `j`, a topic of kind `κ` of `i`'s acquisition and one of kind `κ'` of `j`'s, `(space i).table κ = (space j).table κ' → i = j`). What each working space gives depends on its own input logs alone (`Workspaces.system_apply`).

The general working space (`Workspace`) is the four components wired by the topics, of any data: the system one process of its input logs (`Workspace.system_apply`), its topics the least solution of its equations (`Workspace.topics_eq`, `Workspace.topics_least`), acquisition's topics what it writes from the input logs alone (`Workspace.acquisition_topics`), and a table the rows of every log pushed into it (`Workspace.has_tableRows`). Every working space a wiring makes is one.
