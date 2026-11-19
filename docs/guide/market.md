# Market's contract: the guide for an implementation

How an implementation of market's contract follows its definition. What each record, field and rule is, is `lean/Contract/Market.lean`, each in its doc comment and the module's comment: this guide names them, and restates none.

## What it implements

- In `lean/Contract/Market.lean`: the records `Market.KLine` and `Market.OngoingKLine`; their rules, `Market.KLine.rules` and `Market.OngoingKLine.rules`; `Market.Rule` and `Market.broken`; `Market.KLine.Keeps` and `Market.OngoingKLine.Keeps`, with `Market.KLine.keeps_iff` and `Market.OngoingKLine.keeps_iff`.
- In the export (`export/parts.json`), which holds structures' fields alone: the records' fields (`Market.KLine.index`, …, `Market.OngoingKLine.asOf`), `Market.Rule`'s, and the `Keeps`' (`Market.KLine.Keeps.finite`, …). The rules, `broken` and the theorems are no entries.

## What it must give

- A message for each record, field for field: the same fields, each named as the Lean names it, or as Protobuf names it (`as_of` for `asOf`); a `Nat` a uint64, a `Float` a double.
- A check for each record that gives, for every record, what `Market.broken` gives of its record's rules: the same names, in the same order. By `Market.KLine.keeps_iff` and `Market.OngoingKLine.keeps_iff`, a record then passes its check exactly when it keeps the contract.
- A reader that refuses a value with a field past a uint64's 2⁶⁴ − 1, a bound the records leave to it (`lean/Contract/Market.lean`, the module's comment).

## What is its own

- The `.proto`, the wire's form, and the code generated from it with a standard library.
- Its readers, of Protobuf's JSON and of its binary form, in each language that reads each, and what else they refuse.
- How a check is written in each language, so long as it gives what `Market.broken` gives.
- Its examples, and the program that checks them in each language.

## How it is checked

- The definition: by its proofs, on Lean's three axioms (`make lean` in this project).
- Each implementation: by its examples, each a value with the record it is and the names of the rules it breaks, or marked `refused`, as no record. Each language gives, for each example of a record, the names the example gives, and refuses each one marked `refused`.
- What the examples do not show: that a check gives what `Market.broken` gives on every record. That is tested on the examples, not proved.

## How it takes the definition

- Its Lean takes `Contract.Market` from the Lake package `qi-v2-platform-definition`, pinned at a release, and holds no copy of the records or the rules: it adds its reader (`ProtoJson`, its `FromJson` instances) and its examples program.
- Its `.proto`'s comments and its README point to the definition for what each field is, holding no copy of it.
