# Chanlun's contract: the guide for an implementation

How an implementation of chanlun's contract follows its definition. What each record, field and rule is, and what the contract leaves to the records' user, is `lean/Contract/Chanlun.lean`, each in its doc comment and the module's comment: this guide names them, and restates none.

## What it implements

- In `lean/Contract/Chanlun.lean`: the records `Chanlun.MergedBar`, `Chanlun.Fractal`, `Chanlun.Line`, `Chanlun.Segment`, `Chanlun.Move` and `Chanlun.Consolidation`; their rules, `Chanlun.MergedBar.rules` and the others; `Chanlun.Rule` and `Chanlun.broken`; `Chanlun.MergedBar.Keeps` and the others, with `Chanlun.MergedBar.keeps_iff` and the others; `Chanlun.MergedBar.startNotAfterEnd`.
- In the export (`export/parts.json`), which holds structures' fields alone: the records' fields (`Chanlun.MergedBar.mIndex`, …, `Chanlun.Consolidation.dd`), `Chanlun.Rule`'s, and the `Keeps`' (`Chanlun.MergedBar.Keeps.finite`, …). The rules, `broken` and the theorems are no entries.
- Not the engine's result message, `MarketModelEngine.Result` (`lean/MarketModelEngine.lean`), which is the platform's, not the contract's.

## What it must give

- A message for each record, field for field: the same fields, each named as the Lean names it, or as Protobuf names it (`m_index` for `mIndex`, `confirm_end` for `confirmEnd`); a `Nat` a uint64, an `Option Nat` an optional uint64, a `List Nat` a repeated uint64, a `Float` a double, a `Bool` a bool.
- A check for each record that gives, for every record, what `Chanlun.broken` gives of its record's rules: the same names, in the same order. By `Chanlun.MergedBar.keeps_iff` and the others, a record then passes its check exactly when it keeps the contract.
- A reader that refuses a value with a field past a uint64's 2⁶⁴ − 1, a bound the records leave to it (`lean/Contract/Chanlun.lean`, the module's comment).

## What is its own

- The `.proto`, the wire's form, and the code generated from it with a standard library.
- Its readers, of Protobuf's JSON and of its binary form, in each language that reads each, and what else they refuse.
- How a check is written in each language, so long as it gives what `Chanlun.broken` gives.
- Its examples, and the program that checks them in each language.

## How it is checked

- The definition: by its proofs, on Lean's three axioms (`make lean` in this project).
- Each implementation: by its examples, each a value with the record it is and the names of the rules it breaks, or marked `refused`, as no record. Each language gives, for each example of a record, the names the example gives, and refuses each one marked `refused`.
- What the examples do not show: that a check gives what `Chanlun.broken` gives on every record. That is tested on the examples, not proved.

## How it takes the definition

- Its Lean takes `Contract.Chanlun` from the Lake package `qi-v2-platform-definition`, pinned at a release, and holds no copy of the records or the rules: it adds its reader (`ProtoJson`, its `FromJson` instances) and its examples program.
- Its `.proto`'s comments and its README point to the definition for what each field is, holding no copy of it.
