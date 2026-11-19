# Market's contract: the guide for an implementation

How an implementation of market's contract is made from its definition, and how that is checked. What each record, field and rule is, is `lean/Contract/Market.lean`, each in its doc comment and the module's comment: this guide names them, and restates none.

## What it implements

- In `lean/Contract/Market.lean`: the records `Market.KLine` and `Market.OngoingKLine`; their rules, `Market.KLine.rules` and `Market.OngoingKLine.rules`; `Market.Rule` and `Market.broken`; `Market.KLine.Keeps` and `Market.OngoingKLine.Keeps`, with `Market.KLine.keeps_iff` and `Market.OngoingKLine.keeps_iff`.
- In the export (`export/parts.json`), which holds structures' fields alone: the records' fields (`Market.KLine.index`, …, `Market.OngoingKLine.asOf`), `Market.Rule`'s, and the `Keeps`' (`Market.KLine.Keeps.finite`, …). The rules, `broken` and the theorems are no entries.

## The method

An implementation's input is a record's data, in the form the `.proto` gives it; its output is what the formal definition fixes.

1. **The form of the data: the `.proto`.** One message for each record, field for field its record in `lean/Contract/Market.lean`: the same fields, each named as the Lean names it or as Protobuf names it (`as_of` for `asOf`), each of the type its Lean type is on the wire: a `Nat` a uint64, a `Float` a double. The field numbers and the reserved names are the `.proto`'s own. A value is a record only as a message of the `.proto`: one with a field past a uint64's 2⁶⁴ − 1 is none, a bound the records leave to the reader (`lean/Contract/Market.lean`, the module's comment).
2. **The rules: programmed in a language.** For each record, a check, programmed in a language of the implementation's choosing, takes a record's data, a message of the `.proto`, as its input and gives as its output the names of the rules of its record that the message breaks: for every message, what `Market.broken` gives of the record it holds, the same names in the same order. By `Market.KLine.keeps_iff` and `Market.OngoingKLine.keeps_iff`, a message then passes its check exactly when its record keeps the contract.

## What is its own

- Each message's field numbers and reserved names.
- The languages, and how each check is programmed in each, so long as its output is what step 2 asks.
- How a language reads and writes a message of the `.proto`: by code a standard Protobuf generator makes from it, say, or, in Lean, which none serves, by a reader of its own (`ProtoJson`, its `FromJson` instances) into the definition's records; and what its readers refuse.
- Its examples, and the program that checks them in each language.

## How it is checked

- The definition: by its proofs, on Lean's three axioms (`make lean` in this project).
- Step 1: each message of the `.proto` against its record's entries in the export (`export/parts.json`), the fields by name and by type, as step 1 maps them. The export gives each field of each record, so this is checked mechanically, not by reading.
- Step 2: by the examples, each a value in Protobuf's JSON with the record it is and the names of the rules it breaks, or marked `refused`, as no message of the `.proto`. The definition gives each example's names (`Market.broken` is computable, and Lean evaluates it on the example read), and each language's check gives the same; each language refuses each example marked `refused`.
- What the examples do not show: that a check gives what `Market.broken` gives on every message. That is tested on the examples, not proved.

## How it takes the definition

- Its Lean takes `Contract.Market` from the Lake package `qi-v2-platform-definition`, pinned at a release, and holds no copy of the records or the rules: it adds its reader (`ProtoJson`, its `FromJson` instances) and its examples program.
- Its `.proto`'s comments and its README point to the definition for what each field is, holding no copy of it.
