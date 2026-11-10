import Kahn.Log

/-!
# Rows

A set of rows holds messages in no order: it says which rows are in it, and nothing of when each
came. A set is below another when the other holds every row it holds. The empty set is the least;
the limit of a growing set holds what any stage holds.

The rows of a log are its messages, their order forgotten (`Log.rows`). The rows of several logs
together are the rows of each, each marked with the log it is from (`Rows.ofLogs`). Both are
processes. So several logs into one set of rows is a process, where even two logs into one log, in
the order their messages arrive, is not (`Kahn.no_arrival_merge`): a set does not say which message
came first.
-/

universe u v w

namespace Kahn

open Domain

/-- A set of rows of type `α`: `has a` says that the row `a` is in it. A row is in it or not: put
there twice, it is there once. -/
@[ext]
structure Rows (α : Type u) where
  has : α → Prop

namespace Rows

variable {α : Type u}

instance : Poset (Rows α) where
  le s t := ∀ a, s.has a → t.has a
  refl _ _ h := h
  trans h k a ha := k a (h a ha)
  antisymm h k := Rows.ext (funext fun a => propext ⟨h a, k a⟩)

instance : Domain (Rows α) where
  toPoset := inferInstance
  bot := ⟨fun _ => False⟩
  bot_le _ _ h := h.elim
  sup c := ⟨fun a => ∃ n, (c n).has a⟩
  le_sup c n a h := ⟨n, h⟩
  sup_le c x h a ha := by
    obtain ⟨n, hn⟩ := ha
    exact h n a hn

/-- The limit of a growing set holds a row once some stage holds it. -/
theorem has_sup (c : Chain (Rows α)) (a : α) : (sup c).has a ↔ ∃ n, (c n).has a :=
  Iff.rfl

variable {ι : Type w} {κ : ι → Type v}

/-- Several sets of rows as one: the rows of each, each marked with the set it is from. -/
def union : Process (∀ i, Rows (κ i)) (Rows (Σ i, κ i)) where
  fn s := ⟨fun r => (s r.1).has r.2⟩
  mono h r hr := h r.1 r.2 hr
  cont c r hr := by
    obtain ⟨n, hn⟩ := hr
    exact (has_sup _ _).mpr ⟨n, hn⟩

/-- The union holds a row of set `i` exactly when set `i` holds it. -/
theorem has_union (s : ∀ i, Rows (κ i)) (i : ι) (a : κ i) :
    (union s).has ⟨i, a⟩ ↔ (s i).has a :=
  Iff.rfl

end Rows

/-- The rows of a log: its messages, their order forgotten. -/
def Log.rows {α : Type u} : Process (Log α) (Rows α) where
  fn s := ⟨fun a => ∃ n, s.get n = some a⟩
  mono h a ha := by
    obtain ⟨n, hn⟩ := ha
    exact ⟨n, h n a hn⟩
  cont c a ha := by
    obtain ⟨n, hn⟩ := ha
    obtain ⟨i, hi⟩ := (Log.get_sup c n a).mp hn
    exact (Rows.has_sup _ _).mpr ⟨i, n, hi⟩

/-- A log's rows hold a message exactly when the log holds it, at some position. -/
theorem Log.has_rows {α : Type u} (s : Log α) (a : α) :
    (Log.rows s).has a ↔ ∃ n, s.get n = some a :=
  Iff.rfl

namespace Rows

variable {ι : Type w} {κ : ι → Type v}

/-- Several logs into one set of rows: the messages of each log, each marked with the log it is
from, in no order. It is a process; a merge of two logs into one log by arrival is not
(`Kahn.no_arrival_merge`). -/
noncomputable def ofLogs : Process (∀ i, Log (κ i)) (Rows (Σ i, κ i)) :=
  union ⊚ Process.pi fun i => Log.rows ⊚ Process.proj (κ := fun i => Log (κ i)) i

/-- The set holds a message of log `i` exactly when log `i` holds it, at some position. -/
theorem has_ofLogs (s : ∀ i, Log (κ i)) (i : ι) (a : κ i) :
    (ofLogs s).has ⟨i, a⟩ ↔ ∃ n, (s i).get n = some a :=
  Iff.rfl

end Rows

end Kahn
