import Kahn.Process

/-!
# Logs

A log is an append-only sequence of messages, finite or endless. Position `n` holds `some m`
once the log has reached it; a position not reached is `none`, and so is every position after it.

A log `s` is below a log `t` when `s` is a prefix of `t`: everything `s` holds, `t` holds at the
same place. The empty log is the least; the limit of a growing log is the log that holds what any
stage holds. There is no last stage: a log is never finished, only longer.
-/

universe u v

namespace Kahn

open Domain

/-- A log of messages of type `α`: position `n` holds `some m` once the log has reached it, and a
position not reached is `none`, as is every position after it. -/
@[ext]
structure Log (α : Type u) where
  get : Nat → Option α
  closed : ∀ n, get n = none → get (n + 1) = none

namespace Log

variable {α : Type u} {β : Type v}

instance : Poset (Log α) where
  le s t := ∀ n a, s.get n = some a → t.get n = some a
  refl _ _ _ h := h
  trans h k n a hs := k n a (h n a hs)
  antisymm {s t} h k := by
    apply Log.ext
    funext n
    cases hs : s.get n with
    | none =>
      cases ht : t.get n with
      | none => rfl
      | some b => rw [k n b ht] at hs; cases hs
    | some a => exact (h n a hs).symm

/-- The empty log. -/
def empty : Log α :=
  ⟨fun _ => none, fun _ _ => rfl⟩

/-- In a chain of logs, a position once filled keeps its message. -/
theorem chain_agree (c : Chain (Log α)) {i j n : Nat} {a b : α}
    (hi : (c i).get n = some a) (hj : (c j).get n = some b) : a = b := by
  rcases Nat.le_total i j with h | h
  · have := c.mono h n a hi
    rw [hj] at this
    exact (Option.some.inj this).symm
  · have := c.mono h n b hj
    rw [hi] at this
    exact Option.some.inj this

open Classical in
/-- Position `n` of the limit of a chain: the message some stage holds there, if any does. -/
noncomputable def supGet (c : Chain (Log α)) (n : Nat) : Option α :=
  if h : ∃ i, (c i).get n ≠ none then (c (Classical.choose h)).get n else none

theorem supGet_eq_some (c : Chain (Log α)) (n : Nat) (a : α) :
    supGet c n = some a ↔ ∃ i, (c i).get n = some a := by
  unfold supGet
  constructor
  · intro h
    split at h
    · exact ⟨_, h⟩
    · cases h
  · rintro ⟨i, hi⟩
    split
    · next ex =>
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (Classical.choose_spec ex)
      rw [hb, chain_agree c hi hb]
    · next nex => exact absurd ⟨i, by rw [hi]; exact Option.some_ne_none a⟩ nex

/-- The limit of a chain of logs. -/
noncomputable def lim (c : Chain (Log α)) : Log α where
  get := supGet c
  closed n h := by
    cases h' : supGet c (n + 1) with
    | none => rfl
    | some a =>
      obtain ⟨i, hi⟩ := (supGet_eq_some c (n + 1) a).mp h'
      cases hn : (c i).get n with
      | none => rw [(c i).closed n hn] at hi; cases hi
      | some b =>
        have := (supGet_eq_some c n b).mpr ⟨i, hn⟩
        rw [h] at this
        cases this

noncomputable instance : Domain (Log α) where
  toPoset := inferInstance
  bot := empty
  bot_le _ _ _ h := by cases h
  sup := lim
  le_sup c i n a h := (supGet_eq_some c n a).mpr ⟨i, h⟩
  sup_le c x h n a ha := by
    obtain ⟨i, hi⟩ := (supGet_eq_some c n a).mp ha
    exact h i n a hi

theorem get_sup (c : Chain (Log α)) (n : Nat) (a : α) :
    (sup c).get n = some a ↔ ∃ i, (c i).get n = some a :=
  supGet_eq_some c n a

/-! ## Finite prefixes -/

/-- The first `k` messages of `s`. -/
def take (k : Nat) (s : Log α) : Log α where
  get n := if n < k then s.get n else none
  closed n h := by
    by_cases h1 : n + 1 < k
    · have h2 : n < k := by omega
      simp only [h2, ↓reduceIte] at h
      simp only [h1, ↓reduceIte]
      exact s.closed n h
    · simp only [h1, ↓reduceIte]

theorem take_le (k : Nat) (s : Log α) : take k s ≤ s := by
  intro n a h
  simp only [take] at h
  split at h
  · exact h
  · cases h

theorem take_step (k : Nat) (s : Log α) : take k s ≤ take (k + 1) s := by
  intro n a h
  simp only [take] at h ⊢
  split at h
  · simp only [show n < k + 1 by omega, ↓reduceIte]; exact h
  · cases h

/-- The finite prefixes of `s`, longer and longer. -/
def prefixes (s : Log α) : Chain (Log α) :=
  ⟨fun k => take k s, fun k => take_step k s⟩

/-- Every log is the limit of its finite prefixes. -/
theorem sup_prefixes (s : Log α) : sup (prefixes s) = s := by
  apply Poset.antisymm
  · exact sup_le _ _ fun k => take_le k s
  · intro n a h
    apply le_sup (prefixes s) (n + 1) n a
    show (if n < n + 1 then s.get n else none) = some a
    simp only [show n < n + 1 by omega, ↓reduceIte]
    exact h

/-! ## Message by message -/

/-- `f` applied to every message. -/
def map (f : α → β) (s : Log α) : Log β where
  get n := (s.get n).map f
  closed n h := by
    cases hs : s.get n with
    | none => rw [s.closed n hs]; rfl
    | some a => rw [hs] at h; cases h

theorem map_get_some {f : α → β} {s : Log α} {n : Nat} {b : β} (h : (map f s).get n = some b) :
    ∃ a, s.get n = some a ∧ f a = b := by
  simp only [map] at h
  cases hs : s.get n with
  | none => rw [hs] at h; cases h
  | some a => rw [hs] at h; exact ⟨a, rfl, Option.some.inj h⟩

theorem map_mono (f : α → β) {s t : Log α} (h : s ≤ t) : map f s ≤ map f t := by
  intro n b hb
  obtain ⟨a, ha, rfl⟩ := map_get_some hb
  show (t.get n).map f = some (f a)
  rw [h n a ha]
  rfl

/-- The process that applies `f` to every message. -/
def mapP (f : α → β) : Process (Log α) (Log β) where
  fn := map f
  mono := map_mono f
  cont c n b hb := by
    obtain ⟨a, ha, rfl⟩ := map_get_some hb
    obtain ⟨i, hi⟩ := (get_sup c n a).mp ha
    apply le_sup (c.map (map f) (map_mono f)) i n (f a)
    show ((c i).get n).map f = some (f a)
    rw [hi]
    rfl

/-! ## Finite logs -/

/-- The log holding the messages of `l`, in order, and nothing after them. -/
def ofList (l : List α) : Log α where
  get n := l[n]?
  closed n h := by
    simp only [List.getElem?_eq_none_iff] at h ⊢
    omega

/-- A finite log is a prefix of itself with more messages after it. -/
theorem ofList_le_append (l l' : List α) : ofList l ≤ ofList (l ++ l') := by
  intro n a h
  show (l ++ l')[n]? = some a
  rcases Nat.lt_or_ge n l.length with hn | hn
  · rw [List.getElem?_append_left hn]
    exact h
  · have h' : l[n]? = some a := h
    rw [List.getElem?_eq_none_iff.mpr hn] at h'
    cases h'

end Log

/-- What a process gives for a log is the limit of what it gives for the log's finite prefixes:
no output waits for the end of the input. -/
theorem Process.eq_sup_take {α : Type u} {β : Type v} [Domain β] (f : Process (Log α) β)
    (s : Log α) : f s = sup ((Log.prefixes s).map f f.mono) := by
  conv => lhs; rw [← Log.sup_prefixes s]
  exact f.map_sup (Log.prefixes s)

end Kahn
