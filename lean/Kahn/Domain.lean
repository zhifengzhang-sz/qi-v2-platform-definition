/-!
# Domains

Kahn orders the values a channel can hold by "more": a log that has received more messages is
above the log it was before. A domain is a partial order with a least element (nothing yet) in
which every chain (values growing step by step) has a least upper bound (where the chain goes).

This library stands alone. Mathlib has the same notions as `OmegaCompletePartialOrder`.
-/

universe u v w

namespace Kahn

/-- A partial order. -/
class Poset (α : Type u) extends LE α where
  refl : ∀ a : α, a ≤ a
  trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b

theorem Poset.le_of_eq {α : Type u} [Poset α] {a b : α} (h : a = b) : a ≤ b :=
  h ▸ Poset.refl a

/-- A chain: a sequence in which each value is below the next. -/
structure Chain (α : Type u) [LE α] where
  seq : Nat → α
  step : ∀ n, seq n ≤ seq (n + 1)

instance {α : Type u} [LE α] : CoeFun (Chain α) (fun _ => Nat → α) := ⟨Chain.seq⟩

namespace Chain

variable {α : Type u} {β : Type v}

theorem le_add [Poset α] (c : Chain α) (i : Nat) : ∀ k, c i ≤ c (i + k)
  | 0 => Poset.refl _
  | k + 1 => Poset.trans (le_add c i k) (c.step (i + k))

theorem mono [Poset α] (c : Chain α) {i j : Nat} (h : i ≤ j) : c i ≤ c j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  exact c.le_add i k

/-- A chain carried through a monotone map. -/
def map [LE α] [LE β] (c : Chain α) (f : α → β) (hf : ∀ {x y : α}, x ≤ y → f x ≤ f y) :
    Chain β :=
  ⟨fun n => f (c n), fun n => hf (c.step n)⟩

/-- The chain that stays at `a`. -/
def const [Poset α] (a : α) : Chain α :=
  ⟨fun _ => a, fun _ => Poset.refl a⟩

end Chain

/-- A domain: a partial order with a least element `bot` in which every chain has a least
upper bound `sup`. -/
class Domain (α : Type u) extends Poset α where
  bot : α
  bot_le : ∀ a : α, bot ≤ a
  sup : Chain α → α
  le_sup : ∀ (c : Chain α) (n : Nat), c n ≤ sup c
  sup_le : ∀ (c : Chain α) (x : α), (∀ n, c n ≤ x) → sup c ≤ x

namespace Domain

variable {α : Type u} [Domain α]

theorem sup_const (a : α) : sup (Chain.const a) = a :=
  Poset.antisymm (sup_le _ _ fun _ => Poset.refl a) (le_sup (Chain.const a) 0)

theorem sup_mono {c d : Chain α} (h : ∀ n, c n ≤ d n) : sup c ≤ sup d :=
  sup_le _ _ fun n => Poset.trans (h n) (le_sup d n)

end Domain

/-! ## Pairs: two channels side by side, each ordered on its own. -/

instance {α : Type u} {β : Type v} [Poset α] [Poset β] : Poset (α × β) where
  le x y := x.1 ≤ y.1 ∧ x.2 ≤ y.2
  refl x := ⟨Poset.refl x.1, Poset.refl x.2⟩
  trans h k := ⟨Poset.trans h.1 k.1, Poset.trans h.2 k.2⟩
  antisymm h k := Prod.ext (Poset.antisymm h.1 k.1) (Poset.antisymm h.2 k.2)

instance {α : Type u} {β : Type v} [Domain α] [Domain β] : Domain (α × β) where
  toPoset := inferInstance
  bot := (Domain.bot, Domain.bot)
  bot_le x := ⟨Domain.bot_le x.1, Domain.bot_le x.2⟩
  sup c := (Domain.sup (c.map Prod.fst fun h => h.1), Domain.sup (c.map Prod.snd fun h => h.2))
  le_sup c n := ⟨Domain.le_sup (c.map Prod.fst _) n, Domain.le_sup (c.map Prod.snd _) n⟩
  sup_le _ _ h := ⟨Domain.sup_le _ _ fun n => (h n).1, Domain.sup_le _ _ fun n => (h n).2⟩

theorem pair_le {α : Type u} {β : Type v} [Poset α] [Poset β] {a a' : α} {b b' : β}
    (h₁ : a ≤ a') (h₂ : b ≤ b') : ((a, b) : α × β) ≤ (a', b') :=
  ⟨h₁, h₂⟩

/-! ## Families: one channel for each index (for example one topic for each contract). -/

instance {ι : Type w} {β : ι → Type v} [∀ i, Poset (β i)] : Poset (∀ i, β i) where
  le f g := ∀ i, f i ≤ g i
  refl f i := Poset.refl (f i)
  trans h k i := Poset.trans (h i) (k i)
  antisymm h k := funext fun i => Poset.antisymm (h i) (k i)

instance {ι : Type w} {β : ι → Type v} [∀ i, Domain (β i)] : Domain (∀ i, β i) where
  toPoset := inferInstance
  bot _ := Domain.bot
  bot_le f i := Domain.bot_le (f i)
  sup c i := Domain.sup (c.map (fun f => f i) fun h => h i)
  le_sup c n i := Domain.le_sup (c.map (fun f => f i) _) n
  sup_le _ _ h i := Domain.sup_le _ _ fun n => h n i

end Kahn
