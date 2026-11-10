import Kahn.Domain

/-!
# Processes

A process is a function from its input to its output that meets Kahn's condition:

* monotone: more input never takes back output it has given;
* continuous: the output for a chain's limit is the limit of the outputs. On logs this says that
  no output waits for the end of the input: what a process gives for an endless log is what it
  gives, step by step, for the log's finite prefixes (`Process.eq_sup_take` in `Kahn.Log`).
-/

universe u v w x

namespace Kahn

open Domain

/-- A Kahn process from `α` to `β`. -/
structure Process (α : Type u) (β : Type v) [Domain α] [Domain β] where
  fn : α → β
  mono : ∀ {x y : α}, x ≤ y → fn x ≤ fn y
  cont : ∀ c : Chain α, fn (sup c) ≤ sup (c.map fn mono)

namespace Process

variable {α : Type u} {β : Type v} {γ : Type w} [Domain α] [Domain β] [Domain γ]

instance : CoeFun (Process α β) (fun _ => α → β) := ⟨Process.fn⟩

/-- Continuity as an equation. -/
theorem map_sup (f : Process α β) (c : Chain α) : f (sup c) = sup (c.map f f.mono) :=
  Poset.antisymm (f.cont c) (sup_le _ _ fun n => f.mono (le_sup c n))

/-- The process that passes its input on. -/
def id : Process α α where
  fn x := x
  mono h := h
  cont c := sup_le _ _ fun n => le_sup (c.map (fun x => x) fun h => h) n

/-- Composition: the output of `f` wired to the input of `g`. -/
def comp (g : Process β γ) (f : Process α β) : Process α γ where
  fn x := g (f x)
  mono h := g.mono (f.mono h)
  cont c :=
    Poset.trans (g.mono (f.cont c)) <|
      Poset.trans (g.cont (c.map f f.mono)) <|
        sup_le _ _ fun n => le_sup (c.map (fun x => g (f x)) fun h => g.mono (f.mono h)) n

@[inherit_doc] infixr:90 " ⊚ " => Process.comp

/-- The process that gives `b` whatever it reads. -/
def const (b : β) : Process α β where
  fn _ := b
  mono _ := Poset.refl b
  cont c := le_sup (c.map (fun _ => b) fun _ => Poset.refl b) 0

/-- The first of two channels. -/
def fst : Process (α × β) α where
  fn x := x.1
  mono h := h.1
  cont c := sup_le _ _ fun n => le_sup (c.map (fun x => x.1) fun h => h.1) n

/-- The second of two channels. -/
def snd : Process (α × β) β where
  fn x := x.2
  mono h := h.2
  cont c := sup_le _ _ fun n => le_sup (c.map (fun x => x.2) fun h => h.2) n

/-- Fan-out: `f` and `g` read the same input. -/
def pair (f : Process α β) (g : Process α γ) : Process α (β × γ) where
  fn x := (f x, g x)
  mono h := ⟨f.mono h, g.mono h⟩
  cont c := ⟨f.cont c, g.cont c⟩

/-- Side by side: `f` on the first channel, `g` on the second. -/
def prod {δ : Type x} [Domain δ] (f : Process α β) (g : Process γ δ) :
    Process (α × γ) (β × δ) :=
  pair (f ⊚ fst) (g ⊚ snd)

variable {ι : Type w} {κ : ι → Type v} [∀ i, Domain (κ i)]

/-- One process for each index, all reading the same input. -/
def pi (f : ∀ i, Process α (κ i)) : Process α (∀ i, κ i) where
  fn x i := f i x
  mono h i := (f i).mono h
  cont c i := (f i).cont c

/-- The channel at index `i`. -/
def proj (i : ι) : Process (∀ i, κ i) (κ i) where
  fn x := x i
  mono h := h i
  cont c := sup_le _ _ fun n => le_sup (c.map (fun x => x i) fun h => h i) n

/-! ## Feedback: the least fixed point -/

/-- `f` applied `n` times to nothing. -/
def iterate (f : Process α α) : Nat → α
  | 0 => bot
  | n + 1 => f (iterate f n)

theorem iterate_step (f : Process α α) : ∀ n, iterate f n ≤ iterate f (n + 1)
  | 0 => bot_le _
  | n + 1 => f.mono (iterate_step f n)

/-- The approximations of `f`'s least fixed point. -/
def approx (f : Process α α) : Chain α :=
  ⟨iterate f, iterate_step f⟩

/-- The least fixed point of `f` (Kleene). -/
def fix (f : Process α α) : α :=
  sup (approx f)

theorem iterate_le_fix (f : Process α α) (n : Nat) : iterate f n ≤ fix f :=
  le_sup (approx f) n

theorem fix_eq (f : Process α α) : f (fix f) = fix f := by
  apply Poset.antisymm
  · exact Poset.trans (f.cont (approx f)) <|
      sup_le _ _ fun n => le_sup (approx f) (n + 1)
  · refine sup_le _ _ fun n => ?_
    cases n with
    | zero => exact bot_le _
    | succ n => exact f.mono (iterate_le_fix f n)

theorem iterate_le {f : Process α α} {x : α} (h : f x ≤ x) : ∀ n, iterate f n ≤ x
  | 0 => bot_le x
  | n + 1 => Poset.trans (f.mono (iterate_le h n)) h

theorem fix_least (f : Process α α) {x : α} (h : f x ≤ x) : fix f ≤ x :=
  sup_le _ _ (iterate_le h)

end Process

end Kahn
