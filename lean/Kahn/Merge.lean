import Kahn.Log

/-!
# Merging by arrival

Two writers into one log: the log holds their messages in the order they arrive. A merge by arrival
passes on a message once it has arrived, even while nothing has arrived from the other writer. With
one message from each writer it would then have to put both first, so no process merges by arrival.
A process can still merge by content: for example the left's first message, then the right's.
-/

universe u

namespace Kahn

open Domain

/-- No process merges two logs by arrival. If `f` passes on `a` when `a` is the only message, and `b`
when `b` is the only message, then with both arrived it would have to put both at position 0. -/
theorem no_arrival_merge {α : Type u} {a b : α} (hab : a ≠ b) (f : Process (Log α × Log α) (Log α))
    (hl : (f (Log.ofList [a], Log.empty)).get 0 = some a)
    (hr : (f (Log.empty, Log.ofList [b])).get 0 = some b) : False := by
  have h₁ := f.mono (pair_le (Poset.refl (Log.ofList [a])) (bot_le (Log.ofList [b]))) 0 a hl
  have h₂ := f.mono (pair_le (bot_le (Log.ofList [a])) (Poset.refl (Log.ofList [b]))) 0 b hr
  rw [h₁] at h₂
  exact hab (Option.some.inj h₂)

end Kahn
