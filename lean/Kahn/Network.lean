import Kahn.Process

/-!
# Networks

A network is a set of processes wired by channels. Kahn reads it as a system of equations, one for
each channel: what the channel carries is what the process writing it gives, from the channels it
reads. Wires may loop. The network's meaning is the least solution, and that meaning is again a
process from the network's inputs to its outputs (Kahn's theorem: the continuity proved in `solve`,
used by `Network.denote`): a network of components is itself a component.

This is what a network means. That the real components, run in any order, compute this least
solution is Kahn's result about running networks; it is assumed here, not proved.
-/

universe u v w

namespace Kahn

open Domain Process

variable {ι : Type u} {σ : Type v} {τ : Type w} [Domain ι] [Domain σ] [Domain τ]

/-- The equations with the inputs held at `i`. -/
def Process.curry (F : Process (ι × σ) σ) (i : ι) : Process σ σ where
  fn s := F (i, s)
  mono h := F.mono (pair_le (Poset.refl i) h)
  cont c := by
    let d : Chain (ι × σ) := c.map (fun s => (i, s)) fun h => pair_le (Poset.refl i) h
    have hd : ((i, sup c) : ι × σ) ≤ sup d :=
      pair_le (le_sup (d.map Prod.fst fun h => h.1) 0)
        (sup_le _ _ fun n => le_sup (d.map Prod.snd fun h => h.2) n)
    exact Poset.trans (F.mono hd) <| Poset.trans (F.cont d) <|
      sup_le _ _ fun n => le_sup (c.map (fun s => F (i, s)) fun h => F.mono (pair_le (Poset.refl i) h)) n

/-- The least solution of the equations `F`, for inputs `i`. -/
def solveFn (F : Process (ι × σ) σ) (i : ι) : σ :=
  fix (F.curry i)

theorem solveFn_eq (F : Process (ι × σ) σ) (i : ι) : F (i, solveFn F i) = solveFn F i :=
  fix_eq (F.curry i)

theorem solveFn_mono (F : Process (ι × σ) σ) {i j : ι} (h : i ≤ j) : solveFn F i ≤ solveFn F j :=
  fix_least (F.curry i) <|
    Poset.trans (F.mono (pair_le h (Poset.refl (solveFn F j))))
      (Poset.le_of_eq (solveFn_eq F j))

/-- The least solution, as a process of the inputs. -/
def solve (F : Process (ι × σ) σ) : Process ι σ where
  fn := solveFn F
  mono := solveFn_mono F
  cont c := by
    let X := sup (c.map (solveFn F) (solveFn_mono F))
    let d : Chain (ι × σ) :=
      ⟨fun n => (c n, solveFn F (c n)), fun n => pair_le (c.step n) (solveFn_mono F (c.step n))⟩
    refine fix_least (F.curry (sup c)) ?_
    show F (sup c, X) ≤ X
    have hd : ((sup c, X) : ι × σ) ≤ sup d :=
      pair_le (sup_le _ _ fun n => le_sup (d.map Prod.fst fun h => h.1) n)
        (sup_le _ _ fun n => le_sup (d.map Prod.snd fun h => h.2) n)
    refine Poset.trans (F.mono hd) (Poset.trans (F.cont d) ?_)
    · refine sup_le _ _ fun n => ?_
      show F (c n, solveFn F (c n)) ≤ X
      rw [solveFn_eq]
      exact le_sup (c.map (solveFn F) (solveFn_mono F)) n

/-- The solution solves the equations. -/
theorem solve_eq (F : Process (ι × σ) σ) (i : ι) : F (i, solve F i) = solve F i :=
  solveFn_eq F i

/-- It is the least solution: every other solution is above it. -/
theorem solve_least (F : Process (ι × σ) σ) (i : ι) {s : σ} (h : F (i, s) ≤ s) :
    solve F i ≤ s :=
  fix_least (F.curry i) h

/-- A Kahn network with inputs `ι`, wires `σ` and outputs `τ`. `wires` gives what every wire
carries, from the inputs and all the wires; `out` reads the outputs off them. -/
structure Network (ι : Type u) (σ : Type v) (τ : Type w) [Domain ι] [Domain σ] [Domain τ] where
  wires : Process (ι × σ) σ
  out : Process (ι × σ) τ

/-- The network as one process from its inputs to its outputs. That it is a process is Kahn's theorem,
proved by `solve`. -/
def Network.denote (N : Network ι σ τ) : Process ι τ :=
  N.out ⊚ Process.pair Process.id (solve N.wires)

end Kahn
