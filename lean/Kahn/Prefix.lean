import Kahn.Log

/-!
# Processes from finite prefixes

A function on finite lists that only adds to its output as its input grows (`Log.Extends`) gives a
process on logs (`Log.ofPrefix`): its output for a log is the limit of its outputs for the log's
finite prefixes, and for a finite log it is the function's output (`Log.ofPrefix_ofList`). So a rule
stated on what has been read so far, that only adds to its output as more is read, is a Kahn process.
-/

universe u v

namespace Kahn

open Domain

namespace Log

variable {α : Type u} {β : Type v}

/-- The messages at the first `k` positions of `s`, as a list. -/
def toList (s : Log α) : Nat → List α
  | 0 => []
  | k + 1 =>
    match s.get k with
    | some a => toList s k ++ [a]
    | none => toList s k

theorem toList_succ_some {s : Log α} {k : Nat} {a : α} (h : s.get k = some a) :
    toList s (k + 1) = toList s k ++ [a] := by
  show (match s.get k with | some a => toList s k ++ [a] | none => toList s k) = _
  rw [h]

theorem toList_succ_none {s : Log α} {k : Nat} (h : s.get k = none) :
    toList s (k + 1) = toList s k := by
  show (match s.get k with | some a => toList s k ++ [a] | none => toList s k) = _
  rw [h]

/-- A position before a filled one is filled. -/
theorem get_ne_none_of_le {s : Log α} {k : Nat} {a : α} (h : s.get k = some a) {j : Nat}
    (hj : j ≤ k) : s.get j ≠ none := by
  intro hn
  have : ∀ i, s.get (j + i) = none := by
    intro i
    induction i with
    | zero => exact hn
    | succ i ih => exact s.closed _ ih
  have h' := this (k - j)
  rw [show j + (k - j) = k by omega, h] at h'
  cases h'

/-- Position `n` of `toList s k`: what `s` holds there, if `n` is before `k`. -/
theorem getElem?_toList (s : Log α) (k n : Nat) :
    (toList s k)[n]? = if n < k then s.get n else none := by
  induction k generalizing n with
  | zero => simp [toList]
  | succ k ih =>
    cases hk : s.get k with
    | none =>
      rw [toList_succ_none hk, ih]
      by_cases h1 : n < k
      · simp [h1, show n < k + 1 by omega]
      · by_cases h2 : n = k
        · subst h2; simp [hk]
        · simp [h1, show ¬ n < k + 1 by omega]
    | some a =>
      have hlen : (toList s k).length = k := by
        apply Nat.le_antisymm
        · have := ih k
          simp only [Nat.lt_irrefl, ↓reduceIte] at this
          exact List.getElem?_eq_none_iff.mp this
        · cases k with
          | zero => exact Nat.zero_le _
          | succ k =>
            have hne := get_ne_none_of_le hk (show k ≤ k + 1 by omega)
            have := ih k
            simp only [show k < k + 1 by omega, ↓reduceIte] at this
            rw [← this] at hne
            have : ¬ (toList s (k + 1)).length ≤ k := fun h => hne (List.getElem?_eq_none_iff.mpr h)
            omega
      rw [toList_succ_some hk]
      by_cases h1 : n < k
      · rw [List.getElem?_append_left (by omega), ih]
        simp [h1, show n < k + 1 by omega]
      · by_cases h2 : n = k
        · have hc := List.getElem?_concat_length (l := toList s k) (a := a)
          rw [hlen] at hc
          rw [h2, hc]
          simp [hk]
        · rw [List.getElem?_append_right (by omega)]
          simp [show ¬ n < k + 1 by omega]
          omega

theorem ofList_toList_le (s : Log α) (k : Nat) : ofList (toList s k) ≤ s := by
  intro n a h
  have h' : (toList s k)[n]? = some a := h
  rw [getElem?_toList] at h'
  split at h'
  · exact h'
  · cases h'

theorem toList_step (s : Log α) (k : Nat) : ofList (toList s k) ≤ ofList (toList s (k + 1)) := by
  intro n a h
  have h' : (toList s k)[n]? = some a := h
  show (toList s (k + 1))[n]? = some a
  rw [getElem?_toList] at h' ⊢
  split at h'
  · simp only [show n < k + 1 by omega, ↓reduceIte]; exact h'
  · cases h'

theorem toList_le_of_le {s t : Log α} (h : s ≤ t) (k : Nat) :
    ofList (toList s k) ≤ ofList (toList t k) := by
  intro n a ha
  have ha' : (toList s k)[n]? = some a := ha
  show (toList t k)[n]? = some a
  rw [getElem?_toList] at ha' ⊢
  split at ha'
  · next hn => simp only [hn, ↓reduceIte]; exact h n a ha'
  · cases ha'

/-- The finite list `l`, read to its end, is `l`. -/
theorem toList_ofList (l : List α) : toList (ofList l) l.length = l := by
  apply List.ext_getElem?
  intro n
  rw [getElem?_toList]
  split
  · rfl
  · next hn =>
    show none = l[n]?
    exact (List.getElem?_eq_none_iff.mpr (by omega)).symm

/-- A function on finite lists that only adds to its output as its input grows. -/
def Extends (F : List α → List β) : Prop :=
  ∀ l l', ofList l ≤ ofList l' → ofList (F l) ≤ ofList (F l')

/-- The outputs of `F` for the finite prefixes of `s`, longer and longer. -/
def prefixChain (F : List α → List β) (hF : Extends F) (s : Log α) : Chain (Log β) :=
  ⟨fun k => ofList (F (toList s k)), fun k => hF _ _ (toList_step s k)⟩

/-- For each `k`, one stage of a chain holds everything its limit holds before position `k`. -/
theorem exists_stage (c : Chain (Log α)) (k : Nat) :
    ∃ i, ∀ n, n < k → ∀ a, (sup c).get n = some a → (c i).get n = some a := by
  induction k with
  | zero => exact ⟨0, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ k ih =>
    obtain ⟨i, hi⟩ := ih
    cases hk : (sup c).get k with
    | none =>
      refine ⟨i, fun n hn a ha => ?_⟩
      by_cases h : n < k
      · exact hi n h a ha
      · rw [show n = k by omega, hk] at ha; cases ha
    | some b =>
      obtain ⟨j, hj⟩ := (get_sup c k b).mp hk
      refine ⟨max i j, fun n hn a ha => ?_⟩
      by_cases h : n < k
      · exact c.mono (Nat.le_max_left i j) n a (hi n h a ha)
      · obtain rfl : n = k := by omega
        rw [hk] at ha
        cases ha
        exact c.mono (Nat.le_max_right i j) n b hj

/-- The process `F` gives on logs: for a log, the limit of its outputs for the log's finite prefixes. -/
noncomputable def ofPrefix (F : List α → List β) (hF : Extends F) : Process (Log α) (Log β) where
  fn s := sup (prefixChain F hF s)
  mono h := sup_mono fun k => hF _ _ (toList_le_of_le h k)
  cont c := by
    refine sup_le _ _ fun k => ?_
    obtain ⟨i, hi⟩ := exists_stage c k
    have hle : ofList (toList (sup c) k) ≤ ofList (toList (c i) k) := by
      intro n a ha
      have ha' : (toList (sup c) k)[n]? = some a := ha
      show (toList (c i) k)[n]? = some a
      rw [getElem?_toList] at ha' ⊢
      split at ha'
      · next hn => simp only [hn, ↓reduceIte]; exact hi n hn a ha'
      · cases ha'
    exact Poset.trans (hF _ _ hle) <|
      Poset.trans (le_sup (prefixChain F hF (c i)) k)
        (le_sup (c.map (fun s => sup (prefixChain F hF s)) _) i)

/-- What `ofPrefix F` gives at a position: what `F` gives there for some finite prefix. -/
theorem ofPrefix_get (F : List α → List β) (hF : Extends F) (s : Log α) (n : Nat) (b : β) :
    (ofPrefix F hF s).get n = some b ↔ ∃ k, (F (toList s k))[n]? = some b :=
  get_sup (prefixChain F hF s) n b

/-- For a finite log, `ofPrefix F` gives what `F` gives. -/
theorem ofPrefix_ofList (F : List α → List β) (hF : Extends F) (l : List α) :
    ofPrefix F hF (ofList l) = ofList (F l) := by
  apply Poset.antisymm
  · exact sup_le _ _ fun k => hF _ _ (ofList_toList_le (ofList l) k)
  · have := le_sup (prefixChain F hF (ofList l)) l.length
    simp only [prefixChain, toList_ofList] at this
    exact this

end Log

end Kahn
