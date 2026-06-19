/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import Mathlib.Data.Set.Basic

@[expose] public section

namespace Halt.Diagonal

/-- **Cantor's diagonal lemma.** For any uniform family of Boolean
functions `f : α → α → Bool`, the function `fun a => !f a a` differs
from each `f a` at the input `a`, so it is not equal to any `f a`. -/
theorem cantor_diag {α : Type*} (f : α → α → Bool) :
    ∃ g : α → Bool, ∀ a, g ≠ f a := by
  refine ⟨fun a => !f a a, ?_⟩
  intro a h
  have hcontr : (! f a a) = f a a := congrFun h a
  exact (Bool.not_ne_self _) hcontr

/-- **Cantor's theorem**: there is no surjection from a type onto its
Boolean power-set (`α → α → Bool`). -/
theorem not_surjective_cantor {α : Type*} (f : α → α → Bool) :
    ¬ Function.Surjective f := by
  intro hsurj
  obtain ⟨g, hg⟩ := cantor_diag f
  obtain ⟨a, ha⟩ := hsurj g
  exact hg a ha.symm

/-- A general "no fixpoint" form of the diagonal argument: if `flip` is
a `Bool`-toggle (no fixed point), then `f` cannot satisfy
`f a a = flip (f a a)` for any `a`. The Halting Problem's diagonal
function arises by setting `flip = Bool.not`. -/
theorem no_self_fixpoint_of_flip {α : Type*}
    {flip : Bool → Bool} (hflip : ∀ b, flip b ≠ b)
    (f : α → α → Bool) (a : α) :
    f a a ≠ flip (f a a) := by
  intro h
  exact hflip (f a a) h.symm

theorem halt_diag_contradiction {α : Type*} (H : α → α → Bool)
    (d : α) (hd : (! H d d) = H d d) : False :=
  Bool.not_ne_self _ hd

end Halt.Diagonal

