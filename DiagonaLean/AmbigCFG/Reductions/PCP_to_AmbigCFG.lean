/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.Computability.ContextFreeGrammar

import DiagonaLean.PCP.Basic
import DiagonaLean.AmbigCFG.Basic

@[expose] public section

variable {α : Type} [DecidableEq α]

namespace DiagonaLean.PCP

/-! ## Terminal and nonterminal alphabets -/

/-- The terminal alphabet for a PCP instance `P`:
    original symbols `α` together with one index token `aᵢ` per tile. -/
abbrev PCPAlpha (P : Stack α) : Type := Sum α (Fin P.length)

/-- Nonterminals of the combined PCP grammar.
    - `S` : fresh start symbol
    - `A` : generates encodings driven by the **top** words
    - `B` : generates encodings driven by the **bot** words -/
inductive PCPNonterm | S | A | B
  deriving DecidableEq, Fintype, Repr

/-! ## Building right-hand sides -/

/-- Inject a word over `α` into terminal symbols of `PCPAlpha P`. -/
def liftWord {P : Stack α} (w : Word α) : List (Symbol (PCPAlpha P) PCPNonterm) :=
  w.map (Symbol.terminal ∘ Sum.inl)

/-- The index terminal `aᵢ` for tile `i`. -/
abbrev idxSym {P : Stack α} (i : Fin P.length) : Symbol (PCPAlpha P) PCPNonterm :=
  Symbol.terminal (Sum.inr i)

/-! ## Individual productions -/

/-- Recursive production  `v → w · v · aᵢ`. -/
def recProd (v : PCPNonterm) {P : Stack α} (i : Fin P.length) (w : Word α) :
    ContextFreeRule (PCPAlpha P) PCPNonterm where
  input  := v
  output := liftWord w ++ [Symbol.nonterminal v, idxSym i]

/-- Base production  `v → w · aᵢ`. -/
def baseProd (v : PCPNonterm) {P : Stack α} (i : Fin P.length) (w : Word α) :
    ContextFreeRule (PCPAlpha P) PCPNonterm where
  input  := v
  output := liftWord w ++ [idxSym i]

/-! ## Rule sets -/

/-- For each tile `i`:  `A → top(i) · A · aᵢ`  and  `A → top(i) · aᵢ`. -/
def rulesA (P : Stack α) : Finset (ContextFreeRule (PCPAlpha P) PCPNonterm) :=
  Finset.univ.biUnion fun i : Fin P.length =>
    {recProd PCPNonterm.A i P[i].top, baseProd PCPNonterm.A i P[i].top}

/-- For each tile `i`:  `B → bot(i) · B · aᵢ`  and  `B → bot(i) · aᵢ`. -/
def rulesB (P : Stack α) : Finset (ContextFreeRule (PCPAlpha P) PCPNonterm) :=
  Finset.univ.biUnion fun i : Fin P.length =>
    {recProd PCPNonterm.B i P[i].bot, baseProd PCPNonterm.B i P[i].bot}

/-- Start productions:  `S → A`  and  `S → B`. -/
def rulesS (P : Stack α) : Finset (ContextFreeRule (PCPAlpha P) PCPNonterm) :=
  { ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.A]⟩,
    ⟨PCPNonterm.S, [Symbol.nonterminal PCPNonterm.B]⟩ }

/-- The grammar `G(P)` for a PCP instance `P`.

    `LA` consists of strings of the form  `τ₁(A) ++ aᵢₘ … aᵢ₁`
    and `LB` of strings of the form       `τ₂(A) ++ aᵢₘ … aᵢ₁`
    for a common reversed index sequence.  A string lies in `LA ∩ LB`
    iff the tiles `i₁, …, iₘ` form a PCP solution.
    Such a string has two parse trees from `S` (one via `A`, one via `B`),
    so:

    **`G(P).Ambiguous ↔ HasSolution P`**  (proved separately) -/
def Stack.toGrammar (P : Stack α) : ContextFreeGrammar (PCPAlpha P) where
  NT      := PCPNonterm
  initial := PCPNonterm.S
  rules   := rulesS P ∪ rulesA P ∪ rulesB P

end DiagonaLean.PCP

namespace DiagonaLean.AmbigCFG.Reduction
open DiagonaLean.PCP DiagonaLean.AmbigCFG

theorem pcp_iff_ambigcfg (P : Stack α) :
    HasSolution P ↔ (P.toGrammar).Ambiguous := by sorry

end DiagonaLean.AmbigCFG.Reduction
