/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Cslib.Turing SingleTapeTM

namespace DiagonaLean.Halt.Encoding

/- From Hopcroft et al.'s textbook: δ(qi, Xj ) = (qk, Xl, Dm), for some integers i, j , k, l, and
m. We shall code this rule by the string 0i 10j 10k 10l 10m. Notice that, since all of i, j , k, l,
and m are at least one, there are no occurrences of two or more consecutive 1's within the code for
a single transition. A code for the entire TM M consists of all the codes for the transitions, in
some order, separated by pairs of 1's: C1 11 C2 11 ... 11 Cn-1 11Cn. We shall assume the states are
q1,...,  qr for some r. The start state will always be q1, and q2 will be the only accepting state.
Note that, since we may assume the TM halts whenever it enters an accepting state, there is never
any need for more than one accepting state. We shall assume the tape symbols are X1,... , Xs for
some s. X1 always will be the symbol 0, X2 will be 1, and X3 will be ⊔, the blank. However, other
tape symbols can be assigned to the remaining integers arbitrarily. We shall refer to direction L as
D1 and direction R as D2. The encoding is an injection. -/

def encodeNat (n : ℕ) : List Bool := List.replicate n false

@[simp]
lemma encodeNat_zero : encodeNat 0 = [] := rfl

@[simp]
lemma encodeNat_succ (n : ℕ) :
    encodeNat (n + 1) = false :: encodeNat n := by simp [encodeNat, List.replicate_succ]

def decodeNat (l : List Bool) : Option ℕ :=
  if l.all (· == false) then some l.length
  else none

@[simp]
lemma decodeNat_encodeNat (n : ℕ) : decodeNat (encodeNat n) = n := by
  simp [decodeNat, encodeNat, List.all_replicate, List.length_replicate]

def encodePair (a b : List Bool) : List Bool :=
  a ++ [true, true] ++ b

/-- The binary string `w` is the binary number `[1w]_2 ∈ ℕ`. -/
def enumeratedBinaryString (w : List Bool) : ℕ :=
  w.foldl (fun acc b => acc * 2 + if b then 1 else 0) 1

def unenumeratedBinaryString (n : ℕ) : List Bool := ((Nat.bits n).reverse).tail

private lemma foldl_eq (w : List Bool) (k : ℕ) :
    w.foldl (fun acc b => acc * 2 + if b then 1 else 0) k =
    k * 2 ^ w.length +
      w.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0 := by
  induction w generalizing k with
  | nil => simp
  | cons hd tl ih =>
    simp [List.foldl]
    have ih' := ih (if hd then 1 else 0)
    specialize ih (k * 2 + if hd then 1 else 0)
    rw [ih, ih']
    ring

noncomputable def symbolIdx [DecidableEq Symbol] (s : Option Symbol) : ℕ :=
  match s with
  | none   => 1
  | some s => (Fintype.equivFin Symbol s).val + 2

def dirIdx (d : Option Turing.Dir) : ℕ :=
  match d with
  | some Turing.Dir.left  => 1
  | some Turing.Dir.right => 2
  | none           => 3

def boolSymbolIdx (s : Option Bool) : ℕ :=
  match s with
  | some false => 1  -- X1 = 0
  | some true  => 2  -- X2 = 1
  | none       => 3  -- X3 = blank

noncomputable def boolStateIdx (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) : ℕ :=
  if q == tm.q₀ then 1
  else Finset.univ.toList.findIdx (· == q) + 2

noncomputable def encodeBoolTransition (tm : SingleTapeTM Bool) [DecidableEq tm.State]
    (q : tm.State) (x : Option Bool)
    (stmt : SingleTapeTM.Stmt Bool) (q' : tm.State) : List Bool :=
  let i := boolStateIdx tm q
  let j := boolSymbolIdx x
  let k := boolStateIdx tm q'
  let l := boolSymbolIdx stmt.symbol
  let m := dirIdx stmt.movement
  encodeNat i ++ [true] ++
  encodeNat j ++ [true] ++
  encodeNat k ++ [true] ++
  encodeNat l ++ [true] ++
  encodeNat m

noncomputable def encodeBoolTr (tm : SingleTapeTM Bool) [DecidableEq tm.State] : List Bool :=
  let states := (@Finset.univ tm.State tm.stateFintype).toList
  let pairs := states ×ˢ [none, some false, some true]
  let encoded := pairs.filterMap (fun ⟨q, x⟩ =>
    match tm.tr q x with
    | (stmt, some q') => some (encodeBoolTransition tm q x stmt q')
    | (_, none)       => none
  )
  List.intercalate [true, true] encoded

noncomputable def encodeBoolTM (tm : SingleTapeTM Bool) [DecidableEq tm.State] : List Bool :=
  encodeNat (Fintype.card tm.State) ++ List.replicate 3 true ++ encodeBoolTr tm

end DiagonaLean.Halt.Encoding
