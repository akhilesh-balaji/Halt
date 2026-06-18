import Cslib.Computability.Machines.SingleTapeTuring.Basic
import Halt.Encoding

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Turing SingleTapeTM Halt.Encoding

namespace Halt

/-- Halts at `state=none`. -/
def Halts (tm : SingleTapeTM Symbol) (w : List Symbol) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.ReflTransGen tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩

/-- Halts within `n` steps. -/
def HaltsWithinTime (tm : SingleTapeTM Symbol) (w : List Symbol) (n : ℕ) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.RelatesWithinSteps tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩ n

/-- Halts within `n` steps iff halts. -/
theorem halts_iff_exists_n_haltsWithinTime (tm : SingleTapeTM Symbol)
    (w : List Symbol) :
    Halts tm w ↔ ∃ n, HaltsWithinTime tm w n := by
  constructor
  · rintro ⟨tape, h⟩
    obtain ⟨n, hn⟩ := h.relatesInSteps
    exact ⟨n, tape, .of_relatesInSteps hn⟩
  · rintro ⟨n, tape, m, _, hm⟩
    exact ⟨tape, hm.reflTransGen⟩

/- Define encodings first -/

/-- **`HaltDecidable Symbol`** holds iff some Bool-valued function on
`SingleTapeTM Symbol × List Symbol` decides `Halts`. Vacuously true
classically; included for contrast with the strict forms below. -/
def HaltDecidable (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] : Prop :=
  ∃ decide : SingleTapeTM Symbol → List Symbol → Bool,
    ∀ tm w, decide tm w = true ↔ Halts tm w

def IsHaltDecider (D : SingleTapeTM Bool) : Prop :=
  ∀ (tm : SingleTapeTM Bool) [DecidableEq tm.State] (w : List Bool),
    (Halts tm w →
      SingleTapeTM.Outputs D (encodePair (encodeBoolTM tm) w) [true]) ∧
    (¬ Halts tm w →
      SingleTapeTM.Outputs D (encodePair (encodeBoolTM tm) w) [false])

def IsSelfHaltDecider (D : SingleTapeTM Bool) : Prop :=
  ∀ (tm : SingleTapeTM Bool) [DecidableEq tm.State],
    (Halts tm (encodeBoolTM tm) →
      SingleTapeTM.Outputs D (encodeBoolTM tm) [true]) ∧
    (¬ Halts tm (encodeBoolTM tm) →
      SingleTapeTM.Outputs D (encodeBoolTM tm) [false])

/-- **The Halting Problem is undecidable**: no `SingleTapeTM Bool` can
decide the self-halt problem `K`. -/
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D := by sorry

end Halt

