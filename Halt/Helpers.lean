import Mathlib.Logic.Relation

namespace Halt.Helpers

lemma reflTransGen_diamond {α : Type*} {r : α → α → Prop}
    (h_det : ∀ {a b c : α}, r a b → r a c → b = c) {a b c : α}
    (hab : Relation.ReflTransGen r a b)
    (hac : Relation.ReflTransGen r a c) :
    Relation.ReflTransGen r b c ∨ Relation.ReflTransGen r c b := by
  induction hab with
  | refl => grind
  | @tail b_int b_end h_rest h_step ih =>
    cases ih with
    | inr h_c_b_int => grind
    | inl h_b_int_c =>
      rcases h_b_int_c.cases_head with h_eq | ⟨x, h_b_int_x, h_x_c⟩ <;> grind

end Halt.Helpers
