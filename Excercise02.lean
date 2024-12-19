

-- Section 5--
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := fun h => match h with
  | ⟨_, hw⟩ => hw
example (a : α) : r → (∃ x : α, r) := fun hr => Exists.intro a hr
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := Iff.intro
  (fun h : (∃ x, p x ∧ r) => match h with
    | ⟨w, ⟨hpw, hr⟩⟩ => And.intro (Exists.intro w hpw) hr)
  (fun h : (∃ x, p x) ∧ r => match h with
    | ⟨⟨w, hpw⟩, hr⟩ => Exists.intro w (And.intro hpw hr))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := Iff.intro
  (fun h => match h with
    | ⟨w, hw⟩ => hw.elim
      (fun hp : p w => Or.inl (Exists.intro w hp))
      (fun hq : q w => Or.inr (Exists.intro w hq)))
  (fun h => h.elim
   (fun hp : ∃ x, p x => match hp with | ⟨w, hw⟩ => Exists.intro w (Or.inl hw))
    fun hq : ∃ x, q x => match hq with | ⟨w, hw⟩ => Exists.intro w (Or.inr hw))

theorem A : (y : α) → (∀ x : α, p x) → (¬ ∀ x, ¬ p x) := fun (x) (all_x) (all_not_x) => have p_x := all_x x
  have not_p_x := all_not_x x
  absurd p_x not_p_x

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
 (fun (all_p_w : ∀ (x : α), p x) (exists_not_p_w : ∃ x, ¬p x) => match exists_not_p_w with
 | ⟨w, not_p_w⟩ => have p_w : p w := all_p_w w
  absurd p_w not_p_w)
 (fun (not_h : ¬ ∃ x, ¬p x) (a : α) => show p a from byContradiction
  (fun hnpa : ¬ p a => have h : ∃ x, ¬ p x := Exists.intro a hnpa
    absurd h not_h))

theorem by_contrapositive {P Q : Prop}: (¬ Q → P) → ¬ P → Q := (fun h => fun hnp => byContradiction
  (fun hnq => have p : P := h hnq
    absurd p hnp))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro
  -- Forward direction
  (fun (exists_x_with_property_p) (all_x_have_property_not_p) => match exists_x_with_property_p with
    | ⟨x, proof_of_p_x⟩ => have proof_of_not_p_x := all_x_have_property_not_p x
      absurd proof_of_p_x proof_of_not_p_x
  )
  -- Backward direction
  ( -- Proof the contrapositive
    by_contrapositive (show ¬ (∃ x, p x) → (∀ x, ¬ p x) from fun (ne) (x) (px) => ne ⟨x, px⟩)
  )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
