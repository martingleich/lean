variable {p q r : Prop}

theorem And.swap (h : p ∧ q) : (q ∧ p) := And.intro h.right h.left
theorem Or.swap (h : p ∨ q) : (q ∨ p) := h.elim Or.inr Or.inl

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := Iff.intro And.swap And.swap
example : p ∨ q ↔ q ∨ p := Iff.intro Or.swap Or.swap

theorem And.assoc_left (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) := ⟨h.left.left, ⟨h.left.right, h.right⟩⟩
theorem And.assoc_right (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := ⟨⟨h.left, h.right.left⟩, h.right.right⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro And.assoc_left And.assoc_right

theorem Or.assoc_left (h : (p ∨ q) ∨ r) : p ∨ (q ∨ r) := h.elim
        (fun hpq : p ∨ q =>
          hpq.elim Or.inl (fun hq => Or.inr (Or.inl hq)))
        (fun hr : r => Or.inr (Or.inr hr))
theorem Or.assoc_right (h : p ∨ (q ∨ r)) : (p ∨ q) ∨ r := h.elim
        (fun hp : p => Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          hqr.elim (fun hq : q => Or.inl (Or.inr hq)) Or.inr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := Iff.intro Or.assoc_left Or.assoc_right

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
  (fun h : p ∧ (q ∨ r) =>
    h.right.elim (fun hq => Or.inl (And.intro h.left hq)) (fun hr => Or.inr (And.intro h.left hr)))
  (fun h : (p ∧ q) ∨ (p ∧ r) =>
    h.elim (fun ⟨hp, hq⟩ => And.intro hp (Or.inl hq)) (fun ⟨hp, hr⟩ => And.intro hp (Or.inr hr)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := Iff.intro
  (fun h => h.elim
    (fun hp => And.intro (Or.inl hp) (Or.inl hp))
    (fun ⟨hq, hr⟩ => And.intro (Or.inr hq) (Or.inr hr)))
  (fun ⟨hpq, hqr⟩ => hqr.elim
    Or.inl
    (fun hr => hpq.elim
      Or.inl
      (fun hq => Or.inr (And.intro hq hr))))


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := Iff.intro
  (fun h ⟨hp, hq⟩ => h hp hq)
  (fun h hp hq => h ⟨hp, hq⟩)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := Iff.intro
  (fun h : (p ∨ q) → r =>
    have g : p → r := fun hp => h (Or.inl hp)
    have h : q → r := fun hq => h (Or.inr hq)
    And.intro g h
  )
  (fun (h : (p → r) ∧ (q → r)) (hpq : p ∨ q) => hpq.elim h.left h.right)
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := Iff.intro
  (fun h : ¬(p ∨ q) =>
    have hnp : p → False := fun hp => h (Or.inl hp)
    have hnq : q → False := fun hq => h (Or.inr hq)
    And.intro hnp hnq
  )
  (fun (⟨hnp, hnq⟩ : ¬p ∧ ¬q) (hpq : p ∨ q) => hpq.elim hnp hnq)

example : ¬p ∨ ¬q → ¬(p ∧ q) := fun (h : ¬p ∨ ¬q) (⟨hp, hq⟩ : p ∧ q) =>
  h.elim (fun np => np hp) (fun nq => nq hq)

example : ¬(p ∧ ¬p) := fun (⟨hp, hnp⟩ : p ∧ ¬p) => hnp hp

example : p ∧ ¬q → ¬(p → q) := fun (⟨hp, hnq⟩) (hpq) => hnq (hpq hp)
example : ¬p → (p → q) := fun (hnp) (hp) => False.elim (hnp hp)
example : (¬p ∨ q) → (p → q) := fun (hnp_or_q) (hp) => hnp_or_q.elim
 (fun hnp => False.elim (hnp hp))
  id
example : p ∨ False ↔ p := Iff.intro
  (fun hp_or_false => hp_or_false.elim id False.elim)
  Or.inl
example : p ∧ False ↔ False := Iff.intro And.right False.elim
example : (p → q) → (¬q → ¬p) := fun hpq hnq hp => hnq (hpq hp)

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := fun h => Or.elim (em q)
  (fun hq => Or.inl (fun _ => hq))
  (fun hnq => Or.inr (fun hp =>
    Or.elim (h hp) (fun hq => False.elim (hnq hq)) id))

example : ¬(p ∧ q) → ¬p ∨ ¬q := fun h => Or.elim (em q)
(fun hq => Or.inl (fun hp => h (And.intro hp hq)))
Or.inr

example : ¬(p → q) → p ∧ ¬q := fun h => Or.elim (em p)
(fun hp => Or.elim (em q) (fun hq => False.elim (h (fun _ => hq))) (fun hnq => And.intro hp hnq))
(fun hnp => have F : False := h (fun hp => False.elim (hnp hp))
False.elim F
)

def concat {α β γ : Type u} : (f : α → β) → (g : β → γ) → α → γ := λ f => λ g => λ x => g (f x)

example : (p → q) → (¬p ∨ q) := fun h => Or.elim (em p)
  (fun hp => Or.inr (h hp))
  Or.inl

example : (¬q → ¬p) → (p → q) := fun h => fun hp => Or.elim (em q)
  id
  (fun hnq =>
    suffices hnp : ¬p from absurd hp hnp
    h hnq)

example : p ∨ ¬p := em p
example : (((p → q) → p) → p) := fun h => Or.elim (em p)
id
(fun hnp => h (fun hp => absurd hp hnp))
