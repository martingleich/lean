-- Section 1 --
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := Iff.intro
(fun h => ⟨λ x => (h x).left, λ x => (h x).right ⟩)
(fun ⟨hp, hq⟩ x => ⟨hp x, hq x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := fun hapq hap x =>
  have hpq : p x → q x := hapq x
  have hp : p x := hap x
  hpq hp
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := fun h x => match h with
  |Or.inl hap => Or.inl (hap x)
  |Or.inr haq => Or.inr (haq x)

-- Section 2 --
variable (α : Type) (p q : α → Prop)

variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := fun a => Iff.intro
  (fun har => har a)
  (fun hr _ => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := Iff.intro
  (fun h => match Classical.em r with
    |Or.inl hr => Or.inr hr
    |Or.inr hnr => Or.inl (fun a => have k : p a ∨ r := h a
      match k with
      |Or.inl pa => pa
      |Or.inr hr => absurd hr hnr)
  )
  (fun h a => match h with
    |Or.inl hapa => Or.inl (hapa a)
    |Or.inr hr => Or.inr hr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

-- Section 3 --
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

theorem SelfContradiction {P : Prop} : (P ↔ ¬ P) → False := fun ⟨g, h⟩ => Or.elim (Classical.em P)
  (fun hp => (g hp) hp)
  (fun hnp => hnp (h hnp))

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := SelfContradiction (h barber)


-- Section 5 --
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

theorem by_contrapositive {P Q : Prop}: (¬ P → Q) → ¬ Q → P := (fun h => fun hnp => byContradiction
  (fun hnq => have p : Q := h hnq
    absurd p hnp))

theorem by_contrapositive2 {P Q : Prop}: (P → ¬ Q) → Q → ¬ P := (fun (h p q) => h q p)

def all_to_not_exists_not {α : Type} {p : α → Prop} : (∀ x, p x) → ¬ (∃ x, ¬ p x) :=
  (fun (all_p_w : ∀ (x : α), p x) (exists_not_p_w : ∃ x, ¬p x) => match exists_not_p_w with
  | ⟨w, not_p_w⟩ => have p_w : p w := all_p_w w
    absurd p_w not_p_w)
def not_exists_not_to_all {α : Type} {p : α → Prop} : ¬ (∃ x, ¬ p x) → (∀ x, p x) :=
 (fun (not_h : ¬ ∃ x, ¬p x) (a : α) => show p a from byContradiction
  (fun hnpa : ¬ p a => have h : ∃ x, ¬ p x := Exists.intro a hnpa
    absurd h not_h))

def exists_to_not_all_not {α:Type} {p : α → Prop} : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
  (fun (exists_x_with_property_p) (all_x_have_property_not_p) => match exists_x_with_property_p with
    | ⟨x, proof_of_p_x⟩ => have proof_of_not_p_x := all_x_have_property_not_p x
      absurd proof_of_p_x proof_of_not_p_x)
def not_all_not_to_exists {α:Type} {p : α → Prop} : ¬ (∀ x, ¬ p x) → (∃ x, p x)  :=
    by_contrapositive (show ¬ (∃ x, p x) → (∀ x, ¬ p x) from fun (ne) (x) (px) => ne ⟨x, px⟩)

def not_exists_to_all_not {α:Type}{p : α → Prop} : ¬ (∃ x, p x) → (∀ x, ¬ p x) :=
  fun (not_exists) (x) (p_x) => not_exists ⟨x, p_x⟩
def all_not_x_to_not_exists {α:Type}{p : α → Prop} : (∀ x, ¬ p x) → ¬ (∃ x, p x) :=
  fun (all_not_x) (⟨x, px⟩) => have not_p_x := all_not_x x
  absurd px not_p_x

def not_all_to_exists_not {α:Type}{p : α → Prop} : (¬ ∀ x, p x) → (∃ x, ¬ p x) :=
  by_contrapositive not_exists_not_to_all
def exists_not_to_not_all {α:Type}{p : α → Prop} : (∃ x, ¬ p x) → (¬ ∀ x, p x) :=
  by_contrapositive2 all_to_not_exists_not


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro all_to_not_exists_not not_exists_not_to_all
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro exists_to_not_all_not not_all_not_to_exists

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := Iff.intro not_exists_to_all_not all_not_x_to_not_exists
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := Iff.intro not_all_to_exists_not exists_not_to_not_all

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := Iff.intro
(fun (all_p_implies_r) ⟨x, p_x⟩ => show r from (all_p_implies_r x) p_x)
(fun x_with_px_implies_r x p_x => show r from x_with_px_implies_r ⟨x,p_x⟩)


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := Iff.intro
(fun ⟨x, p_implies_x⟩ all_p => p_implies_x (all_p x))
(fun (h) => show ∃ x, p x → r from byCases
    (fun hap : ∀ x, p x => ⟨a, fun _ => h hap⟩)
    (fun hnap : ¬ ∀ x, p x => byContradiction
      (fun hnex : ¬ ∃ x, p x → r =>
        have hap : ∀ x, p x :=
          fun x => byContradiction
            (fun hnp =>
              have hex : ∃ x, p x → r := ⟨x, fun hp => absurd hp hnp⟩
              absurd hex hnex
            )
       absurd hap hnap
       )
    )
)


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := Iff.intro
  (fun ⟨x, hrpx⟩ hr => ⟨x, show p x from hrpx hr⟩)
  (fun h => sorry)
