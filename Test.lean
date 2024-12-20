-- This module serves as the root of the `Test` library.
-- Import modules here that should be built as part of the library.
import Test.Basic

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
 fun h : ∀ x : α, p x ∧ q x =>
 fun y : α =>
 show p y from (h y).left

#check Eq.refl    -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
#check Eq.symm    -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a
#check Eq.trans   -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
