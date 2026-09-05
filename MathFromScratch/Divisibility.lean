import MathFromScratch.Basic
import MathFromScratch.Order

namespace math

def divides (a b : Nat) : Prop :=
  ∃ c, mul a c = b

theorem gt_divides (a b : Nat) :
    GT a b → ¬(divides a b) := by
  sorry

theorem zero_divides_only_zero (a : Nat) :
    divides ,0 a → a = ,0 := by
  unfold divides
  intro h
  rcases h with ⟨b, hb⟩
  rw [zero_mul] at hb
  rw [hb]


theorem one_divides_everything (a : Nat) :
    divides ,1 a := by
  unfold divides
  use a
  rw [one_mul]

theorem only_one_divides_consecutive (a b : Nat) :
    (divides a b) ∧ (divides a (add b ,1)) → a = ,1 := by
  sorry

def prime (p : Nat) : Prop :=
  ∀ a : Nat, (LT a p) ∧ ¬(a = ,1)→ ¬(divides a p)

-- def prime (p : Nat) : Prop :=
--     LT ,1 p ∧ (∀ a : Nat, divides a p → (a = p ∨ a = ,1))

theorem two_is_prime :
    prime (.succ (.succ .zero)) := by
  sorry
  -- unfold prime
  -- intro a ha hdiv



  -- constructor
  -- . apply LT_succ
  -- . intro a a_div_2
  --   have a_not_gt_2 : ¬GT a ,0.succ.succ


theorem three_is_prime :
    prime (.succ (.succ (.succ .zero))) := by
  sorry

theorem product_not_prime (a b : Nat):
    (LT ,1 a) ∧ (LT ,1 b) → ¬(prime (mul a b)) := by
  sorry
