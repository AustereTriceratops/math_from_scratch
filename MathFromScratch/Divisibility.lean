import MathFromScratch.Basic
import MathFromScratch.Order

namespace math

def divides (a b : Nat) : Prop :=
  ∃ c, mul a c = b

theorem divides_trans (a b c : Nat) :
    divides a b → divides b c → divides a c := by
  unfold divides
  intro hab hbc
  rcases hab with ⟨n0, hab⟩
  rcases hbc with ⟨n1, hbc⟩
  rw [←hab] at hbc
  rw [mul_assoc] at hbc
  use (mul n0 n1)

theorem divides_additive (a b c : Nat) :
    divides a b → divides a c → divides a (add b c) := by
  unfold divides
  intro hab hac
  rcases hab with ⟨n0, hab⟩
  rcases hac with ⟨n1, hac⟩
  use (add n0 n1)
  rw [mul_add, hab, hac]

theorem divides_multiplicative (a b c : Nat) :
    divides a b → divides a (mul b c) := by
  unfold divides
  intro hab
  rcases hab with ⟨n, hab⟩
  use (mul n c)
  rw [← mul_assoc]
  rw [hab]

theorem everything_divides_zero (a : Nat) :
    divides a ,0 := by
  unfold divides
  use ,0
  rw [mul_zero]

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


theorem divides_implies_le (a b : Nat) :
    divides a b → LT ,0 b → LE a b := by
  unfold divides LT LE
  intro h_div hb
  rcases h_div with ⟨n, h_div⟩
  rcases n with _ | m
  . rcases hb with ⟨m, hb⟩
    rw [one_add_eq_succ] at hb
    rw [← hb] at h_div
    contradiction
  . rw [mul_succ, add_comm] at h_div
    use (mul a m)


-- def prime (p : Nat) : Prop :=
--   ∀ a : Nat, (LT a p) ∧ ¬(a = ,1)→ ¬(divides a p)

def prime (p : Nat) : Prop :=
    LT ,1 p ∧ (∀ a : Nat, divides a p → (a = p ∨ a = ,1))

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
