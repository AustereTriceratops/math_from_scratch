import Mathlib

namespace math

inductive Nat: Type where
  | zero : Nat
  | succ : Nat → Nat

notation ",0" => Nat.zero
notation ",1" => Nat.succ Nat.zero
notation ",2" => Nat.zero.succ.succ

#check Nat.zero
#check Nat.succ

theorem Nat.induction
    {P: Nat → Prop}
    (hzero: P Nat.zero)
    (hsucc: ∀ n : Nat, P n → P (Nat.succ n))
    : ∀ n : Nat, P n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n hp => exact hsucc n hp


-- ADDITION
def add: Nat → Nat → Nat
  | n, .zero => n
  | n, .succ m => .succ (add n m)

theorem add_zero (n : Nat) :
    add n .zero = n := by
  rfl

theorem add_succ (n : Nat) :
    add n (.succ m) = .succ (add n m) := by
  rfl

----

theorem zero_add (n : Nat) :
    add ,0 n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- simp [add_succ]
    -- exact ih
    rw [add_succ]
    rw [ih]

theorem succ_add (n : Nat) :
    add (.succ n) m = .succ (add n m) := by
  induction m with
  | zero => apply add_zero
  -- | zero => rfl
  | succ m ih =>
    rw [add_succ]
    rw [ih]
    rfl

theorem add_comm (a b : Nat) :
    add a b = add b a := by
  induction a with
  | zero =>
    rw [zero_add]
    rfl
  | succ a ih =>
    rw [succ_add, add_succ]
    rw [ih]

theorem add_assoc (a b c : Nat) :
    add (add a b) c = add a (add b c) := by
  induction c with
  | zero =>
    apply add_zero
  | succ c ih =>
    simp [add_succ]
    exact ih
    -- rw [add_succ]
    -- rw [add_succ]
    -- rw [add_succ]
    -- rw [ih]

theorem add_one_eq_succ (n : Nat) :
    add n ,1 = n.succ := by
  rw [add_succ]
  rw [add_zero]

theorem one_add_eq_succ (n : Nat) :
    add ,1 n = n.succ := by
  rw [add_comm]
  rw [add_one_eq_succ]

theorem succ_eq_add_one (n : Nat) :
    n.succ = add n ,1 := by
  rw [add_one_eq_succ]

theorem succ_cancel (a b : Nat) :
    a.succ = b.succ → a = b := by
  intro h
  injection h

theorem succ_both_sides (a b : Nat) :
    a = b → a.succ = b.succ := by
  intro h
  rw [h]

theorem succ_eq (a b : Nat) :
    a = b → a.succ = b.succ := by
  intro h
  rw [h]

-- a + c = b + c implies a = b
theorem add_right_cancel (a b c : Nat) :
    add a c = add b c → a = b := by
  intro h
  induction c with
  | zero =>
    simp [add_zero] at h
    exact h
  | succ c ih =>
    rw [add_succ] at h
    rw [add_succ] at h
    simp at h
    exact ih h
    -- -- simp [add_succ] at h
    -- injection h with h_inj
    -- exact ih h_inj

theorem add_left_cancel (a b c : Nat) :
  add a b = add a c → b = c := by
  nth_rewrite 1 [add_comm]
  nth_rewrite 2 [add_comm]
  apply add_right_cancel

theorem add_right_cancel_to_zero (a b : Nat) :
    add a b = b → a = ,0 := by
  intro h
  induction b with
  | zero =>
      -- rw [← add_zero a]
      -- exact h
      rw [add_zero] at h
      exact h
  | succ n ih =>
      rw [add_succ] at h
      -- injection h with h
      simp at h
      exact ih h

theorem add_left_cancel_to_zero (a b : Nat) :
    add a b = a → b = ,0 := by
  rw [add_comm]
  apply add_right_cancel_to_zero


theorem succ_never_zero (a : Nat) :
  ¬(a.succ = ,0) := by
  intro h
  contradiction

theorem add_zero_eq_zero_implies_eq_zero (a: Nat) :
    add a .zero = .zero → a = .zero := by
    intro h
    rw [add_zero] at h
    exact h
  -- rw [add_zero]
  -- tauto

theorem add_eq_zero_implies_left_zero (a b : Nat) :
  add a b = .zero → a = .zero := by
  intro h
  induction b with
  | zero =>
    exact h
  | succ b ih =>
    cases h
  -- induction b with
  -- | zero =>
  --   apply add_zero_eq_zero_implies_eq_zero
  --   exact h
  -- | succ b ih =>    -- h and ih will be contradictory which means
  --   contradiction   -- that the goal can be proven by constructing False

theorem add_eq_zero_implies_right_zero (a b : Nat) :
  add a b = .zero → b = .zero := by
  rw [add_comm]
  apply add_eq_zero_implies_left_zero

-- theorem a_add_b_eq_zero_iff_both_zero (a b: Nat) :
--     add a b = .zero ↔ a = .zero ∧ b = .zero := by
--   constructor
--   . intro h
--   intro h
--   apply (a_add_zero_eq_zero_implies_a_eq_zero) at h
--   use h


-- MULTIPLICATION
def mul : Nat → Nat → Nat
  | _, .zero => .zero
  | n, .succ m => add (mul n m) n

theorem mul_zero (n : Nat) :
    mul n .zero = .zero := by
  rfl

theorem mul_succ (n m : Nat) :
    mul n (.succ m) = add (mul n m) n := by
  rfl

----

theorem zero_mul :
    mul .zero n = .zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [mul_succ]
    rw [add_zero]
    exact ih

theorem succ_mul (n m : Nat) :
    mul (.succ n) m = add (mul n m) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [mul_succ]
    rw [mul_succ]
    rw [ih]
    rw [add_succ]
    rw [add_succ]
    simp [add_assoc]
    simp [add_comm]

theorem one_mul (n : Nat) :
    mul ,1 n = n := by
  induction n with
  | zero => rfl
  -- | zero => rw [mul_zero]
  | succ n ih =>
    rw [mul_succ]
    rw [ih]
    rw [add_one_eq_succ]

theorem mul_one (n : Nat) :
    mul n ,1 = n := by
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]

-- distributivity: a*(b + c) = a*b + a*c
theorem mul_add (a b c : Nat) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [add_succ]
    rw [mul_succ]
    rw [ih]
    rw [mul_succ]
    rw [add_assoc]

-- associativity: (a * b) * c = a * (b * c)
theorem mul_assoc (a b c : Nat) :
    mul (mul a b) c = mul a (mul b c) := by
  induction c with
  | zero =>
    rfl
  | succ c ih =>
    rw [mul_succ]
    rw [mul_succ]
    rw[ih]
    rw [mul_add]

-- commutativity: a * b = b * a
theorem mul_comm (a b : Nat) :
    mul a b = mul b a := by
  induction b with
  | zero =>
    rw [zero_mul]
    rfl
  | succ b ih =>
    rw [mul_succ]
    rw [succ_mul]
    rw [ih]


theorem mul_succ_eq_zero_implies_zero (a b : Nat) :
    mul a b.succ = ,0 → a = ,0 := by
  sorry

theorem succ_mul_eq_zero_implies_zero (a b : Nat) :
    mul a.succ b = ,0 → b = ,0 := by
  sorry

theorem mul_eq_zero_implies_either_eq_zero (a b : Nat) :
    mul a b = ,0 → (a = ,0) ∨ (b = ,0) := by
  intro h
  sorry

theorem mul_eq_left_implies_right_eq_one (a b : Nat) :
    mul a b = a → ¬(a = ,0) → b = ,1 := by
  intro h ha
  cases b with
  | zero =>
    -- rw [mul_zero] at h
    -- rw [h] at ha
    -- contradiction
    tauto
  | succ b =>
    rw [mul_succ] at h
    apply add_right_cancel_to_zero at h
    cases a with
    | zero => contradiction
    | succ a =>
      -- apply succ_both_sides
      -- apply succ_mul_eq_zero_implies_zero a
      -- exact h
      have hb : b = ,0 := by
        apply succ_mul_eq_zero_implies_zero at h
        exact h
      rw [hb]


theorem mul_right_cancel (a b c : Nat) :
    mul a c = mul b c → ¬(c = ,0) → a = b := by
  intro h hc
  sorry
  -- cases c with
  -- | zero => contradiction
  -- | succ n =>
  --   induction n with
  --   | zero =>
  --     simp [mul_one] at h
  --     exact h
  --   | succ n ih =>



end math
