import MathFromScratch.Basic

namespace math

-- ORDERING
def LE (a b : Nat) : Prop :=
  ∃x : Nat, add a x = b

def LT (a b : Nat) : Prop :=
  LE a.succ b

def GE (a b : Nat) : Prop :=
  ∃x: Nat, a = add b x

def GT (a b : Nat) : Prop :=
  GE a b.succ

---


-- less than or equal (le)
theorem le_refl (a : Nat) :
    LE a a := by
  unfold LE
  use .zero
  rw [add_zero]

theorem le_trans (a b c : Nat) :
    LE a b → LE b c → LE a c := by
  unfold LE
  intro hab hbc
  rcases hab with ⟨n_0, hab⟩
  rcases hbc with ⟨n_1, hbc⟩
  use (add n_0 n_1)
  rw [← hab] at hbc
  rw [add_assoc] at hbc
  exact hbc

theorem le_add_right_cancel (a b c : Nat) :
    LE (add a c) (add b c) → LE a b := by
  unfold LE
  intro h
  rcases h with ⟨n_0, h⟩
  use n_0
  rw [add_assoc] at h
  nth_rw 2 [add_comm] at h
  rw [← add_assoc] at h
  apply (add_right_cancel (add a n_0) b c)
  exact h

theorem le_add_left_cancel (a b c : Nat) :
    LE (add c a) (add c b) → LE a b := by
  nth_rw 1 [add_comm]
  nth_rw 2 [add_comm]
  apply le_add_right_cancel

theorem le_zero_eq_zero (a : Nat) :
    LE a ,0 → a = ,0 := by
  unfold LE
  intro h
  rcases h with ⟨b, hb⟩
  exact add_eq_zero_implies_left_zero a b hb

theorem left_add_le_sum (a b : Nat) :
    LE a (add a b) := by
  unfold LE
  use b

theorem right_add_le_sum (a b : Nat) :
    LE b (add a b) := by
  unfold LE
  use a
  rw [add_comm]


-- less than (lt)

theorem lt_add_right_cancel (a b c : Nat) :
    LT (add a c) (add b c) → LT a b := by
  unfold LT
  rw [add_comm]
  rw [← add_succ]
  rw [add_comm]
  apply le_add_right_cancel

theorem lt_succ (a : Nat) :
    LT a (.succ a) := by
  unfold LT LE
  use ,0
  rw [add_zero]

-- theorem never_lt_zero (a : Nat) :
--     ¬(LT a ,0) := by
--   unfold LT LE
--   intro h

end math
