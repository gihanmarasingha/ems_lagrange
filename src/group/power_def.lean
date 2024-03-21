import tactic.basic group.basic

universe u

namespace exlean

open group

attribute [simp] mul_one one_mul

variables {G : Type u} [group G] {a b : G}

instance group.has_pow_Z [group G] : has_pow G ℤ := ⟨λ x n, gpow n x⟩

instance group.has_pow_N [group G] : has_pow G ℕ := ⟨λ x n, npow n x⟩

@[simp] lemma npow_eq_pow {M : Type*} [group M] (n : ℕ) (x : M) : npow n x = x^n := rfl

@[simp] theorem pow_zero (a : G) : a^0 = 1 := npow_zero' _

theorem pow_succ (a : G) (n : ℕ) : a^(n+1) = a * a^n :=
by { show npow n.succ a = a * (npow n a), rw npow_succ' }

end exlean