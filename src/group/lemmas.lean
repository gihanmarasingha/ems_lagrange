import group.power_def

namespace exlean

open group

variables {G: Type* } [group G] (a b c : G) {n m : ℕ} -- hide

lemma pow_one : a ^ 1 = a := by rw [pow_succ, pow_zero, mul_one]

lemma one_pow : (1 : G) ^ n = 1 :=
begin
  induction n with k ih,
  { rw pow_zero, },
  { rw [pow_succ, one_mul, ih], },
end

lemma pow_succ' (a : G) (n : ℕ) : a ^ (n+1) = a ^ n * a :=
begin
  induction n with k ih,
  { rw [pow_one, pow_zero, one_mul], },
  { calc
    a ^ ((k + 1) + 1)
        = a * a ^ (k + 1)     : by rw pow_succ
    ... = a * (a ^ k * a)     : by rw ih
    ... = (a * a ^ k) * a     : by rw mul_assoc
    ... = (a ^ (k + 1)) * a   : by rw pow_succ },
end

end exlean