/-
# Lagrange's theorem
-/

import modules

open_locale coset

open set function subgroup 



/-
## Working with subgroups:

Let `H` be a subgroup of `G`. Then we have

`one_mem : (1 : G) ∈ H`
`mul_mem:  a ∈ H → b ∈ H → a * b ∈ H`
`inv_mem : a ∈ H → a⁻¹ ∈ H`

For example, suppose `G` is a group, and `H` is a subgroup of `G`.
-/

variables {G : Type*} [group G] (H : subgroup G)

/-
We have:
-/

example : (1 : G) ∈ H :=
begin
  from H.one_mem,
end

example (a b : G) (h₁ : a ∈ H) (h₂ : b ∈ H) : a * b ∈ H :=
begin
  from H.mul_mem h₁ h₂,
end

example (a b : G) (h₁ : a ∈ H) : a⁻¹ ∈ H :=
begin
  sorry,
end

-- Try `apply H.mul_mem` for the first line in the next example.

example (a b : G) (h₁ : a ∈ H) : (a * b) * a⁻¹ ∈ H :=
begin
  sorry,
end

namespace exlean

-- We prove an *if and only if* result. Use the `split` tactic.

lemma mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H :=
begin
  sorry,
end

/-
## Cosets

If `a : G` and `H` is a subgroup of `G`, then the left coset of `H` by `a` is the set
`a *l H = {a * h | h ∈ H}`.
-/

lemma mem_left_coset_iff {x : G} (a : G) : x ∈ a *l H ↔ a⁻¹ * x ∈ H :=
begin
  split,
  { intro h,
    obtain ⟨h', hh', rfl⟩ := h,
    simpa, },
  { intro h, 
    use a⁻¹ * x,
    simpa, }
end


lemma left_coset_mem_left_coset {a : G} (ha : a ∈ H) : a *l H = H :=
begin
  ext,
  split,
  { intro h,
    sorry },
  { sorry, },
end

lemma eq_of_non_empty_intersection {a b x : G} : x ∈ (a *l H) ∩ (b*l H) → a *l H = b *l H :=
begin
  sorry,
end


end exlean