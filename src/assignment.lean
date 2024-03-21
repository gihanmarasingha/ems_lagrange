/-
# Lagrange's theorem
-/

import modules

open_locale coset

open set function subgroup 

variables {G : Type*} [group G] (H : subgroup G)

/-
## Useful results:

Let `H` be a subgroup of `G`. Then we have

`mul_mum:  a ∈ H → b ∈ H → a * b ∈ H`
`inv_mul : a ∈ H → a⁻¹ ∈ H`

-/

namespace exlean

lemma mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H :=
begin
  sorry,
end

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