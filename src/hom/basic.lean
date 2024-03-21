import group.lemmas data.fun_like.basic

namespace exlean

variables {G : Type*} {H : Type*} [group G] [group H]

structure hom (G : Type*) (H : Type*) [group G] [group H] :=
(to_fun : G → H)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

class hom_class (F : Type*) (M N : out_param $ Type*)
  [group M] [group N] extends fun_like F M (λ _, N) :=
(map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y)

instance hom.hom_class : hom_class (hom G H) G H :=
{ coe := hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := hom.map_mul' }

end exlean