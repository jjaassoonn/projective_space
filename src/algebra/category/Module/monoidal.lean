/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import category_theory.monoidal.braided
import algebra.category.Module.basic
import linear_algebra.tensor_product

/-!
# The symmetric monoidal category structure on R-modules

Mostly this uses existing machinery in `linear_algebra.tensor_product`.
We just need to provide a few small missing pieces to build the
`monoidal_category` instance and then the `symmetric_category` instance.

If you're happy using the bundled `Module R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

universes u

open category_theory

namespace Module

variables {R : Type u} [comm_ring R]

namespace monoidal_category
-- The definitions inside this namespace are essentially private.
-- After we build the `monoidal_category (Module R)` instance,
-- you should use that API.

open_locale tensor_product
local attribute [ext] tensor_product.ext

/-- (implementation) tensor product of R-modules -/
def tensor_obj (M N : Module R) : Module R := Module.of R (M ā[R] N)
/-- (implementation) tensor product of morphisms R-modules -/
def tensor_hom {M N M' N' : Module R} (f : M ā¶ N) (g : M' ā¶ N') :
  tensor_obj M M' ā¶ tensor_obj N N' :=
tensor_product.map f g

lemma tensor_id (M N : Module R) : tensor_hom (š M) (š N) = š (Module.of R (ā„M ā ā„N)) :=
by tidy

lemma tensor_comp {Xā Yā Zā Xā Yā Zā : Module R}
  (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā) (gā : Yā ā¶ Zā) (gā : Yā ā¶ Zā) :
    tensor_hom (fā ā« gā) (fā ā« gā) = tensor_hom fā fā ā« tensor_hom gā gā :=
by tidy

/-- (implementation) the associator for R-modules -/
def associator (M N K : Module R) : tensor_obj (tensor_obj M N) K ā tensor_obj M (tensor_obj N K) :=
linear_equiv.to_Module_iso (tensor_product.assoc R M N K)

section

/-! The `associator_naturality` and `pentagon` lemmas below are very slow to elaborate.

We give them some help by expressing the lemmas first non-categorically, then using
`convert _aux using 1` to have the elaborator work as little as possible. -/

open tensor_product (assoc map)

private lemma associator_naturality_aux
  {Xā Xā Xā : Type*}
  [add_comm_monoid Xā] [add_comm_monoid Xā] [add_comm_monoid Xā]
  [module R Xā] [module R Xā] [module R Xā]
  {Yā Yā Yā : Type*}
  [add_comm_monoid Yā] [add_comm_monoid Yā] [add_comm_monoid Yā]
  [module R Yā] [module R Yā] [module R Yā]
  (fā : Xā āā[R] Yā) (fā : Xā āā[R] Yā) (fā : Xā āā[R] Yā) :
  (ā(assoc R Yā Yā Yā) āā (map (map fā fā) fā)) = ((map fā (map fā fā)) āā ā(assoc R Xā Xā Xā)) :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  refl
end

variables (R)

private lemma pentagon_aux
  (W X Y Z : Type*)
  [add_comm_monoid W] [add_comm_monoid X] [add_comm_monoid Y] [add_comm_monoid Z]
  [module R W] [module R X] [module R Y] [module R Z] :
  ((map (1 : W āā[R] W) (assoc R X Y Z).to_linear_map).comp (assoc R W (X ā[R] Y) Z).to_linear_map)
    .comp (map ā(assoc R W X Y) (1 : Z āā[R] Z)) =
  (assoc R W X (Y ā[R] Z)).to_linear_map.comp (assoc R (W ā[R] X) Y Z).to_linear_map :=
begin
  apply tensor_product.ext_fourfold,
  intros w x y z,
  refl
end

end

lemma associator_naturality {Xā Xā Xā Yā Yā Yā : Module R}
  (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā) :
    tensor_hom (tensor_hom fā fā) fā ā« (associator Yā Yā Yā).hom =
    (associator Xā Xā Xā).hom ā« tensor_hom fā (tensor_hom fā fā) :=
by convert associator_naturality_aux fā fā fā using 1

lemma pentagon (W X Y Z : Module R) :
  tensor_hom (associator W X Y).hom (š Z) ā« (associator W (tensor_obj X Y) Z).hom
  ā« tensor_hom (š W) (associator X Y Z).hom =
    (associator (tensor_obj W X) Y Z).hom ā« (associator W X (tensor_obj Y Z)).hom :=
by convert pentagon_aux R W X Y Z using 1

/-- (implementation) the left unitor for R-modules -/
def left_unitor (M : Module.{u} R) : Module.of R (R ā[R] M) ā M :=
(linear_equiv.to_Module_iso (tensor_product.lid R M) : of R (R ā M) ā of R M).trans (of_self_iso M)

lemma left_unitor_naturality {M N : Module R} (f : M ā¶ N) :
  tensor_hom (š (Module.of R R)) f ā« (left_unitor N).hom = (left_unitor M).hom ā« f :=
begin
  ext x y, simp,
  erw [tensor_product.lid_tmul, tensor_product.lid_tmul],
  rw linear_map.map_smul,
  refl,
end

/-- (implementation) the right unitor for R-modules -/
def right_unitor (M : Module.{u} R) : Module.of R (M ā[R] R) ā M :=
(linear_equiv.to_Module_iso (tensor_product.rid R M) : of R (M ā R) ā of R M).trans (of_self_iso M)

lemma right_unitor_naturality {M N : Module R} (f : M ā¶ N) :
  tensor_hom f (š (Module.of R R)) ā« (right_unitor N).hom = (right_unitor M).hom ā« f :=
begin
  ext x y, simp,
  erw [tensor_product.rid_tmul, tensor_product.rid_tmul],
  rw linear_map.map_smul,
  refl,
end

lemma triangle (M N : Module.{u} R) :
  (associator M (Module.of R R) N).hom ā« tensor_hom (š M) (left_unitor N).hom =
    tensor_hom (right_unitor M).hom (š N) :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  change R at y,
  dsimp [tensor_hom, associator],
  erw [tensor_product.lid_tmul, tensor_product.rid_tmul],
  exact (tensor_product.smul_tmul _ _ _).symm
end

end monoidal_category

open monoidal_category

instance monoidal_category : monoidal_category (Module.{u} R) :=
{ -- data
  tensor_obj   := tensor_obj,
  tensor_hom   := @tensor_hom _ _,
  tensor_unit  := Module.of R R,
  associator   := associator,
  left_unitor  := left_unitor,
  right_unitor := right_unitor,
  -- properties
  tensor_id'               := Ī» M N, tensor_id M N,
  tensor_comp'             := Ī» M N K M' N' K' f g h, tensor_comp f g h,
  associator_naturality'   := Ī» M N K M' N' K' f g h, associator_naturality f g h,
  left_unitor_naturality'  := Ī» M N f, left_unitor_naturality f,
  right_unitor_naturality' := Ī» M N f, right_unitor_naturality f,
  pentagon'                := Ī» M N K L, pentagon M N K L,
  triangle'                := Ī» M N, triangle M N, }

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : comm_ring ((š_ (Module.{u} R) : Module.{u} R) : Type u) :=
(by apply_instance : comm_ring R)

namespace monoidal_category

@[simp]
lemma hom_apply {K L M N : Module.{u} R} (f : K ā¶ L) (g : M ā¶ N) (k : K) (m : M) :
  (f ā g) (k āā m) = f k āā g m := rfl

@[simp]
lemma left_unitor_hom_apply {M : Module.{u} R} (r : R) (m : M) :
  ((Ī»_ M).hom : š_ (Module R) ā M ā¶ M) (r āā[R] m) = r ā¢ m :=
tensor_product.lid_tmul m r

@[simp]
lemma left_unitor_inv_apply {M : Module.{u} R} (m : M) :
  ((Ī»_ M).inv : M ā¶ š_ (Module.{u} R) ā M) m = 1 āā[R] m :=
tensor_product.lid_symm_apply m

@[simp]
lemma right_unitor_hom_apply {M : Module.{u} R} (m : M) (r : R) :
  ((Ļ_ M).hom : M ā š_ (Module R) ā¶ M) (m āā r) = r ā¢ m :=
tensor_product.rid_tmul m r

@[simp]
lemma right_unitor_inv_apply {M : Module.{u} R} (m : M) :
  ((Ļ_ M).inv : M ā¶ M ā š_ (Module.{u} R)) m = m āā[R] 1 :=
tensor_product.rid_symm_apply m

@[simp]
lemma associator_hom_apply {M N K : Module.{u} R} (m : M) (n : N) (k : K) :
  ((Ī±_ M N K).hom : (M ā N) ā K ā¶ M ā (N ā K)) ((m āā n) āā k) = (m āā (n āā k)) := rfl

@[simp]
lemma associator_inv_apply {M N K : Module.{u} R} (m : M) (n : N) (k : K) :
  ((Ī±_ M N K).inv : M ā (N ā K) ā¶ (M ā N) ā K) (m āā (n āā k)) = ((m āā n) āā k) := rfl

end monoidal_category

/-- (implementation) the braiding for R-modules -/
def braiding (M N : Module R) : tensor_obj M N ā tensor_obj N M :=
linear_equiv.to_Module_iso (tensor_product.comm R M N)

@[simp] lemma braiding_naturality {Xā Xā Yā Yā : Module.{u} R} (f : Xā ā¶ Yā) (g : Xā ā¶ Yā) :
  (f ā g) ā« (Yā.braiding Yā).hom =
    (Xā.braiding Xā).hom ā« (g ā f) :=
begin
  apply tensor_product.ext',
  intros x y,
  refl
end

@[simp] lemma hexagon_forward (X Y Z : Module.{u} R) :
  (Ī±_ X Y Z).hom ā« (braiding X _).hom ā« (Ī±_ Y Z X).hom =
  ((braiding X Y).hom ā š Z) ā« (Ī±_ Y X Z).hom ā« (š Y ā (braiding X Z).hom) :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  refl,
end

@[simp] lemma hexagon_reverse (X Y Z : Module.{u} R) :
  (Ī±_ X Y Z).inv ā« (braiding _ Z).hom ā« (Ī±_ Z X Y).inv =
  (š X ā (Y.braiding Z).hom) ā« (Ī±_ X Z Y).inv ā« ((X.braiding Z).hom ā š Y) :=
begin
  apply (cancel_epi (Ī±_ X Y Z).hom).1,
  apply tensor_product.ext_threefold,
  intros x y z,
  refl,
end

local attribute [ext] tensor_product.ext

/-- The symmetric monoidal structure on `Module R`. -/
instance symmetric_category : symmetric_category (Module.{u} R) :=
{ braiding := braiding,
  braiding_naturality' := Ī» Xā Xā Yā Yā f g, braiding_naturality f g,
  hexagon_forward' := hexagon_forward,
  hexagon_reverse' := hexagon_reverse, }

namespace monoidal_category

@[simp] lemma braiding_hom_apply {M N : Module.{u} R} (m : M) (n : N) :
  ((Ī²_ M N).hom : M ā N ā¶ N ā M) (m āā n) = n āā m := rfl

@[simp] lemma braiding_inv_apply {M N : Module.{u} R} (m : M) (n : N) :
  ((Ī²_ M N).inv : N ā M ā¶ M ā N) (n āā m) = m āā n := rfl

end monoidal_category

end Module
