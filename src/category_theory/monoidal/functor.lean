/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta
-/
import category_theory.monoidal.category
import category_theory.adjunction.basic

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `Īµ : š_ D ā¶ F.obj (š_ C)` (called the unit morphism)
* `Ī¼ X Y : (F.obj X) ā (F.obj Y) ā¶ F.obj (X ā Y)` (called the tensorator, or strength).
satisfying various axioms.

A monoidal functor is a lax monoidal functor for which `Īµ` and `Ī¼` are isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See also `category_theory.monoidal.functorial` for a typeclass decorating an object-level
function with the additional data of a monoidal functor.
This is useful when stating that a pre-existing functor is monoidal.

See `category_theory.monoidal.natural_transformation` for monoidal natural transformations.

We show in `category_theory.monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## Future work
* Oplax monoidal functors.

## References

See https://stacks.math.columbia.edu/tag/0FFL.
-/

open category_theory

universes vā vā vā uā uā uā

open category_theory.category
open category_theory.functor

namespace category_theory

section

open monoidal_category

variables (C : Type uā) [category.{vā} C] [monoidal_category.{vā} C]
          (D : Type uā) [category.{vā} D] [monoidal_category.{vā} D]

/-- A lax monoidal functor is a functor `F : C ā„¤ D` between monoidal categories,
equipped with morphisms `Īµ : š _D ā¶ F.obj (š_ C)` and `Ī¼ X Y : F.obj X ā F.obj Y ā¶ F.obj (X ā Y)`,
satisfying the appropriate coherences. -/
-- The direction of `left_unitality` and `right_unitality` as simp lemmas may look strange:
-- remember the rule of thumb that component indices of natural transformations
-- "weigh more" than structural maps.
-- (However by this argument `associativity` is currently stated backwards!)
structure lax_monoidal_functor extends C ā„¤ D :=
-- unit morphism
(Īµ               : š_ D ā¶ obj (š_ C))
-- tensorator
(Ī¼                : Ī  X Y : C, (obj X) ā (obj Y) ā¶ obj (X ā Y))
(Ī¼_natural'       : ā {X Y X' Y' : C}
  (f : X ā¶ Y) (g : X' ā¶ Y'),
  ((map f) ā (map g)) ā« Ī¼ Y Y' = Ī¼ X X' ā« map (f ā g)
  . obviously)
-- associativity of the tensorator
(associativity'   : ā (X Y Z : C),
    (Ī¼ X Y ā š (obj Z)) ā« Ī¼ (X ā Y) Z ā« map (Ī±_ X Y Z).hom
  = (Ī±_ (obj X) (obj Y) (obj Z)).hom ā« (š (obj X) ā Ī¼ Y Z) ā« Ī¼ X (Y ā Z)
  . obviously)
-- unitality
(left_unitality'  : ā X : C,
    (Ī»_ (obj X)).hom
  = (Īµ ā š (obj X)) ā« Ī¼ (š_ C) X ā« map (Ī»_ X).hom
  . obviously)
(right_unitality' : ā X : C,
    (Ļ_ (obj X)).hom
  = (š (obj X) ā Īµ) ā« Ī¼ X (š_ C) ā« map (Ļ_ X).hom
  . obviously)

restate_axiom lax_monoidal_functor.Ī¼_natural'
attribute [simp, reassoc] lax_monoidal_functor.Ī¼_natural
restate_axiom lax_monoidal_functor.left_unitality'
attribute [simp] lax_monoidal_functor.left_unitality
restate_axiom lax_monoidal_functor.right_unitality'
attribute [simp] lax_monoidal_functor.right_unitality
restate_axiom lax_monoidal_functor.associativity'
attribute [simp, reassoc] lax_monoidal_functor.associativity

-- When `rewrite_search` lands, add @[search] attributes to
-- lax_monoidal_functor.Ī¼_natural lax_monoidal_functor.left_unitality
-- lax_monoidal_functor.right_unitality lax_monoidal_functor.associativity

section
variables {C D}

@[simp, reassoc]
lemma lax_monoidal_functor.left_unitality_inv (F : lax_monoidal_functor C D) (X : C) :
  (Ī»_ (F.obj X)).inv ā« (F.Īµ ā š (F.obj X)) ā« F.Ī¼ (š_ C) X = F.map (Ī»_ X).inv :=
begin
  rw [iso.inv_comp_eq, F.left_unitality, category.assoc, category.assoc,
    āF.to_functor.map_comp, iso.hom_inv_id, F.to_functor.map_id, comp_id],
end

@[simp, reassoc]
lemma lax_monoidal_functor.right_unitality_inv (F : lax_monoidal_functor C D) (X : C) :
  (Ļ_ (F.obj X)).inv ā« (š (F.obj X) ā F.Īµ) ā« F.Ī¼ X (š_ C) = F.map (Ļ_ X).inv :=
begin
  rw [iso.inv_comp_eq, F.right_unitality, category.assoc, category.assoc,
    āF.to_functor.map_comp, iso.hom_inv_id, F.to_functor.map_id, comp_id],
end

@[simp, reassoc]
lemma lax_monoidal_functor.associativity_inv (F : lax_monoidal_functor C D) (X Y Z : C) :
  (š (F.obj X) ā F.Ī¼ Y Z) ā« F.Ī¼ X (Y ā Z) ā« F.map (Ī±_ X Y Z).inv =
    (Ī±_ (F.obj X) (F.obj Y) (F.obj Z)).inv ā« (F.Ī¼ X Y ā š (F.obj Z)) ā« F.Ī¼ (X ā Y) Z :=
begin
  rw [iso.eq_inv_comp, āF.associativity_assoc,
    āF.to_functor.map_comp, iso.hom_inv_id, F.to_functor.map_id, comp_id],
end

end

/--
A monoidal functor is a lax monoidal functor for which the tensorator and unitor as isomorphisms.

See https://stacks.math.columbia.edu/tag/0FFL.
-/
structure monoidal_functor
extends lax_monoidal_functor.{vā vā} C D :=
(Īµ_is_iso            : is_iso Īµ . tactic.apply_instance)
(Ī¼_is_iso            : Ī  X Y : C, is_iso (Ī¼ X Y) . tactic.apply_instance)

attribute [instance] monoidal_functor.Īµ_is_iso monoidal_functor.Ī¼_is_iso

variables {C D}

/--
The unit morphism of a (strong) monoidal functor as an isomorphism.
-/
noncomputable
def monoidal_functor.Īµ_iso (F : monoidal_functor.{vā vā} C D) :
  tensor_unit D ā F.obj (tensor_unit C) :=
as_iso F.Īµ

/--
The tensorator of a (strong) monoidal functor as an isomorphism.
-/
noncomputable
def monoidal_functor.Ī¼_iso (F : monoidal_functor.{vā vā} C D) (X Y : C) :
  (F.obj X) ā (F.obj Y) ā F.obj (X ā Y) :=
as_iso (F.Ī¼ X Y)

end

open monoidal_category

namespace lax_monoidal_functor

variables (C : Type uā) [category.{vā} C] [monoidal_category.{vā} C]

/-- The identity lax monoidal functor. -/
@[simps] def id : lax_monoidal_functor.{vā vā} C C :=
{ Īµ := š _,
  Ī¼ := Ī» X Y, š _,
  .. š­ C }

instance : inhabited (lax_monoidal_functor C C) := āØid Cā©

end lax_monoidal_functor

namespace monoidal_functor

section
variables {C : Type uā} [category.{vā} C] [monoidal_category.{vā} C]
variables {D : Type uā} [category.{vā} D] [monoidal_category.{vā} D]

lemma map_tensor (F : monoidal_functor.{vā vā} C D) {X Y X' Y' : C} (f : X ā¶ Y) (g : X' ā¶ Y') :
  F.map (f ā g) = inv (F.Ī¼ X X') ā« ((F.map f) ā (F.map g)) ā« F.Ī¼ Y Y' :=
by simp

lemma map_left_unitor (F : monoidal_functor.{vā vā} C D) (X : C) :
  F.map (Ī»_ X).hom = inv (F.Ī¼ (š_ C) X) ā« (inv F.Īµ ā š (F.obj X)) ā« (Ī»_ (F.obj X)).hom :=
begin
  simp only [lax_monoidal_functor.left_unitality],
  slice_rhs 2 3 { rw ācomp_tensor_id, simp, },
  simp,
end

lemma map_right_unitor (F : monoidal_functor.{vā vā} C D) (X : C) :
  F.map (Ļ_ X).hom = inv (F.Ī¼ X (š_ C)) ā« (š (F.obj X) ā inv F.Īµ) ā« (Ļ_ (F.obj X)).hom :=
begin
  simp only [lax_monoidal_functor.right_unitality],
  slice_rhs 2 3 { rw āid_tensor_comp, simp, },
  simp,
end

/-- The tensorator as a natural isomorphism. -/
noncomputable
def Ī¼_nat_iso (F : monoidal_functor.{vā vā} C D) :
  (functor.prod F.to_functor F.to_functor) ā (tensor D) ā (tensor C) ā F.to_functor :=
nat_iso.of_components
  (by { intros, apply F.Ī¼_iso })
  (by { intros, apply F.to_lax_monoidal_functor.Ī¼_natural })
end

section
variables (C : Type uā) [category.{vā} C] [monoidal_category.{vā} C]

/-- The identity monoidal functor. -/
@[simps] def id : monoidal_functor.{vā vā} C C :=
{ Īµ := š _,
  Ī¼ := Ī» X Y, š _,
  .. š­ C }

instance : inhabited (monoidal_functor C C) := āØid Cā©

end

end monoidal_functor

variables {C : Type uā} [category.{vā} C] [monoidal_category.{vā} C]
variables {D : Type uā} [category.{vā} D] [monoidal_category.{vā} D]
variables {E : Type uā} [category.{vā} E] [monoidal_category.{vā} E]

namespace lax_monoidal_functor
variables (F : lax_monoidal_functor.{vā vā} C D) (G : lax_monoidal_functor.{vā vā} D E)

-- The proofs here are horrendous; rewrite_search helps a lot.
/-- The composition of two lax monoidal functors is again lax monoidal. -/
@[simps] def comp : lax_monoidal_functor.{vā vā} C E :=
{ Īµ                := G.Īµ ā« (G.map F.Īµ),
  Ī¼                := Ī» X Y, G.Ī¼ (F.obj X) (F.obj Y) ā« G.map (F.Ī¼ X Y),
  Ī¼_natural'       := Ī» _ _ _ _ f g,
  begin
    simp only [functor.comp_map, assoc],
    rw [ācategory.assoc, lax_monoidal_functor.Ī¼_natural, category.assoc, āmap_comp, āmap_comp,
        ālax_monoidal_functor.Ī¼_natural]
  end,
  associativity'   := Ī» X Y Z,
  begin
    dsimp,
    rw id_tensor_comp,
    slice_rhs 3 4 { rw [ā G.to_functor.map_id, G.Ī¼_natural], },
    slice_rhs 1 3 { rw āG.associativity, },
    rw comp_tensor_id,
    slice_lhs 2 3 { rw [ā G.to_functor.map_id, G.Ī¼_natural], },
    rw [category.assoc, category.assoc, category.assoc, category.assoc, category.assoc,
        āG.to_functor.map_comp, āG.to_functor.map_comp, āG.to_functor.map_comp,
        āG.to_functor.map_comp, F.associativity],
  end,
  left_unitality'  := Ī» X,
  begin
    dsimp,
    rw [G.left_unitality, comp_tensor_id, category.assoc, category.assoc],
    apply congr_arg,
    rw [F.left_unitality, map_comp, ānat_trans.id_app, ācategory.assoc,
        ālax_monoidal_functor.Ī¼_natural, nat_trans.id_app, map_id, ācategory.assoc, map_comp],
  end,
  right_unitality' := Ī» X,
  begin
    dsimp,
    rw [G.right_unitality, id_tensor_comp, category.assoc, category.assoc],
    apply congr_arg,
    rw [F.right_unitality, map_comp, ānat_trans.id_app, ācategory.assoc,
        ālax_monoidal_functor.Ī¼_natural, nat_trans.id_app, map_id, ācategory.assoc, map_comp],
  end,
  .. (F.to_functor) ā (G.to_functor) }.

infixr ` āā `:80 := comp

end lax_monoidal_functor

namespace monoidal_functor

variables (F : monoidal_functor.{vā vā} C D) (G : monoidal_functor.{vā vā} D E)

/-- The composition of two monoidal functors is again monoidal. -/
@[simps]
def comp : monoidal_functor.{vā vā} C E :=
{ Īµ_is_iso := by { dsimp, apply_instance },
  Ī¼_is_iso := by { dsimp, apply_instance },
  .. (F.to_lax_monoidal_functor).comp (G.to_lax_monoidal_functor) }.

infixr ` āā `:80 := comp -- We overload notation; potentially dangerous, but it seems to work.

end monoidal_functor

/--
If we have a right adjoint functor `G` to a monoidal functor `F`, then `G` has a lax monoidal
structure as well.
-/
@[simps]
noncomputable
def monoidal_adjoint (F : monoidal_functor C D) {G : D ā„¤ C} (h : F.to_functor ā£ G) :
  lax_monoidal_functor D C :=
{ to_functor := G,
  Īµ := h.hom_equiv _ _ (inv F.Īµ),
  Ī¼ := Ī» X Y,
    h.hom_equiv _ (X ā Y) (inv (F.Ī¼ (G.obj X) (G.obj Y)) ā« (h.counit.app X ā h.counit.app Y)),
  Ī¼_natural' := Ī» X Y X' Y' f g,
  begin
    rw [āh.hom_equiv_naturality_left, āh.hom_equiv_naturality_right, equiv.apply_eq_iff_eq, assoc,
      is_iso.eq_inv_comp, āF.to_lax_monoidal_functor.Ī¼_natural_assoc, is_iso.hom_inv_id_assoc,
      ātensor_comp, adjunction.counit_naturality, adjunction.counit_naturality, tensor_comp],
  end,
  associativity' := Ī» X Y Z,
  begin
    rw [āh.hom_equiv_naturality_right, āh.hom_equiv_naturality_left, āh.hom_equiv_naturality_left,
      āh.hom_equiv_naturality_left, equiv.apply_eq_iff_eq,
      ā cancel_epi (F.to_lax_monoidal_functor.Ī¼ (G.obj X ā G.obj Y) (G.obj Z)),
      ā cancel_epi (F.to_lax_monoidal_functor.Ī¼ (G.obj X) (G.obj Y) ā š (F.obj (G.obj Z))),
      F.to_lax_monoidal_functor.associativity_assoc (G.obj X) (G.obj Y) (G.obj Z),
      āF.to_lax_monoidal_functor.Ī¼_natural_assoc, assoc, is_iso.hom_inv_id_assoc,
      āF.to_lax_monoidal_functor.Ī¼_natural_assoc, is_iso.hom_inv_id_assoc, ātensor_comp,
      ātensor_comp, id_comp, functor.map_id, functor.map_id, id_comp, ātensor_comp_assoc,
      ātensor_comp_assoc, id_comp, id_comp, h.hom_equiv_unit, h.hom_equiv_unit, functor.map_comp,
      assoc, assoc, h.counit_naturality, h.left_triangle_components_assoc, is_iso.hom_inv_id_assoc,
      functor.map_comp, assoc, h.counit_naturality, h.left_triangle_components_assoc,
      is_iso.hom_inv_id_assoc],
    exact associator_naturality (h.counit.app X) (h.counit.app Y) (h.counit.app Z),
  end,
  left_unitality' := Ī» X,
  begin
    rw [āh.hom_equiv_naturality_right, āh.hom_equiv_naturality_left, āequiv.symm_apply_eq,
      h.hom_equiv_counit, F.map_left_unitor, h.hom_equiv_unit, assoc, assoc, assoc, F.map_tensor,
      assoc, assoc, is_iso.hom_inv_id_assoc, ātensor_comp_assoc, functor.map_id, id_comp,
      functor.map_comp, assoc, h.counit_naturality, h.left_triangle_components_assoc,
      āleft_unitor_naturality, ātensor_comp_assoc, id_comp, comp_id],
  end,
  right_unitality' := Ī» X,
  begin
    rw [āh.hom_equiv_naturality_right, āh.hom_equiv_naturality_left, āequiv.symm_apply_eq,
      h.hom_equiv_counit, F.map_right_unitor, assoc, assoc, āright_unitor_naturality,
      ātensor_comp_assoc, comp_id, id_comp, h.hom_equiv_unit, F.map_tensor, assoc, assoc, assoc,
      is_iso.hom_inv_id_assoc, functor.map_comp, functor.map_id, ātensor_comp_assoc, assoc,
      h.counit_naturality, h.left_triangle_components_assoc, id_comp],
  end }.

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
noncomputable
def monoidal_inverse (F : monoidal_functor C D) [is_equivalence F.to_functor] :
  monoidal_functor D C :=
{ to_lax_monoidal_functor := monoidal_adjoint F (as_equivalence _).to_adjunction,
  Īµ_is_iso := by { dsimp [equivalence.to_adjunction], apply_instance },
  Ī¼_is_iso := Ī» X Y, by { dsimp [equivalence.to_adjunction], apply_instance } }

@[simp]
lemma monoidal_inverse_to_functor (F : monoidal_functor C D) [is_equivalence F.to_functor] :
  (monoidal_inverse F).to_functor = F.to_functor.inv := rfl

end category_theory
