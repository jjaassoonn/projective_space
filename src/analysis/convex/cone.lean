/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, FrΓ©dΓ©ric Dupuis
-/
import analysis.convex.hull
import analysis.inner_product_space.basic

/-!
# Convex cones

In a `π`-module `E`, we define a convex cone as a set `s` such that `a β’ x + b β’ y β s` whenever
`x, y β s` and `a, b > 0`. We prove that convex cones form a `complete_lattice`, and define their
images (`convex_cone.map`) and preimages (`convex_cone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We also define `convex.to_cone` to be the minimal cone that includes a given convex set.

We define `set.inner_dual_cone` to be the cone consisting of all points `y` such that for
all points `x` in a given set `0 β€ βͺ x, y β«`.

## Main statements

We prove two extension theorems:
* `riesz_extension`:
  [M. Riesz extension theorem](https://en.wikipedia.org/wiki/M._Riesz_extension_theorem) says that
  if `s` is a convex cone in a real vector space `E`, `p` is a submodule of `E`
  such that `p + s = E`, and `f` is a linear function `p β β` which is
  nonnegative on `p β© s`, then there exists a globally defined linear function
  `g : E β β` that agrees with `f` on `p`, and is nonnegative on `s`.
* `exists_extension_of_le_sublinear`:
  Hahn-Banach theorem: if `N : E β β` is a sublinear map, `f` is a linear map
  defined on a subspace of `E`, and `f x β€ N x` for all `x` in the domain of `f`,
  then `f` can be extended to the whole space to a linear map `g` such that `g x β€ N x`
  for all `x`

## Implementation notes

While `convex π` is a predicate on sets, `convex_cone π E` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
-/


open set linear_map
open_locale classical pointwise

variables {π E F G : Type*}

/-! ### Definition of `convex_cone` and basic properties -/

section definitions
variables (π E) [ordered_semiring π]

/-- A convex cone is a subset `s` of a `π`-module such that `a β’ x + b β’ y β s` whenever `a, b > 0`
and `x, y β s`. -/
structure convex_cone [add_comm_monoid E] [has_scalar π E] :=
(carrier : set E)
(smul_mem' : β β¦c : πβ¦, 0 < c β β β¦x : Eβ¦, x β carrier β c β’ x β carrier)
(add_mem' : β β¦xβ¦ (hx : x β carrier) β¦yβ¦ (hy : y β carrier), x + y β carrier)

end definitions

variables {π E}

namespace convex_cone
section ordered_semiring
variables [ordered_semiring π] [add_comm_monoid E]

section has_scalar
variables [has_scalar π E] (S T : convex_cone π E)

instance : has_coe (convex_cone π E) (set E) := β¨convex_cone.carrierβ©

instance : has_mem E (convex_cone π E) := β¨Ξ» m S, m β S.carrierβ©

instance : has_le (convex_cone π E) := β¨Ξ» S T, S.carrier β T.carrierβ©

instance : has_lt (convex_cone π E) := β¨Ξ» S T, S.carrier β T.carrierβ©

@[simp, norm_cast] lemma mem_coe {x : E} : x β (S : set E) β x β S := iff.rfl

@[simp] lemma mem_mk {s : set E} {hβ hβ x} : x β @mk π _ _ _ _ s hβ hβ β x β s := iff.rfl

/-- Two `convex_cone`s are equal if the underlying sets are equal. -/
theorem ext' {S T : convex_cone π E} (h : (S : set E) = T) : S = T :=
by cases S; cases T; congr'

/-- Two `convex_cone`s are equal if and only if the underlying sets are equal. -/
protected theorem ext'_iff {S T : convex_cone π E}  : (S : set E) = T β S = T :=
β¨ext', Ξ» h, h βΈ rflβ©

/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext] theorem ext {S T : convex_cone π E} (h : β x, x β S β x β T) : S = T := ext' $ set.ext h

lemma smul_mem {c : π} {x : E} (hc : 0 < c) (hx : x β S) : c β’ x β S := S.smul_mem' hc hx

lemma add_mem β¦xβ¦ (hx : x β S) β¦yβ¦ (hy : y β S) : x + y β S := S.add_mem' hx hy

instance : has_inf (convex_cone π E) :=
β¨Ξ» S T, β¨S β© T, Ξ» c hc x hx, β¨S.smul_mem hc hx.1, T.smul_mem hc hx.2β©,
  Ξ» x hx y hy, β¨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2β©β©β©

lemma coe_inf : ((S β T : convex_cone π E) : set E) = βS β© βT := rfl

lemma mem_inf {x} : x β S β T β x β S β§ x β T := iff.rfl

instance : has_Inf (convex_cone π E) :=
β¨Ξ» S, β¨β s β S, βs,
  Ξ» c hc x hx, mem_bInter $ Ξ» s hs, s.smul_mem hc $ by apply mem_bInter_iff.1 hx s hs,
  Ξ» x hx y hy, mem_bInter $ Ξ» s hs, s.add_mem (by apply mem_bInter_iff.1 hx s hs)
    (by apply mem_bInter_iff.1 hy s hs)β©β©

lemma mem_Inf {x : E} {S : set (convex_cone π E)} : x β Inf S β β s β S, x β s := mem_bInter_iff

variables (π)

instance : has_bot (convex_cone π E) := β¨β¨β, Ξ» c hc x, false.elim, Ξ» x, false.elimβ©β©

lemma mem_bot (x : E) : x β (β₯ : convex_cone π E) = false := rfl

instance : has_top (convex_cone π E) := β¨β¨univ, Ξ» c hc x hx, mem_univ _, Ξ» x hx y hy, mem_univ _β©β©

lemma mem_top (x : E) : x β (β€ : convex_cone π E) := mem_univ x

instance : complete_lattice (convex_cone π E) :=
{ le           := (β€),
  lt           := (<),
  bot          := (β₯),
  bot_le       := Ξ» S x, false.elim,
  top          := (β€),
  le_top       := Ξ» S x hx, mem_top π x,
  inf          := (β),
  Inf          := has_Inf.Inf,
  sup          := Ξ» a b, Inf {x | a β€ x β§ b β€ x},
  Sup          := Ξ» s, Inf {T | β S β s, S β€ T},
  le_sup_left  := Ξ» a b, Ξ» x hx, mem_Inf.2 $ Ξ» s hs, hs.1 hx,
  le_sup_right := Ξ» a b, Ξ» x hx, mem_Inf.2 $ Ξ» s hs, hs.2 hx,
  sup_le       := Ξ» a b c ha hb x hx, mem_Inf.1 hx c β¨ha, hbβ©,
  le_inf       := Ξ» a b c ha hb x hx, β¨ha hx, hb hxβ©,
  inf_le_left  := Ξ» a b x, and.left,
  inf_le_right := Ξ» a b x, and.right,
  le_Sup       := Ξ» s p hs x hx, mem_Inf.2 $ Ξ» t ht, ht p hs hx,
  Sup_le       := Ξ» s p hs x hx, mem_Inf.1 hx p hs,
  le_Inf       := Ξ» s a ha x hx, mem_Inf.2 $ Ξ» t ht, ha t ht hx,
  Inf_le       := Ξ» s a ha x hx, mem_Inf.1 hx _ ha,
  .. partial_order.lift (coe : convex_cone π E β set E) (Ξ» a b, ext') }

instance : inhabited (convex_cone π E) := β¨β₯β©

end has_scalar

section module
variables [module π E] (S : convex_cone π E)

protected lemma convex : convex π (S : set E) :=
convex_iff_forall_pos.2 $ Ξ» x y hx hy a b ha hb hab,
  S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

end module
end ordered_semiring

section linear_ordered_field
variables [linear_ordered_field π]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F] [add_comm_monoid G]

section mul_action
variables [mul_action π E] (S : convex_cone π E)

lemma smul_mem_iff {c : π} (hc : 0 < c) {x : E} :
  c β’ x β S β x β S :=
β¨Ξ» h, inv_smul_smulβ hc.ne' x βΈ S.smul_mem (inv_pos.2 hc) h, S.smul_mem hcβ©

end mul_action

section module
variables [module π E] [module π F] [module π G]

/-- The image of a convex cone under a `π`-linear map is a convex cone. -/
def map (f : E ββ[π] F) (S : convex_cone π E) : convex_cone π F :=
{ carrier := f '' S,
  smul_mem' := Ξ» c hc y β¨x, hx, hyβ©, hy βΈ f.map_smul c x βΈ mem_image_of_mem f (S.smul_mem hc hx),
  add_mem' := Ξ» yβ β¨xβ, hxβ, hyββ© yβ β¨xβ, hxβ, hyββ©, hyβ βΈ hyβ βΈ f.map_add xβ xβ βΈ
    mem_image_of_mem f (S.add_mem hxβ hxβ) }

lemma map_map (g : F ββ[π] G) (f : E ββ[π] F) (S : convex_cone π E) :
  (S.map f).map g = S.map (g.comp f) :=
ext' $ image_image g f S

@[simp] lemma map_id (S : convex_cone π E) : S.map linear_map.id = S := ext' $ image_id _

/-- The preimage of a convex cone under a `π`-linear map is a convex cone. -/
def comap (f : E ββ[π] F) (S : convex_cone π F) : convex_cone π E :=
{ carrier := f β»ΒΉ' S,
  smul_mem' := Ξ» c hc x hx, by { rw [mem_preimage, f.map_smul c], exact S.smul_mem hc hx },
  add_mem' := Ξ» x hx y hy, by { rw [mem_preimage, f.map_add], exact S.add_mem hx hy } }

@[simp] lemma comap_id (S : convex_cone π E) : S.comap linear_map.id = S := ext' preimage_id

lemma comap_comap (g : F ββ[π] G) (f : E ββ[π] F) (S : convex_cone π G) :
  (S.comap g).comap f = S.comap (g.comp f) :=
ext' $ preimage_comp.symm

@[simp] lemma mem_comap {f : E ββ[π] F} {S : convex_cone π F} {x : E} : x β S.comap f β f x β S :=
iff.rfl

end module
end add_comm_monoid

section ordered_add_comm_group
variables [ordered_add_comm_group E] [module π E]

/--
Constructs an ordered module given an `ordered_add_comm_group`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
lemma to_ordered_smul (S : convex_cone π E) (h : β x y : E, x β€ y β y - x β S) :
  ordered_smul π E :=
ordered_smul.mk'
begin
  intros x y z xy hz,
  rw [h (z β’ x) (z β’ y), βsmul_sub z y x],
  exact smul_mem S hz ((h x y).mp xy.le),
end

end ordered_add_comm_group
end linear_ordered_field

/-! ### Convex cones with extra properties -/

section ordered_semiring
variables [ordered_semiring π]

section add_comm_monoid
variables [add_comm_monoid E] [has_scalar π E] (S : convex_cone π E)

/-- A convex cone is pointed if it includes `0`. -/
def pointed (S : convex_cone π E) : Prop := (0 : E) β S

/-- A convex cone is blunt if it doesn't include `0`. -/
def blunt (S : convex_cone π E) : Prop := (0 : E) β S

lemma pointed_iff_not_blunt (S : convex_cone π E) : S.pointed β Β¬S.blunt :=
β¨Ξ» hβ hβ, hβ hβ, not_not.mpβ©

lemma blunt_iff_not_pointed (S : convex_cone π E) : S.blunt β Β¬S.pointed :=
by rw [pointed_iff_not_blunt, not_not]

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [has_scalar π E] (S : convex_cone π E)

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def flat : Prop := β x β S, x β  (0 : E) β§ -x β S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def salient : Prop := β x β S, x β  (0 : E) β -x β S

lemma salient_iff_not_flat (S : convex_cone π E) : S.salient β Β¬S.flat :=
begin
  split,
  { rintros hβ β¨x, xs, Hβ, Hββ©,
    exact hβ x xs Hβ Hβ },
  { intro h,
    unfold flat at h,
    push_neg at h,
    exact h }
end

/-- A flat cone is always pointed (contains `0`). -/
lemma flat.pointed {S : convex_cone π E} (hS : S.flat) : S.pointed :=
begin
  obtain β¨x, hx, _, hxnegβ© := hS,
  rw [pointed, βadd_neg_self x],
  exact add_mem S hx hxneg,
end

/-- A blunt cone (one not containing `0`) is always salient. -/
lemma blunt.salient {S : convex_cone π E} : S.blunt β S.salient :=
begin
  rw [salient_iff_not_flat, blunt_iff_not_pointed],
  exact mt flat.pointed,
end

/-- A pointed convex cone defines a preorder. -/
def to_preorder (hβ : S.pointed) : preorder E :=
{ le := Ξ» x y, y - x β S,
  le_refl := Ξ» x, by change x - x β S; rw [sub_self x]; exact hβ,
  le_trans := Ξ» x y z xy zy, by simpa using add_mem S zy xy }

/-- A pointed and salient cone defines a partial order. -/
def to_partial_order (hβ : S.pointed) (hβ : S.salient) : partial_order E :=
{ le_antisymm :=
    begin
      intros a b ab ba,
      by_contradiction h,
      have h' : b - a β  0 := Ξ» h'', h (eq_of_sub_eq_zero h'').symm,
      have H := hβ (b-a) ab h',
      rw neg_sub b a at H,
      exact H ba,
    end,
  ..to_preorder S hβ }

/-- A pointed and salient cone defines an `ordered_add_comm_group`. -/
def to_ordered_add_comm_group (hβ : S.pointed) (hβ : S.salient) :
  ordered_add_comm_group E :=
{ add_le_add_left :=
    begin
      intros a b hab c,
      change c + b - (c + a) β S,
      rw add_sub_add_left_eq_sub,
      exact hab,
    end,
  ..to_partial_order S hβ hβ,
  ..show add_comm_group E, by apply_instance }

end add_comm_group
end ordered_semiring

/-! ### Positive cone of an ordered module -/

section positive_cone
variables (π E) [ordered_semiring π] [ordered_add_comm_group E] [module π E] [ordered_smul π E]

/--
The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positive_cone : convex_cone π E :=
{ carrier := {x | 0 β€ x},
  smul_mem' :=
    begin
      rintro c hc x (hx : _ β€ _),
      rw βsmul_zero c,
      exact smul_le_smul_of_nonneg hx hc.le,
    end,
  add_mem' := Ξ» x (hx : _ β€ _) y (hy : _ β€ _), add_nonneg hx hy }

/-- The positive cone of an ordered module is always salient. -/
lemma salient_positive_cone : salient (positive_cone π E) :=
Ξ» x xs hx hx', lt_irrefl (0 : E)
  (calc
    0   < x         : lt_of_le_of_ne xs hx.symm
    ... β€ x + (-x)  : le_add_of_nonneg_right hx'
    ... = 0         : add_neg_self x)

/-- The positive cone of an ordered module is always pointed. -/
lemma pointed_positive_cone : pointed (positive_cone π E) := le_refl 0

end positive_cone
end convex_cone

/-! ### Cone over a convex set -/

section cone_from_convex
variables [linear_ordered_field π] [ordered_add_comm_group E] [module π E]

namespace convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def to_cone (s : set E) (hs : convex π s) : convex_cone π E :=
begin
  apply convex_cone.mk (β (c : π) (H : 0 < c), c β’ s);
    simp only [mem_Union, mem_smul_set],
  { rintros c c_pos _ β¨c', c'_pos, x, hx, rflβ©,
    exact β¨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symmβ© },
  { rintros _ β¨cx, cx_pos, x, hx, rflβ© _ β¨cy, cy_pos, y, hy, rflβ©,
    have : 0 < cx + cy, from add_pos cx_pos cy_pos,
    refine β¨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, _β©,
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left _ this.ne'] }
end

variables {s : set E} (hs : convex π s) {x : E}

lemma mem_to_cone : x β hs.to_cone s β β (c : π), 0 < c β§ β y β s, c β’ y = x :=
by simp only [to_cone, convex_cone.mem_mk, mem_Union, mem_smul_set, eq_comm, exists_prop]

lemma mem_to_cone' : x β hs.to_cone s β β (c : π), 0 < c β§ c β’ x β s :=
begin
  refine hs.mem_to_cone.trans β¨_, _β©,
  { rintros β¨c, hc, y, hy, rflβ©,
    exact β¨cβ»ΒΉ, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel hc.ne', one_smul]β© },
  { rintros β¨c, hc, hcxβ©,
    exact β¨cβ»ΒΉ, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel hc.ne', one_smul]β© }
end

lemma subset_to_cone : s β hs.to_cone s :=
Ξ» x hx, hs.mem_to_cone'.2 β¨1, zero_lt_one, by rwa one_smulβ©

/-- `hs.to_cone s` is the least cone that includes `s`. -/
lemma to_cone_is_least : is_least { t : convex_cone π E | s β t } (hs.to_cone s) :=
begin
  refine β¨hs.subset_to_cone, Ξ» t ht x hx, _β©,
  rcases hs.mem_to_cone.1 hx with β¨c, hc, y, hy, rflβ©,
  exact t.smul_mem hc (ht hy)
end

lemma to_cone_eq_Inf : hs.to_cone s = Inf { t : convex_cone π E | s β t } :=
hs.to_cone_is_least.is_glb.Inf_eq.symm

end convex

lemma convex_hull_to_cone_is_least (s : set E) :
  is_least {t : convex_cone π E | s β t} ((convex_convex_hull π s).to_cone _) :=
begin
  convert (convex_convex_hull π s).to_cone_is_least,
  ext t,
  exact β¨Ξ» h, convex_hull_min h t.convex, (subset_convex_hull π s).transβ©,
end

lemma convex_hull_to_cone_eq_Inf (s : set E) :
  (convex_convex_hull π s).to_cone _ = Inf {t : convex_cone π E | s β t} :=
(convex_hull_to_cone_is_least s).is_glb.Inf_eq.symm

end cone_from_convex

/-!
### M. Riesz extension theorem

Given a convex cone `s` in a vector space `E`, a submodule `p`, and a linear `f : p β β`, assume
that `f` is nonnegative on `p β© s` and `p + s = E`. Then there exists a globally defined linear
function `g : E β β` that agrees with `f` on `p`, and is nonnegative on `s`.

We prove this theorem using Zorn's lemma. `riesz_extension.step` is the main part of the proof.
It says that if the domain `p` of `f` is not the whole space, then `f` can be extended to a larger
subspace `p β span β {y}` without breaking the non-negativity condition.

In `riesz_extension.exists_top` we use Zorn's lemma to prove that we can extend `f`
to a linear map `g` on `β€ : submodule E`. Mathematically this is the same as a linear map on `E`
but in Lean `β€ : submodule E` is isomorphic but is not equal to `E`. In `riesz_extension`
we use this isomorphism to prove the theorem.
-/

variables [add_comm_group E] [module β E]

namespace riesz_extension
open submodule
variables (s : convex_cone β E) (f : linear_pmap β E β)

/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain β β`, assume that `f` is nonnegative on `f.domain β© p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
lemma step (nonneg : β x : f.domain, (x : E) β s β 0 β€ f x)
  (dense : β y, β x : f.domain, (x : E) + y β s) (hdom : f.domain β  β€) :
  β g, f < g β§ β x : g.domain, (x : E) β s β 0 β€ g x :=
begin
  obtain β¨y, -, hyβ© : β (y : E) (h : y β β€), y β f.domain,
    { exact @set_like.exists_of_lt (submodule β E) _ _ _ _ (lt_top_iff_ne_top.2 hdom) },
  obtain β¨c, le_c, c_leβ© :
    β c, (β x : f.domain, -(x:E) - y β s β f x β€ c) β§ (β x : f.domain, (x:E) + y β s β c β€ f x),
  { set Sp := f '' {x : f.domain | (x:E) + y β s},
    set Sn := f '' {x : f.domain | -(x:E) - y β s},
    suffices : (upper_bounds Sn β© lower_bounds Sp).nonempty,
      by simpa only [set.nonempty, upper_bounds, lower_bounds, ball_image_iff] using this,
    refine exists_between_of_forall_le (nonempty.image f _) (nonempty.image f (dense y)) _,
    { rcases (dense (-y)) with β¨x, hxβ©,
      rw [β neg_neg x, coe_neg, β sub_eq_add_neg] at hx,
      exact β¨_, hxβ© },
    rintros a β¨xn, hxn, rflβ© b β¨xp, hxp, rflβ©,
    have := s.add_mem hxp hxn,
    rw [add_assoc, add_sub_cancel'_right, β sub_eq_add_neg, β coe_sub] at this,
    replace := nonneg _ this,
    rwa [f.map_sub, sub_nonneg] at this },
  have hy' : y β  0, from Ξ» hyβ, hy (hyβ.symm βΈ zero_mem _),
  refine β¨f.sup_span_singleton y (-c) hy, _, _β©,
  { refine lt_iff_le_not_le.2 β¨f.left_le_sup _ _, Ξ» H, _β©,
    replace H := linear_pmap.domain_mono.monotone H,
    rw [linear_pmap.domain_sup_span_singleton, sup_le_iff, span_le, singleton_subset_iff] at H,
    exact hy H.2 },
  { rintros β¨z, hzβ© hzs,
    rcases mem_sup.1 hz with β¨x, hx, y', hy', rflβ©,
    rcases mem_span_singleton.1 hy' with β¨r, rflβ©,
    simp only [subtype.coe_mk] at hzs,
    erw [linear_pmap.sup_span_singleton_apply_mk _ _ _ _ _ hx, smul_neg,
      β sub_eq_add_neg, sub_nonneg],
    rcases lt_trichotomy r 0 with hr|hr|hr,
    { have : -(rβ»ΒΉ β’ x) - y β s,
        by rwa [β s.smul_mem_iff (neg_pos.2 hr), smul_sub, smul_neg, neg_smul, neg_neg, smul_smul,
          mul_inv_cancel hr.ne, one_smul, sub_eq_add_neg, neg_smul, neg_neg],
      replace := le_c (rβ»ΒΉ β’ β¨x, hxβ©) this,
      rwa [β mul_le_mul_left (neg_pos.2 hr), β neg_mul_eq_neg_mul, β neg_mul_eq_neg_mul,
        neg_le_neg_iff, f.map_smul, smul_eq_mul, β mul_assoc, mul_inv_cancel hr.ne,
        one_mul] at this },
    { subst r,
      simp only [zero_smul, add_zero] at hzs β’,
      apply nonneg,
      exact hzs },
    { have : rβ»ΒΉ β’ x + y β s,
        by rwa [β s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel hr.ne', one_smul],
      replace := c_le (rβ»ΒΉ β’ β¨x, hxβ©) this,
      rwa [β mul_le_mul_left hr, f.map_smul, smul_eq_mul, β mul_assoc,
        mul_inv_cancel hr.ne', one_mul] at this } }
end

theorem exists_top (p : linear_pmap β E β)
  (hp_nonneg : β x : p.domain, (x : E) β s β 0 β€ p x)
  (hp_dense : β y, β x : p.domain, (x : E) + y β s) :
  β q β₯ p, q.domain = β€ β§ β x : q.domain, (x : E) β s β 0 β€ q x :=
begin
  replace hp_nonneg : p β { p | _ }, by { rw mem_set_of_eq, exact hp_nonneg },
  obtain β¨q, hqs, hpq, hqβ© := zorn.zorn_nonempty_partial_orderβ _ _ _ hp_nonneg,
  { refine β¨q, hpq, _, hqsβ©,
    contrapose! hq,
    rcases step s q hqs _ hq with β¨r, hqr, hrβ©,
    { exact β¨r, hr, hqr.le, hqr.ne'β© },
    { exact Ξ» y, let β¨x, hxβ© := hp_dense y in β¨of_le hpq.left x, hxβ© } },
  { intros c hcs c_chain y hy,
    clear hp_nonneg hp_dense p,
    have cne : c.nonempty := β¨y, hyβ©,
    refine β¨linear_pmap.Sup c c_chain.directed_on, _, Ξ» _, linear_pmap.le_Sup c_chain.directed_onβ©,
    rintros β¨x, hxβ© hxs,
    have hdir : directed_on (β€) (linear_pmap.domain '' c),
      from directed_on_image.2 (c_chain.directed_on.mono linear_pmap.domain_mono.monotone),
    rcases (mem_Sup_of_directed (cne.image _) hdir).1 hx with β¨_, β¨f, hfc, rflβ©, hfxβ©,
    have : f β€ linear_pmap.Sup c c_chain.directed_on, from linear_pmap.le_Sup _ hfc,
    convert β hcs hfc β¨x, hfxβ© hxs,
    apply this.2, refl }
end

end riesz_extension

/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p β β`, assume that `f` is nonnegative on `p β© s` and `p + s = E`. Then
there exists a globally defined linear function `g : E β β` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem riesz_extension (s : convex_cone β E) (f : linear_pmap β E β)
  (nonneg : β x : f.domain, (x : E) β s β 0 β€ f x) (dense : β y, β x : f.domain, (x : E) + y β s) :
  β g : E ββ[β] β, (β x : f.domain, g x = f x) β§ (β x β s, 0 β€ g x) :=
begin
  rcases riesz_extension.exists_top s f nonneg dense with β¨β¨g_dom, gβ©, β¨hpg, hfgβ©, htop, hgsβ©,
  clear hpg,
  refine β¨g ββ β(linear_equiv.of_top _ htop).symm, _, _β©;
    simp only [comp_apply, linear_equiv.coe_coe, linear_equiv.of_top_symm_apply],
  { exact Ξ» x, (hfg (submodule.coe_mk _ _).symm).symm },
  { exact Ξ» x hx, hgs β¨x, _β© hx }
end

/-- **Hahn-Banach theorem**: if `N : E β β` is a sublinear map, `f` is a linear map
defined on a subspace of `E`, and `f x β€ N x` for all `x` in the domain of `f`,
then `f` can be extended to the whole space to a linear map `g` such that `g x β€ N x`
for all `x`. -/
theorem exists_extension_of_le_sublinear (f : linear_pmap β E β) (N : E β β)
  (N_hom : β (c : β), 0 < c β β x, N (c β’ x) = c * N x)
  (N_add : β x y, N (x + y) β€ N x + N y)
  (hf : β x : f.domain, f x β€ N x) :
  β g : E ββ[β] β, (β x : f.domain, g x = f x) β§ (β x, g x β€ N x) :=
begin
  let s : convex_cone β (E Γ β) :=
  { carrier := {p : E Γ β | N p.1 β€ p.2 },
    smul_mem' := Ξ» c hc p hp,
      calc N (c β’ p.1) = c * N p.1 : N_hom c hc p.1
      ... β€ c * p.2 : mul_le_mul_of_nonneg_left hp hc.le,
    add_mem' := Ξ» x hx y hy, (N_add _ _).trans (add_le_add hx hy) },
  obtain β¨g, g_eq, g_nonnegβ© :=
    riesz_extension s ((-f).coprod (linear_map.id.to_pmap β€)) _ _;
    try { simp only [linear_pmap.coprod_apply, to_pmap_apply, id_apply,
            linear_pmap.neg_apply, β sub_eq_neg_add, sub_nonneg, subtype.coe_mk] at * },
  replace g_eq : β (x : f.domain) (y : β), g (x, y) = y - f x,
  { intros x y,
    simpa only [subtype.coe_mk, subtype.coe_eta] using g_eq β¨(x, y), β¨x.2, trivialβ©β© },
  { refine β¨-g.comp (inl β E β), _, _β©; simp only [neg_apply, inl_apply, comp_apply],
    { intro x, simp [g_eq x 0] },
    { intro x,
      have A : (x, N x) = (x, 0) + (0, N x), by simp,
      have B := g_nonneg β¨x, N xβ© (le_refl (N x)),
      rw [A, map_add, β neg_le_iff_add_nonneg'] at B,
      have C := g_eq 0 (N x),
      simp only [submodule.coe_zero, f.map_zero, sub_zero] at C,
      rwa β C } },
  { exact Ξ» x hx, le_trans (hf _) hx },
  { rintros β¨x, yβ©,
    refine β¨β¨(0, N x - y), β¨f.domain.zero_mem, trivialβ©β©, _β©,
    simp only [convex_cone.mem_mk, mem_set_of_eq, subtype.coe_mk, prod.fst_add, prod.snd_add,
      zero_add, sub_add_cancel] }
end

/-! ### The dual cone -/

section dual
variables {H : Type*} [inner_product_space β H] (s t : set H)
open_locale real_inner_product_space

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 β€ βͺ x, y β«`. -/
noncomputable def set.inner_dual_cone (s : set H) : convex_cone β H :=
{ carrier := { y | β x β s, 0 β€ βͺ x, y β« },
  smul_mem' := Ξ» c hc y hy x hx,
  begin
    rw real_inner_smul_right,
    exact mul_nonneg hc.le (hy x hx)
  end,
  add_mem' := Ξ» u hu v hv x hx,
  begin
    rw inner_add_right,
    exact add_nonneg (hu x hx) (hv x hx)
  end }

lemma mem_inner_dual_cone (y : H) (s : set H) :
  y β s.inner_dual_cone β β x β s, 0 β€ βͺ x, y β« := by refl

@[simp] lemma inner_dual_cone_empty : (β : set H).inner_dual_cone = β€ :=
convex_cone.ext' (eq_univ_of_forall
  (Ξ» x y hy, false.elim (set.not_mem_empty _ hy)))

lemma inner_dual_cone_le_inner_dual_cone (h : t β s) :
  s.inner_dual_cone β€ t.inner_dual_cone :=
Ξ» y hy x hx, hy x (h hx)

lemma pointed_inner_dual_cone : s.inner_dual_cone.pointed :=
Ξ» x hx, by rw inner_zero_right

end dual
