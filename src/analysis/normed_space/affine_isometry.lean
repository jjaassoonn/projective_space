/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.add_torsor
import analysis.normed_space.linear_isometry

/-!
# Affine isometries

In this file we define `affine_isometry ๐ P Pโ` to be an affine isometric embedding of normed
add-torsors `P` into `Pโ` over normed `๐`-spaces and `affine_isometry_equiv` to be an affine
isometric equivalence between `P` and `Pโ`.

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `linear_isometry` and `affine_map` theories.

Since many elementary properties don't require `โฅxโฅ = 0 โ x = 0` we initially set up the theory for
`semi_normed_add_torsor` and specialize to `normed_add_torsor` only when needed.

## Notation

We introduce the notation `P โแตโฑ[๐] Pโ` for `affine_isometry ๐ P Pโ`, and `P โแตโฑ[๐] Pโ` for
`affine_isometry_equiv ๐ P Pโ`.  In contrast with the notation `โโแตข` for linear isometries, `โแตข`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `โแต` is an affine map, since `โโ` has been taken by
algebra-homomorphisms.)

-/
open function set

variables (๐ : Type*) {V Vโ Vโ Vโ Vโ : Type*} {Pโ : Type*} (P Pโ : Type*) {Pโ Pโ : Type*}
    [normed_field ๐]
  [semi_normed_group V] [normed_group Vโ] [semi_normed_group Vโ] [semi_normed_group Vโ]
    [semi_normed_group Vโ]
  [semi_normed_space ๐ V] [normed_space ๐ Vโ] [semi_normed_space ๐ Vโ] [semi_normed_space ๐ Vโ]
    [semi_normed_space ๐ Vโ]
  [pseudo_metric_space P] [metric_space Pโ] [pseudo_metric_space Pโ] [pseudo_metric_space Pโ]
    [pseudo_metric_space Pโ]
  [semi_normed_add_torsor V P] [normed_add_torsor Vโ Pโ] [semi_normed_add_torsor Vโ Pโ]
    [semi_normed_add_torsor Vโ Pโ] [semi_normed_add_torsor Vโ Pโ]

include V Vโ

/-- An `๐`-affine isometric embedding of one normed add-torsor over a normed `๐`-space into
another. -/
structure affine_isometry extends P โแต[๐] Pโ :=
(norm_map : โ x : V, โฅlinear xโฅ = โฅxโฅ)

omit V Vโ
variables {๐ P Pโ}

-- `โแตแตข` would be more consistent with the linear isometry notation, but it is uglier
notation P ` โแตโฑ[`:25 ๐:25 `] `:0 Pโ:0 := affine_isometry ๐ P Pโ

namespace affine_isometry
variables (f : P โแตโฑ[๐] Pโ)

/-- The underlying linear map of an affine isometry is in fact a linear isometry. -/
protected def linear_isometry : V โโแตข[๐] Vโ :=
{ norm_map' := f.norm_map,
  .. f.linear }

@[simp] lemma linear_eq_linear_isometry : f.linear = f.linear_isometry.to_linear_map :=
by { ext, refl }

include V Vโ
instance : has_coe_to_fun (P โแตโฑ[๐] Pโ) (ฮป _, P โ Pโ) := โจฮป f, f.to_funโฉ
omit V Vโ

@[simp] lemma coe_to_affine_map : โf.to_affine_map = f := rfl

include V Vโ
lemma to_affine_map_injective : injective (to_affine_map : (P โแตโฑ[๐] Pโ) โ (P โแต[๐] Pโ))
| โจf, _โฉ โจg, _โฉ rfl := rfl

lemma coe_fn_injective : @injective (P โแตโฑ[๐] Pโ) (P โ Pโ) coe_fn :=
affine_map.coe_fn_injective.comp to_affine_map_injective

@[ext] lemma ext {f g : P โแตโฑ[๐] Pโ} (h : โ x, f x = g x) : f = g :=
coe_fn_injective $ funext h
omit V Vโ

end affine_isometry

namespace linear_isometry
variables (f : V โโแตข[๐] Vโ)

/-- Reinterpret a linear isometry as an affine isometry. -/
def to_affine_isometry : V โแตโฑ[๐] Vโ :=
{ norm_map := f.norm_map,
  .. f.to_linear_map.to_affine_map }

@[simp] lemma coe_to_affine_isometry : โ(f.to_affine_isometry : V โแตโฑ[๐] Vโ) = f := rfl

@[simp] lemma to_affine_isometry_linear_isometry : f.to_affine_isometry.linear_isometry = f :=
by { ext, refl }

-- somewhat arbitrary choice of simp direction
@[simp] lemma to_affine_isometry_to_affine_map :
  f.to_affine_isometry.to_affine_map = f.to_linear_map.to_affine_map :=
rfl

end linear_isometry

namespace affine_isometry

/-- We use `fโ` when we need the domain to be a `normed_space`. -/
variables (f : P โแตโฑ[๐] Pโ) (fโ : Pโ โแตโฑ[๐] Pโ)

@[simp] lemma map_vadd (p : P) (v : V) : f (v +แตฅ p) = f.linear_isometry v +แตฅ f p :=
f.to_affine_map.map_vadd p v

@[simp] lemma map_vsub (p1 p2 : P) : f.linear_isometry (p1 -แตฅ p2) = f p1 -แตฅ f p2 :=
f.to_affine_map.linear_map_vsub p1 p2

@[simp] lemma dist_map (x y : P) : dist (f x) (f y) = dist x y :=
by rw [dist_eq_norm_vsub Vโ, dist_eq_norm_vsub V, โ map_vsub, f.linear_isometry.norm_map]

@[simp] lemma nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by simp [nndist_dist]

@[simp] lemma edist_map (x y : P) : edist (f x) (f y) = edist x y := by simp [edist_dist]

protected lemma isometry : isometry f := f.edist_map

protected lemma injective : injective fโ := fโ.isometry.injective

@[simp] lemma map_eq_iff {x y : Pโ} : fโ x = fโ y โ x = y := fโ.injective.eq_iff

lemma map_ne {x y : Pโ} (h : x โ? y) : fโ x โ? fโ y := fโ.injective.ne h

protected lemma lipschitz : lipschitz_with 1 f := f.isometry.lipschitz

protected lemma antilipschitz : antilipschitz_with 1 f := f.isometry.antilipschitz

@[continuity] protected lemma continuous : continuous f := f.isometry.continuous

lemma ediam_image (s : set P) : emetric.diam (f '' s) = emetric.diam s :=
f.isometry.ediam_image s

lemma ediam_range : emetric.diam (range f) = emetric.diam (univ : set P) :=
f.isometry.ediam_range

lemma diam_image (s : set P) : metric.diam (f '' s) = metric.diam s :=
f.isometry.diam_image s

lemma diam_range : metric.diam (range f) = metric.diam (univ : set P) :=
f.isometry.diam_range

@[simp] lemma comp_continuous_iff {ฮฑ : Type*} [topological_space ฮฑ] {g : ฮฑ โ P} :
  continuous (f โ g) โ continuous g :=
f.isometry.comp_continuous_iff

include V
/-- The identity affine isometry. -/
def id : P โแตโฑ[๐] P := โจaffine_map.id ๐ P, ฮป x, rflโฉ

@[simp] lemma coe_id : โ(id : P โแตโฑ[๐] P) = _root_.id := rfl

@[simp] lemma id_apply (x : P) : (affine_isometry.id : P โแตโฑ[๐] P) x = x := rfl

@[simp] lemma id_to_affine_map : (id.to_affine_map : P โแต[๐] P) = affine_map.id ๐ P := rfl

instance : inhabited (P โแตโฑ[๐] P) := โจidโฉ

include Vโ Vโ
/-- Composition of affine isometries. -/
def comp (g : Pโ โแตโฑ[๐] Pโ) (f : P โแตโฑ[๐] Pโ) : P โแตโฑ[๐] Pโ :=
โจg.to_affine_map.comp f.to_affine_map, ฮป x, (g.norm_map _).trans (f.norm_map _)โฉ

@[simp] lemma coe_comp (g : Pโ โแตโฑ[๐] Pโ) (f : P โแตโฑ[๐] Pโ) :
  โ(g.comp f) = g โ f :=
rfl

omit V Vโ Vโ

@[simp] lemma id_comp : (id : Pโ โแตโฑ[๐] Pโ).comp f = f := ext $ ฮป x, rfl

@[simp] lemma comp_id : f.comp id = f := ext $ ฮป x, rfl

include V Vโ Vโ Vโ
lemma comp_assoc (f : Pโ โแตโฑ[๐] Pโ) (g : Pโ โแตโฑ[๐] Pโ) (h : P โแตโฑ[๐] Pโ) :
  (f.comp g).comp h = f.comp (g.comp h) :=
rfl
omit Vโ Vโ Vโ

instance : monoid (P โแตโฑ[๐] P) :=
{ one := id,
  mul := comp,
  mul_assoc := comp_assoc,
  one_mul := id_comp,
  mul_one := comp_id }

@[simp] lemma coe_one : โ(1 : P โแตโฑ[๐] P) = _root_.id := rfl
@[simp] lemma coe_mul (f g : P โแตโฑ[๐] P) : โ(f * g) = f โ g := rfl

end affine_isometry

-- remark: by analogy with the `linear_isometry` file from which this is adapted, there should
-- follow here a section defining an "inclusion" affine isometry from `p : affine_subspace ๐ P`
-- into `P`; we omit this for now

variables (๐ P Pโ)
include V Vโ

/-- A affine isometric equivalence between two normed vector spaces. -/
structure affine_isometry_equiv extends P โแต[๐] Pโ :=
(norm_map : โ x, โฅlinear xโฅ = โฅxโฅ)

variables {๐ P Pโ}
omit V Vโ

-- `โแตแตข` would be more consistent with the linear isometry equiv notation, but it is uglier
notation P ` โแตโฑ[`:25 ๐:25 `] `:0 Pโ:0 := affine_isometry_equiv ๐ P Pโ

namespace affine_isometry_equiv

variables (e : P โแตโฑ[๐] Pโ)

/-- The underlying linear equiv of an affine isometry equiv is in fact a linear isometry equiv. -/
protected def linear_isometry_equiv : V โโแตข[๐] Vโ :=
{ norm_map' := e.norm_map,
  .. e.linear }

@[simp] lemma linear_eq_linear_isometry : e.linear = e.linear_isometry_equiv.to_linear_equiv :=
by { ext, refl }

include V Vโ
instance : has_coe_to_fun (P โแตโฑ[๐] Pโ) (ฮป _, P โ Pโ) := โจฮป f, f.to_funโฉ

@[simp] lemma coe_mk (e : P โแต[๐] Pโ) (he : โ x, โฅe.linear xโฅ = โฅxโฅ) :
  โ(mk e he) = e :=
rfl

@[simp] lemma coe_to_affine_equiv (e : P โแตโฑ[๐] Pโ) : โe.to_affine_equiv = e := rfl

lemma to_affine_equiv_injective : injective (to_affine_equiv : (P โแตโฑ[๐] Pโ) โ (P โแต[๐] Pโ))
| โจe, _โฉ โจ_, _โฉ rfl := rfl

@[ext] lemma ext {e e' : P โแตโฑ[๐] Pโ} (h : โ x, e x = e' x) : e = e' :=
to_affine_equiv_injective $ affine_equiv.ext h
omit V Vโ

/-- Reinterpret a `affine_isometry_equiv` as a `affine_isometry`. -/
def to_affine_isometry : P โแตโฑ[๐] Pโ := โจe.1.to_affine_map, e.2โฉ

@[simp] lemma coe_to_affine_isometry : โe.to_affine_isometry = e := rfl

/-- Construct an affine isometry equivalence by verifying the relation between the map and its
linear part at one base point. Namely, this function takes a map `e : Pโ โ Pโ`, a linear isometry
equivalence `e' : Vโ โแตขโ[k] Vโ`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -แตฅ p) +แตฅ e p`. -/
def mk' (e : Pโ โ Pโ) (e' : Vโ โโแตข[๐] Vโ) (p : Pโ) (h : โ p' : Pโ, e p' = e' (p' -แตฅ p) +แตฅ e p) :
  Pโ โแตโฑ[๐] Pโ :=
{ norm_map := e'.norm_map,
  .. affine_equiv.mk' e e'.to_linear_equiv p h }

@[simp] lemma coe_mk' (e : Pโ โ Pโ) (e' : Vโ โโแตข[๐] Vโ) (p h) : โ(mk' e e' p h) = e := rfl
@[simp] lemma linear_isometry_equiv_mk' (e : Pโ โ Pโ) (e' : Vโ โโแตข[๐] Vโ) (p h) :
  (mk' e e' p h).linear_isometry_equiv = e' := by { ext, refl }

end affine_isometry_equiv

namespace linear_isometry_equiv
variables (e : V โโแตข[๐] Vโ)

/-- Reinterpret a linear isometry equiv as an affine isometry equiv. -/
def to_affine_isometry_equiv  : V โแตโฑ[๐] Vโ :=
{ norm_map := e.norm_map,
  .. e.to_linear_equiv.to_affine_equiv }

@[simp] lemma coe_to_affine_isometry_equiv : โ(e.to_affine_isometry_equiv : V โแตโฑ[๐] Vโ) = e := rfl

@[simp] lemma to_affine_isometry_equiv_linear_isometry_equiv :
  e.to_affine_isometry_equiv.linear_isometry_equiv = e :=
by { ext, refl }

-- somewhat arbitrary choice of simp direction
@[simp] lemma to_affine_isometry_equiv_to_affine_equiv :
  e.to_affine_isometry_equiv.to_affine_equiv = e.to_linear_equiv.to_affine_equiv :=
rfl

-- somewhat arbitrary choice of simp direction
@[simp] lemma to_affine_isometry_equiv_to_affine_isometry :
  e.to_affine_isometry_equiv.to_affine_isometry = e.to_linear_isometry.to_affine_isometry :=
rfl

end linear_isometry_equiv

namespace affine_isometry_equiv
variables (e : P โแตโฑ[๐] Pโ)

protected lemma isometry : isometry e := e.to_affine_isometry.isometry

/-- Reinterpret a `affine_isometry_equiv` as an `isometric`. -/
def to_isometric : P โแตข Pโ := โจe.to_affine_equiv.to_equiv, e.isometryโฉ

@[simp] lemma coe_to_isometric : โe.to_isometric = e := rfl

include V Vโ
lemma range_eq_univ (e : P โแตโฑ[๐] Pโ) : set.range e = set.univ :=
by { rw โ coe_to_isometric, exact isometric.range_eq_univ _, }
omit V Vโ

/-- Reinterpret a `affine_isometry_equiv` as an `homeomorph`. -/
def to_homeomorph : P โโ Pโ := e.to_isometric.to_homeomorph

@[simp] lemma coe_to_homeomorph : โe.to_homeomorph = e := rfl

protected lemma continuous : continuous e := e.isometry.continuous
protected lemma continuous_at {x} : continuous_at e x := e.continuous.continuous_at
protected lemma continuous_on {s} : continuous_on e s := e.continuous.continuous_on

protected lemma continuous_within_at {s x} : continuous_within_at e s x :=
e.continuous.continuous_within_at

variables (๐ P)
include V

/-- Identity map as a `affine_isometry_equiv`. -/
def refl : P โแตโฑ[๐] P := โจaffine_equiv.refl ๐ P, ฮป x, rflโฉ

variables {๐ P}

instance : inhabited (P โแตโฑ[๐] P) := โจrefl ๐ Pโฉ

@[simp] lemma coe_refl : โ(refl ๐ P) = id := rfl
@[simp] lemma to_affine_equiv_refl : (refl ๐ P).to_affine_equiv = affine_equiv.refl ๐ P := rfl
@[simp] lemma to_isometric_refl : (refl ๐ P).to_isometric = isometric.refl P := rfl
@[simp] lemma to_homeomorph_refl : (refl ๐ P).to_homeomorph = homeomorph.refl P := rfl
omit V

/-- The inverse `affine_isometry_equiv`. -/
def symm : Pโ โแตโฑ[๐] P :=
{ norm_map := e.linear_isometry_equiv.symm.norm_map,
  .. e.to_affine_equiv.symm }

@[simp] lemma apply_symm_apply (x : Pโ) : e (e.symm x) = x := e.to_affine_equiv.apply_symm_apply x
@[simp] lemma symm_apply_apply (x : P) : e.symm (e x) = x := e.to_affine_equiv.symm_apply_apply x
@[simp] lemma symm_symm : e.symm.symm = e := ext $ ฮป x, rfl

@[simp] lemma to_affine_equiv_symm : e.to_affine_equiv.symm = e.symm.to_affine_equiv := rfl
@[simp] lemma to_isometric_symm : e.to_isometric.symm = e.symm.to_isometric := rfl
@[simp] lemma to_homeomorph_symm : e.to_homeomorph.symm = e.symm.to_homeomorph := rfl

include Vโ
/-- Composition of `affine_isometry_equiv`s as a `affine_isometry_equiv`. -/
def trans (e' : Pโ โแตโฑ[๐] Pโ) : P โแตโฑ[๐] Pโ :=
โจe.to_affine_equiv.trans e'.to_affine_equiv, ฮป x, (e'.norm_map _).trans (e.norm_map _)โฉ

include V Vโ
@[simp] lemma coe_trans (eโ : P โแตโฑ[๐] Pโ) (eโ : Pโ โแตโฑ[๐] Pโ) : โ(eโ.trans eโ) = eโ โ eโ := rfl
omit V Vโ Vโ

@[simp] lemma trans_refl : e.trans (refl ๐ Pโ) = e := ext $ ฮป x, rfl
@[simp] lemma refl_trans : (refl ๐ P).trans e = e := ext $ ฮป x, rfl
@[simp] lemma self_trans_symm : e.trans e.symm = refl ๐ P := ext e.symm_apply_apply
@[simp] lemma symm_trans_self : e.symm.trans e = refl ๐ Pโ := ext e.apply_symm_apply

include V Vโ Vโ
@[simp] lemma coe_symm_trans (eโ : P โแตโฑ[๐] Pโ) (eโ : Pโ โแตโฑ[๐] Pโ) :
  โ(eโ.trans eโ).symm = eโ.symm โ eโ.symm :=
rfl

include Vโ
lemma trans_assoc (ePPโ : P โแตโฑ[๐] Pโ) (ePโG : Pโ โแตโฑ[๐] Pโ) (eGG' : Pโ โแตโฑ[๐] Pโ) :
  ePPโ.trans (ePโG.trans eGG') = (ePPโ.trans ePโG).trans eGG' :=
rfl
omit Vโ Vโ Vโ

/-- The group of affine isometries of a `normed_add_torsor`, `P`. -/
instance : group (P โแตโฑ[๐] P) :=
{ mul := ฮป eโ eโ, eโ.trans eโ,
  one := refl _ _,
  inv := symm,
  one_mul := trans_refl,
  mul_one := refl_trans,
  mul_assoc := ฮป _ _ _, trans_assoc _ _ _,
  mul_left_inv := self_trans_symm }

@[simp] lemma coe_one : โ(1 : P โแตโฑ[๐] P) = id := rfl
@[simp] lemma coe_mul (e e' : P โแตโฑ[๐] P) : โ(e * e') = e โ e' := rfl
@[simp] lemma coe_inv (e : P โแตโฑ[๐] P) : โ(eโปยน) = e.symm := rfl

omit V

@[simp] lemma map_vadd (p : P) (v : V) : e (v +แตฅ p) = e.linear_isometry_equiv v +แตฅ e p :=
e.to_affine_isometry.map_vadd p v

@[simp] lemma map_vsub (p1 p2 : P) : e.linear_isometry_equiv (p1 -แตฅ p2) = e p1 -แตฅ e p2 :=
e.to_affine_isometry.map_vsub p1 p2

@[simp] lemma dist_map (x y : P) : dist (e x) (e y) = dist x y :=
e.to_affine_isometry.dist_map x y

@[simp] lemma edist_map (x y : P) : edist (e x) (e y) = edist x y :=
e.to_affine_isometry.edist_map x y

protected lemma bijective : bijective e := e.1.bijective
protected lemma injective : injective e := e.1.injective
protected lemma surjective : surjective e := e.1.surjective

@[simp] lemma map_eq_iff {x y : P} : e x = e y โ x = y := e.injective.eq_iff

lemma map_ne {x y : P} (h : x โ? y) : e x โ? e y := e.injective.ne h

protected lemma lipschitz : lipschitz_with 1 e := e.isometry.lipschitz

protected lemma antilipschitz : antilipschitz_with 1 e := e.isometry.antilipschitz

@[simp] lemma ediam_image (s : set P) : emetric.diam (e '' s) = emetric.diam s :=
e.isometry.ediam_image s

@[simp] lemma diam_image (s : set P) : metric.diam (e '' s) = metric.diam s :=
e.isometry.diam_image s

variables {ฮฑ : Type*} [topological_space ฮฑ]

@[simp] lemma comp_continuous_on_iff {f : ฮฑ โ P} {s : set ฮฑ} :
  continuous_on (e โ f) s โ continuous_on f s :=
e.isometry.comp_continuous_on_iff

@[simp] lemma comp_continuous_iff {f : ฮฑ โ P} :
  continuous (e โ f) โ continuous f :=
e.isometry.comp_continuous_iff

section constructions

variables (๐)
/-- The map `v โฆ v +แตฅ p` as an affine isometric equivalence between `V` and `P`. -/
def vadd_const (p : P) : V โแตโฑ[๐] P :=
{ norm_map := ฮป x, rfl,
  .. affine_equiv.vadd_const ๐ p }
variables {๐}

include V
@[simp] lemma coe_vadd_const (p : P) : โ(vadd_const ๐ p) = ฮป v, v +แตฅ p := rfl

@[simp] lemma coe_vadd_const_symm (p : P) : โ(vadd_const ๐ p).symm = ฮป p', p' -แตฅ p :=
rfl

@[simp] lemma vadd_const_to_affine_equiv (p : P) :
  (vadd_const ๐ p).to_affine_equiv = affine_equiv.vadd_const ๐ p :=
rfl
omit V

variables (๐)
/-- `p' โฆ p -แตฅ p'` as an affine isometric equivalence. -/
def const_vsub (p : P) : P โแตโฑ[๐] V :=
{ norm_map := norm_neg,
  .. affine_equiv.const_vsub ๐ p }
variables {๐}

include V
@[simp] lemma coe_const_vsub (p : P) : โ(const_vsub ๐ p) = (-แตฅ) p := rfl

@[simp] lemma symm_const_vsub (p : P) :
  (const_vsub ๐ p).symm
  = (linear_isometry_equiv.neg ๐).to_affine_isometry_equiv.trans (vadd_const ๐ p) :=
by { ext, refl }
omit V

variables (๐ P)
/-- Translation by `v` (that is, the map `p โฆ v +แตฅ p`) as an affine isometric automorphism of `P`.
-/
def const_vadd (v : V) : P โแตโฑ[๐] P :=
{ norm_map := ฮป x, rfl,
  .. affine_equiv.const_vadd ๐ P v }
variables {๐ P}

@[simp] lemma coe_const_vadd (v : V) : โ(const_vadd ๐ P v : P โแตโฑ[๐] P) = (+แตฅ) v := rfl

@[simp] lemma const_vadd_zero : const_vadd ๐ P (0:V) = refl ๐ P := ext $ zero_vadd V

include ๐ V
/-- The map `g` from `V` to `Vโ` corresponding to a map `f` from `P` to `Pโ`, at a base point `p`,
is an isometry if `f` is one. -/
lemma vadd_vsub {f : P โ Pโ} (hf : isometry f) {p : P} {g : V โ Vโ}
  (hg : โ v, g v = f (v +แตฅ p) -แตฅ f p) : isometry g :=
begin
  convert (vadd_const ๐ (f p)).symm.isometry.comp (hf.comp (vadd_const ๐ p).isometry),
  exact funext hg
end
omit ๐

variables (๐)
/-- Point reflection in `x` as an affine isometric automorphism. -/
def point_reflection (x : P) : P โแตโฑ[๐] P := (const_vsub ๐ x).trans (vadd_const ๐ x)
variables {๐}

lemma point_reflection_apply (x y : P) : (point_reflection ๐ x) y = x -แตฅ y +แตฅ x := rfl

@[simp] lemma point_reflection_to_affine_equiv (x : P) :
  (point_reflection ๐ x).to_affine_equiv = affine_equiv.point_reflection ๐ x := rfl

@[simp] lemma point_reflection_self (x : P) : point_reflection ๐ x x = x :=
affine_equiv.point_reflection_self ๐ x

lemma point_reflection_involutive (x : P) : function.involutive (point_reflection ๐ x) :=
equiv.point_reflection_involutive x

@[simp] lemma point_reflection_symm (x : P) : (point_reflection ๐ x).symm = point_reflection ๐ x :=
to_affine_equiv_injective $ affine_equiv.point_reflection_symm ๐ x

@[simp] lemma dist_point_reflection_fixed (x y : P) :
  dist (point_reflection ๐ x y) x = dist y x :=
by rw [โ (point_reflection ๐ x).dist_map y x, point_reflection_self]

lemma dist_point_reflection_self' (x y : P) :
  dist (point_reflection ๐ x y) y = โฅbit0 (x -แตฅ y)โฅ :=
by rw [point_reflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, bit0]

lemma dist_point_reflection_self (x y : P) :
  dist (point_reflection ๐ x y) y = โฅ(2:๐)โฅ * dist x y :=
by rw [dist_point_reflection_self', โ two_smul' ๐ (x -แตฅ y), norm_smul, โ dist_eq_norm_vsub V]

lemma point_reflection_fixed_iff [invertible (2:๐)] {x y : P} :
  point_reflection ๐ x y = y โ y = x :=
affine_equiv.point_reflection_fixed_iff_of_module ๐

variables [semi_normed_space โ V]

lemma dist_point_reflection_self_real (x y : P) :
  dist (point_reflection โ x y) y = 2 * dist x y :=
by { rw [dist_point_reflection_self, real.norm_two] }

@[simp] lemma point_reflection_midpoint_left (x y : P) :
  point_reflection โ (midpoint โ x y) x = y :=
affine_equiv.point_reflection_midpoint_left x y

@[simp] lemma point_reflection_midpoint_right (x y : P) :
  point_reflection โ (midpoint โ x y) y = x :=
affine_equiv.point_reflection_midpoint_right x y

end constructions

end affine_isometry_equiv

include V Vโ

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
lemma affine_map.continuous_linear_iff {f : P โแต[๐] Pโ} :
  continuous f.linear โ continuous f :=
begin
  inhabit P,
  have : (f.linear : V โ Vโ) =
    (affine_isometry_equiv.vadd_const ๐ $ f $ default P).to_homeomorph.symm โ f โ
      (affine_isometry_equiv.vadd_const ๐ $ default P).to_homeomorph,
  { ext v, simp },
  rw this,
  simp only [homeomorph.comp_continuous_iff, homeomorph.comp_continuous_iff'],
end

/-- If `f` is an affine map, then its linear part is an open map iff `f` is an open map. -/
lemma affine_map.is_open_map_linear_iff {f : P โแต[๐] Pโ} :
  is_open_map f.linear โ is_open_map f :=
begin
  inhabit P,
  have : (f.linear : V โ Vโ) =
    (affine_isometry_equiv.vadd_const ๐ $ f $ default P).to_homeomorph.symm โ f โ
      (affine_isometry_equiv.vadd_const ๐ $ default P).to_homeomorph,
  { ext v, simp },
  rw this,
  simp only [homeomorph.comp_is_open_map_iff, homeomorph.comp_is_open_map_iff'],
end
