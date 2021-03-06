/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.hahn_banach

/-!
# The topological dual of a normed space

In this file we define the topological dual `normed_space.dual` of a normed space, and the
continuous linear map `normed_space.inclusion_in_double_dual` from a normed space into its double
dual.

For base field `๐ = โ` or `๐ = โ`, this map is actually an isometric embedding; we provide a
version `normed_space.inclusion_in_double_dual_li` of the map which is of type a bundled linear
isometric embedding, `E โโแตข[๐] (dual ๐ (dual ๐ E))`.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `semi_normed_space` and we specialize to `normed_space` when needed.

## Tags

dual
-/

noncomputable theory
open_locale classical
universes u v

namespace normed_space

section general
variables (๐ : Type*) [nondiscrete_normed_field ๐]
variables (E : Type*) [semi_normed_group E] [semi_normed_space ๐ E]
variables (F : Type*) [normed_group F] [normed_space ๐ F]

/-- The topological dual of a seminormed space `E`. -/
@[derive [inhabited, semi_normed_group, semi_normed_space ๐]] def dual := E โL[๐] ๐

instance : has_coe_to_fun (dual ๐ E) (ฮป _, E โ ๐) := continuous_linear_map.to_fun

instance : normed_group (dual ๐ F) := continuous_linear_map.to_normed_group

instance : normed_space ๐ (dual ๐ F) := continuous_linear_map.to_normed_space

instance [finite_dimensional ๐ E] : finite_dimensional ๐ (dual ๐ E) :=
continuous_linear_map.finite_dimensional

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual : E โL[๐] (dual ๐ (dual ๐ E)) :=
continuous_linear_map.apply ๐ ๐

@[simp] lemma dual_def (x : E) (f : dual ๐ E) : inclusion_in_double_dual ๐ E x f = f x := rfl

lemma inclusion_in_double_dual_norm_eq :
  โฅinclusion_in_double_dual ๐ Eโฅ = โฅ(continuous_linear_map.id ๐ (dual ๐ E))โฅ :=
continuous_linear_map.op_norm_flip _

lemma inclusion_in_double_dual_norm_le : โฅinclusion_in_double_dual ๐ Eโฅ โค 1 :=
by { rw inclusion_in_double_dual_norm_eq, exact continuous_linear_map.norm_id_le }

lemma double_dual_bound (x : E) : โฅ(inclusion_in_double_dual ๐ E) xโฅ โค โฅxโฅ :=
by simpa using continuous_linear_map.le_of_op_norm_le _ (inclusion_in_double_dual_norm_le ๐ E) x

end general

section bidual_isometry

variables (๐ : Type v) [is_R_or_C ๐]
  {E : Type u} [normed_group E] [normed_space ๐ E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
lemma norm_le_dual_bound (x : E) {M : โ} (hMp: 0 โค M) (hM : โ (f : dual ๐ E), โฅf xโฅ โค M * โฅfโฅ) :
  โฅxโฅ โค M :=
begin
  classical,
  by_cases h : x = 0,
  { simp only [h, hMp, norm_zero] },
  { obtain โจf, hfโฉ : โ g : E โL[๐] ๐, _ := exists_dual_vector ๐ x h,
    calc โฅxโฅ = โฅ(โฅxโฅ : ๐)โฅ : is_R_or_C.norm_coe_norm.symm
    ... = โฅf xโฅ : by rw hf.2
    ... โค M * โฅfโฅ : hM f
    ... = M : by rw [hf.1, mul_one] }
end

lemma eq_zero_of_forall_dual_eq_zero {x : E} (h : โ f : dual ๐ E, f x = (0 : ๐)) : x = 0 :=
norm_eq_zero.mp (le_antisymm (norm_le_dual_bound ๐ x le_rfl (ฮป f, by simp [h f])) (norm_nonneg _))

lemma eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 โ โ g : dual ๐ E, g x = 0 :=
โจฮป hx, by simp [hx], ฮป h, eq_zero_of_forall_dual_eq_zero ๐ hโฉ

lemma eq_iff_forall_dual_eq {x y : E} :
  x = y โ โ g : dual ๐ E, g x = g y :=
begin
  rw [โ sub_eq_zero, eq_zero_iff_forall_dual_eq_zero ๐ (x - y)],
  simp [sub_eq_zero],
end

/-- The inclusion of a normed space in its double dual is an isometry onto its image.-/
def inclusion_in_double_dual_li : E โโแตข[๐] (dual ๐ (dual ๐ E)) :=
{ norm_map' := begin
    intros x,
    apply le_antisymm,
    { exact double_dual_bound ๐ E x },
    rw continuous_linear_map.norm_def,
    apply le_cInf continuous_linear_map.bounds_nonempty,
    rintros c โจhc1, hc2โฉ,
    exact norm_le_dual_bound ๐ x hc1 hc2
  end,
  .. inclusion_in_double_dual ๐ E }

end bidual_isometry

end normed_space
