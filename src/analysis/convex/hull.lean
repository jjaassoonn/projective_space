/-
Copyright (c) 2020 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, YaÃ«l Dillies
-/
import analysis.convex.basic
import order.closure

/-!
# Convex hull

This file defines the convex hull of a set `s` in a module. `convex_hull ð s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull ð s` is automatically elaborated as
`â(convex_hull ð) s`.
-/

open set

variables {ð E F : Type*}

section convex_hull
section ordered_semiring
variables [ordered_semiring ð]

section add_comm_monoid
variables (ð) [add_comm_monoid E] [add_comm_monoid F] [module ð E] [module ð F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convex_hull : closure_operator (set E) :=
closure_operator.mkâ
  (Î» s, â (t : set E) (hst : s â t) (ht : convex ð t), t)
  (convex ð)
  (Î» s, set.subset_Inter (Î» t, set.subset_Inter $ Î» hst, set.subset_Inter $ Î» ht, hst))
  (Î» s, convex_Inter $ Î» t, convex_Inter $ Î» ht, convex_Inter id)
  (Î» s t hst ht, set.Inter_subset_of_subset t $ set.Inter_subset_of_subset hst $
  set.Inter_subset _ ht)

variables (s : set E)

lemma subset_convex_hull : s â convex_hull ð s := (convex_hull ð).le_closure s

lemma convex_convex_hull : convex ð (convex_hull ð s) := closure_operator.closure_mem_mkâ s

variables {ð s} {t : set E}

lemma convex_hull_min (hst : s â t) (ht : convex ð t) : convex_hull ð s â t :=
closure_operator.closure_le_mkâ_iff (show s â¤ t, from hst) ht

@[mono] lemma convex_hull_mono (hst : s â t) : convex_hull ð s â convex_hull ð t :=
(convex_hull ð).monotone hst

lemma convex.convex_hull_eq {s : set E} (hs : convex ð s) : convex_hull ð s = s :=
closure_operator.mem_mkâ_closed hs

@[simp] lemma convex_hull_univ : convex_hull ð (univ : set E) = univ :=
closure_operator.closure_top (convex_hull ð)

@[simp] lemma convex_hull_empty : convex_hull ð (â : set E) = â := convex_empty.convex_hull_eq

@[simp] lemma convex_hull_empty_iff : convex_hull ð s = â â s = â :=
begin
  split,
  { intro h,
    rw [âset.subset_empty_iff, âh],
    exact subset_convex_hull ð _ },
  { rintro rfl,
    exact convex_hull_empty }
end

@[simp] lemma convex_hull_nonempty_iff : (convex_hull ð s).nonempty â s.nonempty :=
begin
  rw [âne_empty_iff_nonempty, âne_empty_iff_nonempty, ne.def, ne.def],
  exact not_congr convex_hull_empty_iff,
end

@[simp]
lemma convex_hull_singleton {x : E} : convex_hull ð ({x} : set E) = {x} :=
(convex_singleton x).convex_hull_eq

lemma convex.convex_remove_iff_not_mem_convex_hull_remove {s : set E} (hs : convex ð s) (x : E) :
  convex ð (s \ {x}) â x â convex_hull ð (s \ {x}) :=
begin
  split,
  { rintro hsx hx,
    rw hsx.convex_hull_eq at hx,
    exact hx.2 (mem_singleton _) },
  rintro hx,
  suffices h : s \ {x} = convex_hull ð (s \ {x}), { convert convex_convex_hull ð _ },
  exact subset.antisymm (subset_convex_hull ð _) (Î» y hy, â¨convex_hull_min (diff_subset _ _) hs hy,
    by { rintro (rfl : y = x), exact hx hy }â©),
end

lemma is_linear_map.image_convex_hull {f : E â F} (hf : is_linear_map ð f) :
  f '' (convex_hull ð s) = convex_hull ð (f '' s) :=
begin
  apply set.subset.antisymm ,
  { rw set.image_subset_iff,
    exact convex_hull_min (set.image_subset_iff.1 $ subset_convex_hull ð $ f '' s)
      ((convex_convex_hull ð (f '' s)).is_linear_preimage hf) },
  { exact convex_hull_min (set.image_subset _ $ subset_convex_hull ð s)
     ((convex_convex_hull ð s).is_linear_image hf) }
end

lemma linear_map.image_convex_hull (f : E ââ[ð] F) :
  f '' (convex_hull ð s) = convex_hull ð (f '' s) :=
f.is_linear.image_convex_hull

lemma is_linear_map.convex_hull_image {f : E â F} (hf : is_linear_map ð f) (s : set E) :
  convex_hull ð (f '' s) = f '' convex_hull ð s :=
set.subset.antisymm (convex_hull_min (image_subset _ (subset_convex_hull ð s)) $
  (convex_convex_hull ð s).is_linear_image hf)
  (image_subset_iff.2 $ convex_hull_min
    (image_subset_iff.1 $ subset_convex_hull ð _)
    ((convex_convex_hull ð _).is_linear_preimage hf))

lemma linear_map.convex_hull_image (f : E ââ[ð] F) (s : set E) :
  convex_hull ð (f '' s) = f '' convex_hull ð s :=
f.is_linear.convex_hull_image s

end add_comm_monoid
end ordered_semiring

section ordered_ring
variables [ordered_ring ð]

section add_comm_group
variables [add_comm_group E] [add_comm_group F] [module ð E] [module ð F] (s : set E)

lemma affine_map.image_convex_hull (f : E âáµ[ð] F) :
  f '' (convex_hull ð s) = convex_hull ð (f '' s) :=
begin
  apply set.subset.antisymm,
  { rw set.image_subset_iff,
    refine convex_hull_min _ ((convex_convex_hull ð (âf '' s)).affine_preimage f),
    rw â set.image_subset_iff,
    exact subset_convex_hull ð (f '' s) },
  { exact convex_hull_min (set.image_subset _ (subset_convex_hull ð s))
    ((convex_convex_hull ð s).affine_image f) }
end

lemma convex_hull_subset_affine_span : convex_hull ð s â (affine_span ð s : set E) :=
convex_hull_min (subset_affine_span ð s) (affine_span ð s).convex

@[simp] lemma affine_span_convex_hull : affine_span ð (convex_hull ð s) = affine_span ð s :=
begin
  refine le_antisymm _ (affine_span_mono ð (subset_convex_hull ð s)),
  rw affine_span_le,
  exact convex_hull_subset_affine_span s,
end

end add_comm_group
end ordered_ring
end convex_hull
