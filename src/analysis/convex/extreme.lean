/-
Copyright (c) 2021 YaÃ«l Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YaÃ«l Dillies, Bhavik Mehta
-/
import analysis.convex.hull

/-!
# Extreme sets

This file defines extreme sets and extreme points for sets in a module.

An extreme set of `A` is a subset of `A` that is as far as it can get in any outward direction: If
point `x` is in it and point `y â A`, then the line passing through `x` and `y` leaves `A` at `x`.
This is an analytic notion of "being on the side of". It is weaker than being exposed (see
`is_exposed.is_extreme`).

## Main declarations

* `is_extreme ð A B`: States that `B` is an extreme set of `A` (in the literature, `A` is often
  implicit).
* `set.extreme_points ð A`: Set of extreme points of `A` (corresponding to extreme singletons).
* `convex.mem_extreme_points_iff_convex_diff`: A useful equivalent condition to being an extreme
  point: `x` is an extreme point iff `A \ {x}` is convex.

## Implementation notes

The exact definition of extremeness has been carefully chosen so as to make as many lemmas
unconditional (in particular, the Krein-Milman theorem doesn't need the set to be convex!).
In practice, `A` is often assumed to be a convex set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Define intrinsic frontier and prove lemmas related to extreme sets and points.

More not-yet-PRed stuff is available on the branch `sperner_again`.
-/

open_locale classical affine
open set

variables (ð : Type*) {E : Type*}

section has_scalar
variables [ordered_semiring ð] [add_comm_monoid E] [has_scalar ð E]

/-- A set `B` is an extreme subset of `A` if `B â A` and all points of `B` only belong to open
segments whose ends are in `B`. -/
def is_extreme (A B : set E) : Prop :=
B â A â§ â xâ xâ â A, â x â B, x â open_segment ð xâ xâ â xâ â B â§ xâ â B

/-- A point `x` is an extreme point of a set `A` if `x` belongs to no open segment with ends in
`A`, except for the obvious `open_segment x x`. -/
def set.extreme_points (A : set E) : set E :=
{x â A | â (xâ xâ â A), x â open_segment ð xâ xâ â xâ = x â§ xâ = x}

@[refl] protected lemma is_extreme.refl (A : set E) :
  is_extreme ð A A :=
â¨subset.rfl, Î» xâ xâ hxâA hxâA x hxA hx, â¨hxâA, hxâAâ©â©

variables {ð} {A B C : set E} {x : E}

protected lemma is_extreme.rfl :
  is_extreme ð A A :=
is_extreme.refl ð A

@[trans] protected lemma is_extreme.trans (hAB : is_extreme ð A B) (hBC : is_extreme ð B C) :
  is_extreme ð A C :=
begin
  use subset.trans hBC.1 hAB.1,
  rintro xâ xâ hxâA hxâA x hxC hx,
  obtain â¨hxâB, hxâBâ© := hAB.2 xâ xâ hxâA hxâA x (hBC.1 hxC) hx,
  exact hBC.2 xâ xâ hxâB hxâB x hxC hx,
end

protected lemma is_extreme.antisymm :
  anti_symmetric (is_extreme ð : set E â set E â Prop) :=
Î» A B hAB hBA, subset.antisymm hBA.1 hAB.1

instance : is_partial_order (set E) (is_extreme ð) :=
{ refl := is_extreme.refl ð,
  trans := Î» A B C, is_extreme.trans,
  antisymm := is_extreme.antisymm }

lemma is_extreme.inter (hAB : is_extreme ð A B) (hAC : is_extreme ð A C) :
  is_extreme ð A (B â© C) :=
begin
  use subset.trans (inter_subset_left _ _) hAB.1,
  rintro xâ xâ hxâA hxâA x â¨hxB, hxCâ© hx,
  obtain â¨hxâB, hxâBâ© := hAB.2 xâ xâ hxâA hxâA x hxB hx,
  obtain â¨hxâC, hxâCâ© := hAC.2 xâ xâ hxâA hxâA x hxC hx,
  exact â¨â¨hxâB, hxâCâ©, hxâB, hxâCâ©,
end

protected lemma is_extreme.mono (hAC : is_extreme ð A C) (hBA : B â A) (hCB : C â B) :
  is_extreme ð B C :=
â¨hCB, Î» xâ xâ hxâB hxâB x hxC hx, hAC.2 xâ xâ (hBA hxâB) (hBA hxâB) x hxC hxâ©

lemma is_extreme_Inter {Î¹ : Type*} [nonempty Î¹] {F : Î¹ â set E}
  (hAF : â i : Î¹, is_extreme ð A (F i)) :
  is_extreme ð A (â i : Î¹, F i) :=
begin
  obtain i := classical.arbitrary Î¹,
  use Inter_subset_of_subset i (hAF i).1,
  rintro xâ xâ hxâA hxâA x hxF hx,
  simp_rw mem_Inter at â¢ hxF,
  have h := Î» i, (hAF i).2 xâ xâ hxâA hxâA x (hxF i) hx,
  exact â¨Î» i, (h i).1, Î» i, (h i).2â©,
end

lemma is_extreme_bInter {F : set (set E)} (hF : F.nonempty)
  (hAF : â B â F, is_extreme ð A B) :
  is_extreme ð A (â B â F, B) :=
begin
  obtain â¨B, hBâ© := hF,
  refine â¨(bInter_subset_of_mem hB).trans (hAF B hB).1, Î» xâ xâ hxâA hxâA x hxF hx, _â©,
  simp_rw mem_bInter_iff at â¢ hxF,
  have h := Î» B hB, (hAF B hB).2 xâ xâ hxâA hxâA x (hxF B hB) hx,
  exact â¨Î» B hB, (h B hB).1, Î» B hB, (h B hB).2â©,
end

lemma is_extreme_sInter {F : set (set E)} (hF : F.nonempty)
  (hAF : â B â F, is_extreme ð A B) :
  is_extreme ð A (ââ F) :=
begin
  obtain â¨B, hBâ© := hF,
  refine â¨(sInter_subset_of_mem hB).trans (hAF B hB).1, Î» xâ xâ hxâA hxâA x hxF hx, _â©,
  simp_rw mem_sInter at â¢ hxF,
  have h := Î» B hB, (hAF B hB).2 xâ xâ hxâA hxâA x (hxF B hB) hx,
  exact â¨Î» B hB, (h B hB).1, Î» B hB, (h B hB).2â©,
end

lemma extreme_points_def :
  x â A.extreme_points ð â x â A â§ â (xâ xâ â A), x â open_segment ð xâ xâ â xâ = x â§ xâ = x :=
iff.rfl

/-- x is an extreme point to A iff {x} is an extreme set of A. -/
lemma mem_extreme_points_iff_extreme_singleton :
  x â A.extreme_points ð â is_extreme ð A {x} :=
begin
  refine â¨_, Î» hx, â¨singleton_subset_iff.1 hx.1, Î» xâ xâ hxâ hxâ, hx.2 xâ xâ hxâ hxâ x rflâ©â©,
  rintro â¨hxA, hAxâ©,
  use singleton_subset_iff.2 hxA,
  rintro xâ xâ hxâA hxâA y (rfl : y = x),
  exact hAx xâ xâ hxâA hxâA,
end

lemma extreme_points_subset : A.extreme_points ð â A := Î» x hx, hx.1

@[simp] lemma extreme_points_empty :
  (â : set E).extreme_points ð = â :=
subset_empty_iff.1 extreme_points_subset

@[simp] lemma extreme_points_singleton :
  ({x} : set E).extreme_points ð = {x} :=
extreme_points_subset.antisymm $ singleton_subset_iff.2
  â¨mem_singleton x, Î» xâ xâ hxâ hxâ _, â¨hxâ, hxââ©â©

lemma inter_extreme_points_subset_extreme_points_of_subset (hBA : B â A) :
  B â© A.extreme_points ð â B.extreme_points ð :=
Î» x â¨hxB, hxAâ©, â¨hxB, Î» xâ xâ hxâ hxâ hx, hxA.2 xâ xâ (hBA hxâ) (hBA hxâ) hxâ©

lemma is_extreme.extreme_points_subset_extreme_points (hAB : is_extreme ð A B) :
  B.extreme_points ð â A.extreme_points ð :=
Î» x hx, mem_extreme_points_iff_extreme_singleton.2 (hAB.trans
  (mem_extreme_points_iff_extreme_singleton.1 hx))

lemma is_extreme.extreme_points_eq (hAB : is_extreme ð A B) :
  B.extreme_points ð = B â© A.extreme_points ð :=
subset.antisymm (Î» x hx, â¨hx.1, hAB.extreme_points_subset_extreme_points hxâ©)
  (inter_extreme_points_subset_extreme_points_of_subset hAB.1)

end has_scalar

section ordered_semiring
variables {ð} [ordered_semiring ð] [add_comm_group E] [module ð E] {A B : set E} {x : E}

lemma is_extreme.convex_diff (hA : convex ð A) (hAB : is_extreme ð A B) :
  convex ð (A \ B) :=
convex_iff_open_segment_subset.2 (Î» xâ xâ â¨hxâA, hxâBâ© â¨hxâA, hxâBâ© x hx,
    â¨hA.open_segment_subset hxâA hxâA hx, Î» hxB, hxâB (hAB.2 xâ xâ hxâA hxâA x hxB hx).1â©)

end ordered_semiring

section linear_ordered_field
variables {ð} [linear_ordered_field ð] [add_comm_group E] [module ð E] {A B : set E} {x : E}

/-- A useful restatement using `segment`: `x` is an extreme point iff the only (closed) segments
that contain it are those with `x` as one of their endpoints. -/
lemma mem_extreme_points_iff_forall_segment [no_zero_smul_divisors ð E] :
  x â A.extreme_points ð â x â A â§ â (xâ xâ â A), x â segment ð xâ xâ â xâ = x â¨ xâ = x :=
begin
  split,
  { rintro â¨hxA, hAxâ©,
    use hxA,
    rintro xâ xâ hxâ hxâ hx,
    by_contra,
    push_neg at h,
    exact h.1 (hAx _ _ hxâ hxâ (mem_open_segment_of_ne_left_right ð h.1 h.2 hx)).1 },
  rintro â¨hxA, hAxâ©,
  use hxA,
  rintro xâ xâ hxâ hxâ hx,
  obtain rfl | rfl := hAx xâ xâ hxâ hxâ (open_segment_subset_segment ð _ _ hx),
  { exact â¨rfl, (left_mem_open_segment_iff.1 hx).symmâ© },
  exact â¨right_mem_open_segment_iff.1 hx, rflâ©,
end

lemma convex.mem_extreme_points_iff_convex_diff (hA : convex ð A) :
  x â A.extreme_points ð â x â A â§ convex ð (A \ {x}) :=
begin
  use Î» hx, â¨hx.1, (mem_extreme_points_iff_extreme_singleton.1 hx).convex_diff hAâ©,
  rintro â¨hxA, hAxâ©,
  refine mem_extreme_points_iff_forall_segment.2 â¨hxA, Î» xâ xâ hxâ hxâ hx, _â©,
  rw convex_iff_segment_subset at hAx,
  by_contra,
  push_neg at h,
  exact (hAx â¨hxâ, Î» hxâ, h.1 (mem_singleton_iff.2 hxâ)â©
    â¨hxâ, Î» hxâ, h.2 (mem_singleton_iff.2 hxâ)â© hx).2 rfl,
end

lemma convex.mem_extreme_points_iff_mem_diff_convex_hull_diff (hA : convex ð A) :
  x â A.extreme_points ð â x â A \ convex_hull ð (A \ {x}) :=
by rw [hA.mem_extreme_points_iff_convex_diff, hA.convex_remove_iff_not_mem_convex_hull_remove,
  mem_diff]

lemma extreme_points_convex_hull_subset :
  (convex_hull ð A).extreme_points ð â A :=
begin
  rintro x hx,
  rw (convex_convex_hull ð _).mem_extreme_points_iff_convex_diff at hx,
  by_contra,
  exact (convex_hull_min (subset_diff.2 â¨subset_convex_hull ð _, disjoint_singleton_right.2 hâ©) hx.2
    hx.1).2 rfl,
end

end linear_ordered_field
