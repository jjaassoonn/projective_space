/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import analysis.convex.combination
import analysis.convex.function

/-!
# Jensen's inequality and maximum principle for convex functions

In this file, we prove the finite Jensen inequality and the finite maximum principle for convex
functions. The integral versions are to be found in `analysis.convex.integral`.

## Main declarations

Jensen's inequalities:
* `convex_on.map_center_mass_le`, `convex_on.map_sum_le`: Convex Jensen's inequality. The image of a
  convex combination of points under a convex function is less than the convex combination of the
  images.
* `concave_on.le_map_center_mass`, `concave_on.le_map_sum`: Concave Jensen's inequality.

As corollaries, we get:
* `convex_on.exists_ge_of_mem_convex_hull `: Maximum principle for convex functions.
* `concave_on.exists_le_of_mem_convex_hull`: Minimum principle for concave functions.
-/

open finset linear_map set
open_locale big_operators classical convex pointwise

variables {π E F Ξ² ΞΉ : Type*}

/-! ### Jensen's inequality -/

section jensen
variables [linear_ordered_field π] [add_comm_group E] [ordered_add_comm_group Ξ²] [module π E]
  [module π Ξ²] [ordered_smul π Ξ²] {s : set E} {f : E β Ξ²} {t : finset ΞΉ} {w : ΞΉ β π} {p : ΞΉ β E}

/-- Convex **Jensen's inequality**, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le (hf : convex_on π s f) (hβ : β i β t, 0 β€ w i)
  (hβ : 0 < β i in t, w i) (hmem : β i β t, p i β s) :
  f (t.center_mass w p) β€ t.center_mass w (f β p) :=
begin
  have hmem' : β i β t, (p i, (f β p) i) β {p : E Γ Ξ² | p.1 β s β§ f p.1 β€ p.2},
    from Ξ» i hi, β¨hmem i hi, le_rflβ©,
  convert (hf.convex_epigraph.center_mass_mem hβ hβ hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum,
      prod.smul_snd, prod.snd_sum],
end

/-- Concave **Jensen's inequality**, `finset.center_mass` version. -/
lemma concave_on.le_map_center_mass (hf : concave_on π s f) (hβ : β i β t, 0 β€ w i)
  (hβ : 0 < β i in t, w i) (hmem : β i β t, p i β s) :
  t.center_mass w (f β p) β€ f (t.center_mass w p) :=
@convex_on.map_center_mass_le π E (order_dual Ξ²) _ _ _ _ _ _ _ _ _ _ _ _ hf hβ hβ hmem

/-- Convex **Jensen's inequality**, `finset.sum` version. -/
lemma convex_on.map_sum_le (hf : convex_on π s f) (hβ : β i β t, 0 β€ w i) (hβ : β i in t, w i = 1)
  (hmem : β i β t, p i β s) :
  f (β i in t, w i β’ p i) β€ β i in t, w i β’ f (p i) :=
by simpa only [center_mass, hβ, inv_one, one_smul]
  using hf.map_center_mass_le hβ (hβ.symm βΈ zero_lt_one) hmem

/-- Concave **Jensen's inequality**, `finset.sum` version. -/
lemma concave_on.le_map_sum (hf : concave_on π s f) (hβ : β i β t, 0 β€ w i) (hβ : β i in t, w i = 1)
  (hmem : β i β t, p i β s) :
  β i in t, w i β’ f (p i) β€ f (β i in t, w i β’ p i) :=
@convex_on.map_sum_le π E (order_dual Ξ²) _ _ _ _ _ _ _ _ _ _ _ _ hf hβ hβ hmem

end jensen

/-! ### Maximum principle -/

section maximum_principle
variables [linear_ordered_field π] [add_comm_group E] [linear_ordered_add_comm_group Ξ²]
  [module π E] [module π Ξ²] [ordered_smul π Ξ²] {s : set E} {f : E β Ξ²} {t : finset ΞΉ} {w : ΞΉ β π}
  {p : ΞΉ β E}

/-- If a function `f` is convex on `s`, then the value it takes at some center of mass of points of
`s` is less than the value it takes on one of those points. -/
lemma convex_on.exists_ge_of_center_mass (h : convex_on π s f)
  (hwβ : β i β t, 0 β€ w i) (hwβ : 0 < β i in t, w i) (hp : β i β t, p i β s) :
  β i β t, f (t.center_mass w p) β€ f (p i) :=
begin
  set y := t.center_mass w p,
  suffices h : β i β t.filter (Ξ» i, w i β  0), w i β’ f y β€ w i β’ (f β p) i,
  { obtain β¨i, hi, hfiβ© := h,
    rw mem_filter at hi,
    exact β¨i, hi.1, (smul_le_smul_iff_of_pos $ (hwβ i hi.1).lt_of_ne hi.2.symm).1 hfiβ© },
  have hw' : (0 : π) < β i in filter (Ξ» i, w i β  0) t, w i := by rwa sum_filter_ne_zero,
  refine exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') _,
  rw [βsum_smul, βsmul_le_smul_iff_of_pos (inv_pos.2 hw'), inv_smul_smulβ hw'.ne',
    βfinset.center_mass, finset.center_mass_filter_ne_zero],
  exact h.map_center_mass_le hwβ hwβ hp,
  apply_instance,
end

/-- If a function `f` is concave on `s`, then the value it takes at some center of mass of points of
`s` is greater than the value it takes on one of those points. -/
lemma concave_on.exists_le_of_center_mass (h : concave_on π s f)
  (hwβ : β i β t, 0 β€ w i) (hwβ : 0 < β i in t, w i) (hp : β i β t, p i β s) :
  β i β t, f (p i) β€ f (t.center_mass w p) :=
@convex_on.exists_ge_of_center_mass π E (order_dual Ξ²) _ _ _ _ _ _ _ _ _ _ _ _ h hwβ hwβ hp

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then the eventual maximum of `f` on `convex_hull π s` lies in `s`. -/
lemma convex_on.exists_ge_of_mem_convex_hull (hf : convex_on π (convex_hull π s) f) {x}
  (hx : x β convex_hull π s) : β y β s, f x β€ f y :=
begin
  rw _root_.convex_hull_eq at hx,
  obtain β¨Ξ±, t, w, p, hwβ, hwβ, hp, rflβ© := hx,
  rcases hf.exists_ge_of_center_mass hwβ (hwβ.symm βΈ zero_lt_one)
    (Ξ» i hi, subset_convex_hull π s (hp i hi)) with β¨i, hit, Hiβ©,
  exact β¨p i, hp i hit, Hiβ©
end

/-- Minimum principle for concave functions. If a function `f` is concave on the convex hull of `s`,
then the eventual minimum of `f` on `convex_hull π s` lies in `s`. -/
lemma concave_on.exists_le_of_mem_convex_hull (hf : concave_on π (convex_hull π s) f) {x}
  (hx : x β convex_hull π s) : β y β s, f y β€ f x :=
@convex_on.exists_ge_of_mem_convex_hull π E (order_dual Ξ²) _ _ _ _ _ _ _ _ hf _ hx

end maximum_principle
