/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.analytic.basic
import analysis.special_functions.pow

/-!
# Representation of `formal_multilinear_series.radius` as a `liminf`

In this file we prove that the radius of convergence of a `formal_multilinear_series` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{โฅp nโฅ}}$. This lemma can't go to `basic.lean` because this
would create a circular dependency once we redefine `exp` using `formal_multilinear_series`.
-/
variables {๐ : Type*} [nondiscrete_normed_field ๐]
{E : Type*} [normed_group E] [normed_space ๐ E]
{F : Type*} [normed_group F] [normed_space ๐ F]

open_locale topological_space classical big_operators nnreal ennreal
open filter asymptotics

namespace formal_multilinear_series

variables (p : formal_multilinear_series ๐ E F)

/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{โฅp nโฅ}}$. The actual statement uses `โโฅ0` and some
coercions. -/
lemma radius_eq_liminf : p.radius = liminf at_top (ฮป n, 1/((nnnorm (p n)) ^ (1 / (n : โ)) : โโฅ0)) :=
begin
  have : โ (r : โโฅ0) {n : โ}, 0 < n โ
    ((r : โโฅ0โ) โค 1 / โ(nnnorm (p n) ^ (1 / (n : โ))) โ nnnorm (p n) * r ^ n โค 1),
  { intros r n hn,
    have : 0 < (n : โ) := nat.cast_pos.2 hn,
    conv_lhs {rw [one_div, ennreal.le_inv_iff_mul_le, โ ennreal.coe_mul,
      ennreal.coe_le_one_iff, one_div, โ nnreal.rpow_one r, โ mul_inv_cancel this.ne',
      nnreal.rpow_mul, โ nnreal.mul_rpow, โ nnreal.one_rpow (nโปยน),
      nnreal.rpow_le_rpow_iff (inv_pos.2 this), mul_comm, nnreal.rpow_nat_cast] } },
  apply le_antisymm; refine ennreal.le_of_forall_nnreal_lt (ฮป r hr, _),
  { rcases ((tfae_exists_lt_is_o_pow (ฮป n, โฅp nโฅ * r ^ n) 1).out 1 7).1 (p.is_o_of_lt_radius hr)
      with โจa, ha, Hโฉ,
    refine le_Liminf_of_le (by apply_auto_param) (eventually_map.2 $ _),
    refine H.mp ((eventually_gt_at_top 0).mono $ ฮป n hnโ hn, (this _ hnโ).2
      (nnreal.coe_le_coe.1 _)),
    push_cast,
    exact (le_abs_self _).trans (hn.trans (pow_le_one _ ha.1.le ha.2.le)) },
  { refine p.le_radius_of_is_O (is_O.of_bound 1 _),
    refine (eventually_lt_of_lt_liminf hr).mp ((eventually_gt_at_top 0).mono (ฮป n hnโ hn, _)),
    simpa using nnreal.coe_le_coe.2 ((this _ hnโ).1 hn.le) }
end

end formal_multilinear_series
