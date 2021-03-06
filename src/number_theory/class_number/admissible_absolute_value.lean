/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.fin.tuple
import data.real.basic
import combinatorics.pigeonhole
import algebra.order.euclidean_absolute_value

/-!
# Admissible absolute values
This file defines a structure `absolute_value.is_admissible` which we use to show the class number
of the ring of integers of a global field is finite.

## Main definitions

 * `absolute_value.is_admissible abv` states the absolute value `abv : R ā ā¤`
   respects the Euclidean domain structure on `R`, and that a large enough set
   of elements of `R^n` contains a pair of elements whose remainders are
   pointwise close together.

## Main results

 * `absolute_value.abs_is_admissible` shows the "standard" absolute value on `ā¤`,
   mapping negative `x` to `-x`, is admissible.
 * `polynomial.card_pow_degree_is_admissible` shows `card_pow_degree`,
   mapping `p : polynomial š½_q` to `q ^ degree p`, is admissible
-/

local infix ` āŗ `:50 := euclidean_domain.r

namespace absolute_value

variables {R : Type*} [euclidean_domain R]
variables (abv : absolute_value R ā¤)

/-- An absolute value `R ā ā¤` is admissible if it respects the Euclidean domain
structure and a large enough set of elements in `R^n` will contain a pair of
elements whose remainders are pointwise close together. -/
structure is_admissible extends is_euclidean abv :=
(card : ā ā ā)
(exists_partition' : ā (n : ā) {Īµ : ā} (hĪµ : 0 < Īµ) {b : R} (hb : b ā  0) (A : fin n ā R),
                     ā (t : fin n ā fin (card Īµ)),
                     ā iā iā, t iā = t iā ā (abv (A iā % b - A iā % b) : ā) < abv b ā¢ Īµ)

attribute [protected] is_admissible.card

namespace is_admissible

variables {abv}

/-- For all `Īµ > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
into `abv.card Īµ` sets, such that all elements in each part of remainders are close together. -/
lemma exists_partition {Ī¹ : Type*} [fintype Ī¹] {Īµ : ā} (hĪµ : 0 < Īµ) {b : R} (hb : b ā  0)
  (A : Ī¹ ā R) (h : abv.is_admissible) :
  ā (t : Ī¹ ā fin (h.card Īµ)),
  ā iā iā, t iā = t iā ā (abv (A iā % b - A iā % b) : ā) < abv b ā¢ Īµ :=
begin
  let e := fintype.equiv_fin Ī¹,
  obtain āØt, htā© := h.exists_partition' (fintype.card Ī¹) hĪµ hb (A ā e.symm),
  refine āØt ā e, Ī» iā iā h, _ā©,
  convert ht (e iā) (e iā) h; simp only [e.symm_apply_apply]
end

/-- Any large enough family of vectors in `R^n` has a pair of elements
whose remainders are close together, pointwise. -/
lemma exists_approx_aux (n : ā) (h : abv.is_admissible) :
  ā {Īµ : ā} (hĪµ : 0 < Īµ) {b : R} (hb : b ā  0) (A : fin (h.card Īµ ^ n).succ ā (fin n ā R)),
  ā (iā iā), (iā ā  iā) ā§ ā k, (abv (A iā k % b - A iā k % b) : ā) < abv b ā¢ Īµ :=
begin
  haveI := classical.dec_eq R,
  induction n with n ih,
  { intros Īµ hĪµ b hb A,
    refine āØ0, 1, _, _ā©,
    { simp },
    rintros āØi, āØā©ā© },
  intros Īµ hĪµ b hb A,
  set M := h.card Īµ with hM,
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M^n` remainders where the first components lie close together:
  obtain āØs, s_inj, hsā© : ā s : fin (M ^ n).succ ā fin (M ^ n.succ).succ,
    function.injective s ā§
    ā iā iā, (abv (A (s iā) 0 % b - A (s iā) 0 % b) : ā) < abv b ā¢ Īµ,
  { -- We can partition the `A`s into `M` subsets where
    -- the first components lie close together:
    obtain āØt, htā© : ā (t : fin (M ^ n.succ).succ ā fin M),
      ā iā iā, t iā = t iā ā (abv (A iā 0 % b - A iā 0 % b) : ā) < abv b ā¢ Īµ :=
      h.exists_partition hĪµ hb (Ī» x, A x 0),
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain āØs, hsā© := @fintype.exists_lt_card_fiber_of_mul_lt_card _ _ _ _ _ t (M ^ n)
      (by simpa only [fintype.card_fin, pow_succ] using nat.lt_succ_self (M ^ n.succ) ),
    refine āØĪ» i, (finset.univ.filter (Ī» x, t x = s)).to_list.nth_le i _, _, Ī» iā iā, ht _ _ _ā©,
    { refine i.2.trans_le _, rwa finset.length_to_list },
    { intros i j h, ext, exact list.nodup_iff_nth_le_inj.mp (finset.nodup_to_list _) _ _ _ _ h },
    have : ā i h, (finset.univ.filter (Ī» x, t x = s)).to_list.nth_le i h ā
      finset.univ.filter (Ī» x, t x = s),
    { intros i h, exact (finset.mem_to_list _).mp (list.nth_le_mem _ _ _) },
    obtain āØ_, hāā© := finset.mem_filter.mp (this iā _),
    obtain āØ_, hāā© := finset.mem_filter.mp (this iā _),
    exact hā.trans hā.symm },
  -- Since `s` is large enough, there are two elements of `A ā s`
  -- where the second components lie close together.
  obtain āØkā, kā, hk, hā© := ih hĪµ hb (Ī» x, fin.tail (A (s x))),
  refine āØs kā, s kā, Ī» h, hk (s_inj h), Ī» i, fin.cases _ (Ī» i, _) iā©,
  { exact hs kā kā },
  { exact h i },
end

/-- Any large enough family of vectors in `R^Ī¹` has a pair of elements
whose remainders are close together, pointwise. -/
lemma exists_approx {Ī¹ : Type*} [fintype Ī¹] {Īµ : ā} (hĪµ : 0 < Īµ) {b : R} (hb : b ā  0)
  (h : abv.is_admissible)
  (A : fin (h.card Īµ ^ fintype.card Ī¹).succ ā Ī¹ ā R) :
  ā (iā iā), (iā ā  iā) ā§ ā k, (abv (A iā k % b - A iā k % b) : ā) < abv b ā¢ Īµ :=
begin
  let e := fintype.equiv_fin Ī¹,
  obtain āØiā, iā, ne, hā© := h.exists_approx_aux (fintype.card Ī¹) hĪµ hb (Ī» x y, A x (e.symm y)),
  refine āØiā, iā, ne, Ī» k, _ā©,
  convert h (e k); simp only [e.symm_apply_apply]
end

end is_admissible

end absolute_value
