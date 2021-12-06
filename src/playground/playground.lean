import algebra.field.basic
import group_theory.group_action
import data.fin.vec_notation
import data.mv_polynomial.basic
import ring_theory.polynomial.homogeneous

open_locale big_operators

variables (𝔽 V : Type*) [field 𝔽] (n : ℕ)

def affine_coordinate : Type* := { v : fin n → 𝔽 // v ≠ 0}

lemma when_ne_zero (v : fin n → 𝔽) (h : ∃ (m : fin n), v m ≠ 0) : v ≠ 0 := λ rid,
begin
  rcases h with ⟨m, hm⟩,
  apply hm, convert congr_fun rid m,
end

instance : has_scalar (units 𝔽) (affine_coordinate 𝔽 n) :=
{ smul := λ r ⟨v, hv⟩, ⟨λ n, r * v n,
    λ rid, hv begin
      ext m, replace rid := congr_fun rid m,
      simpa only [pi.zero_apply, units.mul_right_eq_zero] using rid,
    end⟩ }

@[simp] lemma smul_eq (r : units 𝔽) (v : affine_coordinate 𝔽 n) (m : fin n):
  ((r • v).1 m) = ↑r * (v.1 m) :=
by { cases v, refl }

instance : mul_action (units 𝔽) (affine_coordinate 𝔽 n) :=
{ one_smul := λ ⟨v, hv⟩, begin ext m, unfold_coes, rw [smul_eq, units.coe_one, one_mul] end,
  mul_smul := λ r₁ r₂ v, begin
    ext m, unfold_coes,
    rw [smul_eq, smul_eq, smul_eq, ←mul_assoc], norm_cast,
  end }

def same_line (v₁ v₂ : affine_coordinate 𝔽 n) : Prop :=
  ∃ r : units 𝔽, (r • v₁ = v₂)

lemma same_line_refl : reflexive (same_line 𝔽 n) :=
λ v, ⟨1, one_smul _ v⟩

lemma same_line_symm : symmetric (same_line 𝔽 n) :=
λ v w ⟨r, h⟩, ⟨r⁻¹, by rw [←h, ←mul_smul, mul_left_inv, one_smul]⟩

lemma same_line_trans : transitive (same_line 𝔽 n) :=
λ v₁ v₂ v₃ ⟨r,hr⟩ ⟨s, hs⟩,
  ⟨s * r, by rw [←hs, ←hr, mul_smul]⟩

lemma same_line_equiv : equivalence (same_line 𝔽 n) :=
⟨same_line_refl _ _, same_line_symm _ _, same_line_trans _ _⟩

instance projective_space.setoid : setoid (affine_coordinate 𝔽 n) :=
{ r := same_line _ _,
  iseqv := same_line_equiv _ _ }

def projective_space : Type* := @quotient (affine_coordinate 𝔽 n) (projective_space.setoid _ _)


lemma projective_space.smul_out (a : affine_coordinate 𝔽 n) (r : units 𝔽) :
  ⟦r • a⟧.out ≈ r • ⟦a⟧.out :=
begin
  rcases a with ⟨v, hv⟩,
  have := quotient.out_eq (@quotient.mk (affine_coordinate 𝔽 n) (projective_space.setoid _ _)
    (⟨v, hv⟩ : affine_coordinate 𝔽 n)),
  rw quotient.eq at this,
  replace this := (symmetric.iff (same_line_symm 𝔽 n) _ _).1 this,
  rcases this with ⟨r', hr'⟩,
  rw ←hr',

  have := quotient.out_eq (@quotient.mk (affine_coordinate 𝔽 n) (projective_space.setoid _ _)
    (r • ⟨v, hv⟩ : affine_coordinate 𝔽 n)),
  rw quotient.eq at this,
  replace this := (symmetric.iff (same_line_symm 𝔽 n) _ _).1 this,
  rcases this with ⟨r'', hr''⟩,
  rw ←hr'',
  use r' * r''⁻¹,
  repeat { rw ←mul_smul },
  congr' 1, rw [inv_mul_cancel_right, mul_comm],
end

section mv_polynomial

-- variables (v : projective_space 𝔽 n)
variables {𝔽 n}

lemma eval_scalar_multiple {m : ℕ} (a : affine_coordinate 𝔽 n) (r : units 𝔽)
  (p : mv_polynomial (fin n) 𝔽) (hp : mv_polynomial.is_homogeneous p m) :
  mv_polynomial.eval (r • a).1 p = r ^ m * (mv_polynomial.eval a.1 p) :=
begin
  simp_rw [mv_polynomial.eval_eq, smul_eq, finset.mul_sum],
  apply finset.sum_congr rfl,
  intros x hx, ring_nf, congr,
  simp_rw [mul_pow], rw [finset.prod_mul_distrib, mul_comm], congr,
  rw finset.prod_pow_eq_pow_sum,
  congr,
  specialize hp (λ x, _), exact x,
  rw mv_polynomial.mem_support_iff at hx, apply hx, assumption,
  exact hp,
end

def eval_to_zero {m} (v : projective_space 𝔽 n) (p : mv_polynomial (fin n) 𝔽)
  (h : mv_polynomial.is_homogeneous p m) : Prop :=
  mv_polynomial.eval (quotient.out v).1 p = 0

lemma eval_to_zero.wd' {m} (a b : affine_coordinate 𝔽 n) (h : ⟦a⟧ = ⟦b⟧)
  (p : mv_polynomial (fin n) 𝔽) (hp : mv_polynomial.is_homogeneous p m):
  eval_to_zero ⟦a⟧ p hp → eval_to_zero ⟦b⟧ p hp := λ H,
begin
  unfold eval_to_zero at H ⊢,
  rw quotient.eq at h,
  rcases h with ⟨r, hr⟩,
  rw [←hr],
  have := projective_space.smul_out 𝔽 n a r,
  replace this := (symmetric.iff (same_line_symm 𝔽 n) _ _).1 this,
  rcases this with ⟨r', hr'⟩,
  rw [←hr', eval_scalar_multiple _ _ _ hp, eval_scalar_multiple _ _ _ hp, ←mul_assoc, H, mul_zero],
end

end mv_polynomial
