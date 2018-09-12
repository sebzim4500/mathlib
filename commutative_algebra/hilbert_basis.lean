-- Hilbert basis theorem

import ring_theory.noetherian
import data.polynomial

open polynomial

local attribute [instance, priority 1] classical.prop_decidable

lemma polynomial.zero_ring_degree {R} [comm_ring R] (h : (0 : R) = 1) (f : polynomial R) :
degree f = ⊥ := by rw ←leading_coeff_eq_zero_iff_deg_eq_bot;exact semiring.zero_of_zero_eq_one h _

lemma polynomial.leading_term_f_mul_X_pow {R} [nonzero_comm_ring R] (f : polynomial R)
  (n : ℕ) (hf : f ≠ 0) :
leading_coeff (f * X ^ n) ≠ 0 := 
begin
 rw leading_coeff_mul';
 {
   rw [leading_coeff_X_pow,mul_one],
   intro h,apply hf,
   rwa ←leading_coeff_eq_zero,
 }
end

lemma polynomial.degree_mul_X_pow {R} [comm_ring R] {f : polynomial R} (hf : f ≠ 0) (n : ℕ) :
degree (f * X ^ n) = degree f + n :=
begin
  by_cases h01 : (0 : R) = 1, simp [polynomial.zero_ring_degree h01 _],
  letI : nonzero_comm_ring R := comm_ring.non_zero_of_zero_ne_one (h01 : (0 : R) ≠ 1),
  rw degree_mul_eq',rw degree_X_pow,
  rw [leading_coeff_X_pow,mul_one],
  exact (iff_false_right hf).1 leading_coeff_eq_zero,
end

-- remark that g ≠ 0 is not necessary but I don't need the lemma in this case.
lemma polynomial.eq_degree_of_mul_X_pow {R} [comm_ring R] (f g : polynomial R)
  (h : nat_degree f ≤ nat_degree g) (hf : f ≠ 0) (hg : g ≠ 0):
degree (f * X ^ (nat_degree g - nat_degree f)) = degree g :=
begin
  by_cases h01 : (0 : R) = 1, simp [polynomial.zero_ring_degree h01 _],
  letI : nonzero_comm_ring R := comm_ring.non_zero_of_zero_ne_one (h01 : (0 : R) ≠ 1),
  rw polynomial.degree_mul_X_pow hf,
  rw [degree_eq_nat_degree hf,←with_bot.coe_add,degree_eq_nat_degree hg,with_bot.coe_eq_coe],
  exact nat.add_sub_cancel' h,
end

-- zero ring a special case so let's deal with it separately
theorem hilbert_basis_zero_ring {R} [comm_ring R] (h : (0 : R) = 1) :
is_noetherian_ring (polynomial R) :=
ring.is_noetherian_of_zero_eq_one (by simp [h]) -- I need a way of checking equality
-- amongst polynomials

theorem hilbert_basis {R} [comm_ring R] (hR : is_noetherian_ring R) : is_noetherian_ring (polynomial R) :=
begin
  -- deal with zero ring first
  by_cases h01 : (0 : R) = 1,
    
  let L : set R := set.range leading_coeff,
  have HL : is_ideal L := {
    zero_ := ⟨0,rfl⟩,
    add_ := λ a b ⟨f,Hf⟩ ⟨g,Hg⟩, begin
      by_cases h0 : a + b = 0, rw h0, exact ⟨0, rfl⟩,
      letI : nonzero_comm_ring R := nonzero_comm_ring.of_nonzero ⟨a+b,h0⟩,
      by_cases hf : f = 0, rw [←Hf, ←Hg, hf, leading_coeff_zero, zero_add], exact ⟨g,rfl⟩,
      by_cases hg : g = 0, rw [←Hf, ←Hg, hg, leading_coeff_zero, add_zero], exact ⟨f,rfl⟩,
      by_cases hd : nat_degree f ≤ nat_degree g,
      { let h := f * X ^ (nat_degree g - nat_degree f) + g,
        have Hf2 : leading_coeff (X ^ (nat_degree g - nat_degree f) : polynomial R) = 1,
          rw leading_coeff_X_pow,
        exact ⟨h, begin convert leading_coeff_add_of_degree_eq _ _,
                  rw leading_coeff_mul',
                    rw [Hf,Hf2,mul_one],
                  rw [Hf2,mul_one],
                  intro h,apply hf,rwa ←leading_coeff_eq_zero, 
                exact Hg.symm,
              rw degree_mul_eq',
              rw degree_X_pow,
              rw degree_eq_nat_degree hf,
              rw degree_eq_nat_degree hg,
              rw ←with_bot.coe_add,
              rw with_bot.coe_eq_coe,
              exact nat.add_sub_cancel' (le_of_lt hd),
            rw [leading_coeff_X_pow,mul_one],
            intro h,apply hf,rwa ←leading_coeff_eq_zero,
          rwa [Hg,leading_coeff_mul',leading_coeff_X_pow,mul_one,Hf],
          -- goal now again leading_coeff f * leading_coeff (X ^ (nat_degree g - nat_degree f)) ≠ 0
          rw [leading_coeff_X_pow,mul_one], -- I've now proved this three times.
          intro h,apply hf,rwa ←leading_coeff_eq_zero,
        end⟩,
      },
      -- other way now
    end,
    smul := sorry
  },
  sorry,
end

