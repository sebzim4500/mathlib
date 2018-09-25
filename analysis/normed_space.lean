/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Normed spaces.

Authors: Patrick Massot, Johannes Hölzl
-/

import algebra.pi_instances
import linear_algebra.basic
import analysis.nnreal
variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

noncomputable theory
open filter
local notation f `→_{`:50 a `}`:0 b := tendsto f (nhds a) (nhds b)

lemma squeeze_zero {α} {f g : α → ℝ} {t₀ : filter α} (hf : ∀t, 0 ≤ f t) (hft : ∀t, f t ≤ g t)
  (g0 : tendsto g t₀ (nhds 0)) : tendsto f t₀ (nhds 0) :=
begin
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) g0;
  simp [*]; exact filter.univ_mem_sets
end

class has_norm (α : Type*) := (norm : α → ℝ)

export has_norm (norm)

notation `∥`:1024 e:1 `∥`:1 := norm e

class normed_group (α : Type*) extends has_norm α, add_comm_group α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

section normed_group
variables [normed_group α] [normed_group β]

lemma dist_eq_norm (g h : α) : dist g h = ∥g - h∥ :=
normed_group.dist_eq _ _

@[simp] lemma dist_zero_right (g : α) : dist g 0 = ∥g∥ :=
by { rw[dist_eq_norm], simp }

lemma norm_triangle (g h : α) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
calc ∥g + h∥ = ∥g - (-h)∥             : by simp
         ... = dist g (-h)            : by simp[dist_eq_norm]
         ... ≤ dist g 0 + dist 0 (-h) : by apply dist_triangle
         ... = ∥g∥ + ∥h∥               : by simp[dist_eq_norm]

@[simp] lemma norm_nonneg (g : α) : 0 ≤ ∥g∥ :=
by { rw[←dist_zero_right], exact dist_nonneg }

lemma norm_eq_zero (g : α) : ∥g∥ = 0 ↔ g = 0 :=
by { rw[←dist_zero_right], exact dist_eq_zero }

@[simp] lemma norm_zero : ∥(0:α)∥ = 0 := (norm_eq_zero _).2 (by simp)

lemma norm_pos_iff (g : α) : ∥ g ∥ > 0 ↔ g ≠ 0 :=
begin
  split ; intro h ; rw[←dist_zero_right] at *,
  { exact dist_pos.1 h },
  { exact dist_pos.2 h }
end

lemma norm_le_zero_iff (g : α) : ∥g∥ ≤ 0 ↔ g = 0 :=
by { rw[←dist_zero_right], exact dist_le_zero }

@[simp] lemma norm_neg (g : α) : ∥-g∥ = ∥g∥ :=
calc ∥-g∥ = ∥0 - g∥ : by simp
      ... = dist 0 g : (dist_eq_norm 0 g).symm
      ... = dist g 0 : dist_comm _ _
      ... = ∥g - 0∥ : (dist_eq_norm g 0)
      ... = ∥g∥ : by simp

lemma abs_norm_sub_norm_le (g h : α) : abs(∥g∥ - ∥h∥) ≤ ∥g - h∥ :=
abs_le.2 $ and.intro
  (suffices -∥g - h∥ ≤ -(∥h∥ - ∥g∥), by simpa,
    neg_le_neg $ sub_right_le_of_le_add $
    calc ∥h∥ = ∥h - g + g∥ : by simp
      ... ≤ ∥h - g∥ + ∥g∥ : norm_triangle _ _
      ... = ∥-(g - h)∥ + ∥g∥ : by simp
      ... = ∥g - h∥ + ∥g∥ : by { rw [norm_neg (g-h)] })
  (sub_right_le_of_le_add $ calc ∥g∥ = ∥g - h + h∥ : by simp ... ≤ ∥g-h∥ + ∥h∥ : norm_triangle _ _)

lemma dist_norm_norm_le (g h : α) : dist ∥g∥ ∥h∥ ≤ ∥g - h∥ :=
abs_norm_sub_norm_le g h

section nnnorm

def nnnorm (a : α) : nnreal := ⟨norm a, norm_nonneg a⟩

@[simp] lemma coe_nnnorm (a : α) : (nnnorm a : ℝ) = norm a := rfl

lemma nndist_eq_nnnorm (a b : α) : nndist a b = nnnorm (a - b) := nnreal.eq $ dist_eq_norm _ _

lemma nnnorm_eq_zero (a : α) : nnnorm a = 0 ↔ a = 0 :=
by simp only [nnreal.eq_iff.symm, nnreal.coe_zero, coe_nnnorm, norm_eq_zero]

@[simp] lemma nnnorm_zero : nnnorm (0 : α) = 0 :=
nnreal.eq norm_zero

lemma nnnorm_triangle (g h : α) : nnnorm (g + h) ≤ nnnorm g + nnnorm h :=
by simpa [nnreal.coe_le] using norm_triangle g h

@[simp] lemma nnnorm_neg (g : α) : nnnorm (-g) = nnnorm g :=
nnreal.eq $ norm_neg g

lemma nndist_nnnorm_nnnorm_le (g h : α) : nndist (nnnorm g) (nnnorm h) ≤ nnnorm (g - h) :=
(nnreal.coe_le _ _).2 $ dist_norm_norm_le g h

end nnnorm

instance prod.normed_group [normed_group β] : normed_group (α × β) :=
{ norm := λx, max ∥x.1∥ ∥x.2∥,
  dist_eq := assume (x y : α × β),
    show max (dist x.1 y.1) (dist x.2 y.2) = (max ∥(x - y).1∥ ∥(x - y).2∥), by simp [dist_eq_norm] }

lemma norm_fst_le (x : α × β) : ∥x.1∥ ≤ ∥x∥ :=
begin have : ∥x∥ = max (∥x.fst∥) (∥x.snd∥) := rfl, rw this, simp[le_max_left] end

lemma norm_snd_le (x : α × β) : ∥x.2∥ ≤ ∥x∥ :=
begin have : ∥x∥ = max (∥x.fst∥) (∥x.snd∥) := rfl, rw this, simp[le_max_right] end

instance fintype.normed_group {π : α → Type*} [fintype α] [∀i, normed_group (π i)] :
  normed_group (Πb, π b) :=
{ norm := λf, ((finset.sup finset.univ (λ b, nnnorm (f b)) : nnreal) : ℝ),
  dist_eq := assume x y,
    congr_arg (coe : nnreal → ℝ) $ congr_arg (finset.sup finset.univ) $ funext $ assume a,
    show nndist (x a) (y a) = nnnorm (x a - y a), from nndist_eq_nnnorm _ _ }

lemma tendsto_iff_norm_tendsto_zero {f : ι → β} {a : filter ι} {b : β} :
  tendsto f a (nhds b) ↔ tendsto (λ e, ∥ f e - b ∥) a (nhds 0) :=
by rw tendsto_iff_dist_tendsto_zero ; simp only [(dist_eq_norm _ _).symm]

lemma lim_norm (x : α) : ((λ g, ∥g - x∥) : α → ℝ) →_{x} 0 :=
tendsto_iff_norm_tendsto_zero.1 (continuous_iff_tendsto.1 continuous_id x)

lemma lim_norm_zero : ((λ g, ∥g∥) : α → ℝ) →_{0} 0 :=
by simpa using lim_norm (0:α)

lemma continuous_norm : continuous ((λ g, ∥g∥) : α → ℝ) :=
begin
  rw continuous_iff_tendsto,
  intro x,
  rw tendsto_iff_dist_tendsto_zero,
  exact squeeze_zero (λ t, abs_nonneg _) (λ t, abs_norm_sub_norm_le _ _) (lim_norm x)
end

instance normed_top_monoid : topological_add_monoid α :=
⟨continuous_iff_tendsto.2 $ λ ⟨x₁, x₂⟩,
  tendsto_iff_norm_tendsto_zero.2
  begin
    refine squeeze_zero (by simp) _
      (by simpa using tendsto_add (lim_norm (x₁, x₂)) (lim_norm (x₁, x₂))),
    exact λ ⟨e₁, e₂⟩, calc
      ∥(e₁ + e₂) - (x₁ + x₂)∥ = ∥(e₁ - x₁) + (e₂ - x₂)∥ : by simp
      ... ≤ ∥e₁ - x₁∥ + ∥e₂ - x₂∥ : norm_triangle _ _
      ... ≤ max (∥e₁ - x₁∥) (∥e₂ - x₂∥) + max (∥e₁ - x₁∥) (∥e₂ - x₂∥) :
        add_le_add (le_max_left _ _) (le_max_right _ _)
  end⟩

instance normed_top_group : topological_add_group α :=
⟨continuous_iff_tendsto.2 $ λ x,
tendsto_iff_norm_tendsto_zero.2 begin
  have : ∀ (e : α), ∥-e - -x∥ = ∥e - x∥,
  { intro, simpa using norm_neg (e - x) },
  rw funext this, exact lim_norm x,
end⟩

end normed_group

section normed_ring

class normed_ring (α : Type*) extends has_norm α, ring α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

instance normed_ring.to_normed_group [β : normed_ring α] : normed_group α := { ..β }

lemma norm_mul {α : Type*} [normed_ring α] (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
normed_ring.norm_mul _ _

instance prod.normed_ring [normed_ring α] [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := assume x y,
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) : max_le_max (norm_mul (x.1) (y.1)) (norm_mul (x.2) (y.2))
        ... = (max (∥x.1∥*∥y.1∥) (∥y.2∥*∥x.2∥)) : by simp[mul_comm]
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.2∥) (∥y.1∥)) : by { apply max_mul_mul_le_max_mul_max; simp [norm_nonneg] }
        ... = (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by simp[max_comm]
        ... = (∥x∥*∥y∥) : rfl,
  ..prod.normed_group }
end normed_ring

section normed_field

class normed_field (α : Type*) extends has_norm α, discrete_field α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) = norm a * norm b)

instance normed_field.to_normed_ring [i : normed_field α] : normed_ring α :=
{ norm_mul := by finish [i.norm_mul], ..i }

instance : normed_field ℝ :=
{ norm := λ x, abs x,
  dist_eq := assume x y, rfl,
  norm_mul := abs_mul }

lemma real.norm_eq_abs (r : ℝ): norm r = abs r := rfl

end normed_field

section normed_space

class normed_space (α : out_param $ Type*) (β : Type*) [out_param $ normed_field α]
  extends has_norm β , vector_space α β, metric_space β :=
(dist_eq   : ∀ x y, dist x y = norm (x - y))
(norm_smul : ∀ a b, norm (a • b) = has_norm.norm a * norm b)

variables [normed_field α]

instance normed_space.to_normed_group [i : normed_space α β] : normed_group β :=
by refine { add := (+),
            dist_eq := normed_space.dist_eq,
            zero := 0,
            neg := λ x, -x,
            ..i, .. }; simp

instance normed_field.to_normed_space : normed_space α α :=
{ dist_eq := normed_field.dist_eq,
  norm_smul := normed_field.norm_mul }

lemma norm_smul [normed_space α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
normed_space.norm_smul _ _

lemma nnnorm_smul [normed_space α β] (s : α) (x : β) : nnnorm (s • x) = nnnorm s * nnnorm x :=
nnreal.eq $ norm_smul s x

variables {E : Type*} {F : Type*} [normed_space α E] [normed_space α F]

lemma tendsto_smul {f : γ → α} { g : γ → F} {e : filter γ} {s : α} {b : F} :
  (tendsto f e (nhds s)) → (tendsto g e (nhds b)) → tendsto (λ x, (f x) • (g x)) e (nhds (s • b)) :=
begin
  intros limf limg,
  rw tendsto_iff_norm_tendsto_zero,
  have ineq := λ x : γ, calc
      ∥f x • g x - s • b∥ = ∥(f x • g x - s • g x) + (s • g x - s • b)∥ : by simp[add_assoc]
                      ... ≤ ∥f x • g x - s • g x∥ + ∥s • g x - s • b∥ : norm_triangle (f x • g x - s • g x) (s • g x - s • b)
                      ... ≤ ∥f x - s∥*∥g x∥ + ∥s∥*∥g x - b∥ : by { rw [←smul_sub, ←sub_smul, norm_smul, norm_smul] },
  apply squeeze_zero,
  { intro t, exact norm_nonneg _ },
  { exact ineq },
  { clear ineq,

    have limf': tendsto (λ x, ∥f x - s∥) e (nhds 0) := tendsto_iff_norm_tendsto_zero.1 limf,
    have limg' : tendsto (λ x, ∥g x∥) e (nhds ∥b∥) := filter.tendsto.comp limg (continuous_iff_tendsto.1 continuous_norm _),

    have lim1 : tendsto (λ x, ∥f x - s∥ * ∥g x∥) e (nhds 0),
      by simpa using tendsto_mul limf' limg',
    have limg3 := tendsto_iff_norm_tendsto_zero.1 limg,
    have lim2 : tendsto (λ x, ∥s∥ * ∥g x - b∥) e (nhds 0),
      by simpa using tendsto_mul tendsto_const_nhds limg3,

    rw [show (0:ℝ) = 0 + 0, by simp],
    exact tendsto_add lim1 lim2  }
end

instance : normed_space α (E × F) :=
{ norm_smul :=
  begin
    intros s x,
    cases x with x₁ x₂,
    exact calc
      ∥s • (x₁, x₂)∥ = ∥ (s • x₁, s• x₂)∥ : rfl
      ... = max (∥s • x₁∥) (∥ s• x₂∥) : rfl
      ... = max (∥s∥ * ∥x₁∥) (∥s∥ * ∥x₂∥) : by simp [norm_smul s x₁, norm_smul s x₂]
      ... = ∥s∥ * max (∥x₁∥) (∥x₂∥) : by simp [mul_max_of_nonneg]
  end,

  add_smul := by simp[add_smul],
  -- I have no idea why by simp[smul_add] is not enough for the next goal
  smul_add := assume r x y,  show (r•(x+y).fst, r•(x+y).snd)  = (r•x.fst+r•y.fst, r•x.snd+r•y.snd),
               by simp[smul_add],
  ..prod.normed_group,
  ..prod.vector_space }

instance fintype.normed_space {ι : Type*} {E : ι → Type*} [fintype ι] [∀i, normed_space α (E i)] :
  normed_space α (Πi, E i) :=
{ norm := λf, ((finset.univ.sup (λb, nnnorm (f b)) : nnreal) : ℝ),
  dist_eq :=
    assume f g, congr_arg coe $ congr_arg (finset.sup finset.univ) $
    by funext i; exact nndist_eq_nnnorm _ _,
  norm_smul := λ a f,
    show (↑(finset.sup finset.univ (λ (b : ι), nnnorm (a • f b))) : ℝ) =
      nnnorm a * ↑(finset.sup finset.univ (λ (b : ι), nnnorm (f b))),
    by simp only [(nnreal.coe_mul _ _).symm, nnreal.mul_finset_sup, nnnorm_smul],
  ..metric_space_pi,
  ..pi.vector_space α }

end normed_space
