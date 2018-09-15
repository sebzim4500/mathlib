/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Linear algebra -- classical

This file is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define the following concepts:

* `lc α β`: linear combinations over `β` (`α` is the scalar ring)

* `span s`: the submodule generated by `s`

* `linear_independent s`: states that `s` are linear independent

* `linear_independent.repr s b`: choose the linear combination representing `b` on the linear
  independent vectors `s`. `b` should be in `span b` (uses classical choice)

* `is_basis s`: if `s` is a basis, i.e. linear independent and spans the entire space

* `is_basis.repr s b`: like `linear_independent.repr` but as a `linear_map`

* `is_basis.constr s g`: constructs a `linear_map` by extending `g` from the basis `s`

-/

import algebra algebra.big_operators order.zorn data.finset data.finsupp
noncomputable theory

open classical set function lattice
local attribute [instance] prop_decidable

reserve infix `≃ₗ` : 50

universes u v w x y
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type y} {ι : Type x}

@[simp] lemma set.diff_self {s : set α} : s \ s = ∅ :=
set.ext $ by simp

lemma zero_ne_one_or_forall_eq_0 (α : Type u) [ring α] : (0 : α) ≠ 1 ∨ (∀a:α, a = 0) :=
not_or_of_imp $ λ h a, by simpa using congr_arg ((*) a) h.symm

namespace finset

lemma smul_sum [ring γ] [module γ β] {s : finset α} {a : γ} {f : α → β} :
  a • (s.sum f) = s.sum (λc, a • f c) :=
(finset.sum_hom ((•) a) (@smul_zero γ β _ _ a) (assume _ _, smul_add)).symm

end finset

namespace finsupp

lemma smul_sum [has_zero β] [ring γ] [module γ δ] {v : α →₀ β} {c : γ} {h : α → β → δ} :
  c • (v.sum h) = v.sum (λa b, c • h a b) :=
finset.smul_sum

end finsupp

/-- The type of linear coefficients, which are simply the finitely supported functions
from the module `β` to the scalar ring `α`. -/
@[reducible] def lc (α : Type u) (β : Type v) [ring α] [module α β] : Type (max u v) := β →₀ α

namespace lc
variables [ring α] [module α β]

instance : has_scalar α (lc α β) := finsupp.to_has_scalar

instance : module α (lc α β) := finsupp.to_module α

lemma is_linear_map_sum [module α γ] [module α δ] {f : β → α → γ} {g : δ → lc α β}
  (hf : ∀b, is_linear_map (f b)) (hg : is_linear_map g) : is_linear_map (λd, (g d).sum f) :=
⟨assume d₁ d₂, by simp [hg.add, finsupp.sum_add_index, (hf _).zero, (hf _).add],
  assume a d,
    by simp [hg.smul, finsupp.sum_smul_index, (hf _).zero, finsupp.smul_sum, ((hf _).smul _ _).symm]⟩

end lc

namespace is_linear_map

@[simp] lemma finsupp_sum [ring α] [module α β] [module α γ] [has_zero δ]
  {f : β → γ} {t : ι →₀ δ} {g : ι → δ → β} (hf : is_linear_map f) :
  f (t.sum g) = t.sum (λi d, f (g i d)) :=
hf.sum

end is_linear_map

structure linear_equiv {α : Type u} [ring α] (β : Type v) (γ : Type w) [module α β] [module α γ]
  extends equiv β γ :=
(linear_fun : is_linear_map to_fun)

infix ` ≃ₗ ` := linear_equiv

namespace linear_equiv
variables [ring α] [module α β] [module α γ] [module α δ]
include α

lemma linear_inv (e : β ≃ₗ γ) : is_linear_map e.inv_fun :=
e.linear_fun.inverse e.left_inv e.right_inv

section
variable (β)
def refl : β ≃ₗ β := { linear_fun := is_linear_map.id, .. equiv.refl β }
end

def symm (e : β ≃ₗ γ) : γ ≃ₗ β := { linear_fun := e.linear_inv, .. e.to_equiv.symm }

def trans (e₁ : β ≃ₗ γ) (e₂ : γ ≃ₗ δ) : β ≃ₗ δ :=
{ linear_fun := is_linear_map.comp e₂.linear_fun e₁.linear_fun,
  .. e₁.to_equiv.trans e₂.to_equiv }


end linear_equiv

section module
variables [ring α] [module α β] [module α γ] [module α δ]
variables {a a' : α} {s t : set β} {b b' b₁ b₂ : β}
include α

/-- Linear span of a set of vectors -/
def span (s : set β) : set β := { x | ∃(v : lc α β), (∀x∉s, v x = 0) ∧ x = v.sum (λb a, a • b) }

instance is_submodule_span : is_submodule (span s) :=
{ zero_ := ⟨0,
    by simp [finsupp.sum_zero_index]⟩,
  add_  := assume x y ⟨vx, hx, eqx⟩ ⟨vy, hy, eqy⟩, ⟨vx + vy,
    by simp [hx, hy, eqx, eqy, finsupp.sum_add_index, add_smul] {contextual := tt}⟩,
  smul  := assume a b ⟨v, hv, veq⟩, ⟨a • v,
    by simp [hv, veq, finsupp.sum_smul_index, finsupp.smul_sum, smul_smul] {contextual := tt}⟩ }

lemma subset_span : s ⊆ span s :=
assume b (hb : b ∈ s),
have ∀b'∉s, b ≠ b', by intros b' hb' ne; cc,
⟨finsupp.single b 1, by simp [finsupp.sum_single_index, this] {contextual := tt}⟩

lemma span_eq_of_is_submodule (hs : is_submodule s) : span s = s :=
have span s ⊆ s,
  from assume b ⟨v, hv, eq⟩,
  have ∀c, v c • c ∈ s, from assume c, is_submodule.smul_ne_0 $ not_imp_comm.mp $ hv c,
  eq.symm ▸ is_submodule.sum (by simp [this] {contextual := tt}),
subset.antisymm this subset_span

lemma span_mono (h : t ⊆ s) : span t ⊆ span s :=
assume b ⟨v, hv, eq⟩, ⟨v, assume b, hv b ∘ mt (@h b), eq⟩

lemma span_minimal (hs : is_submodule s) (h : t ⊆ s) : span t ⊆ s :=
calc span t ⊆ span s : span_mono h
  ... = s : span_eq_of_is_submodule hs

lemma span_eq (hs : is_submodule s) (hts : t ⊆ s) (hst : s ⊆ span t) : span t = s :=
subset.antisymm (span_minimal hs hts) hst

@[simp] lemma span_empty : span (∅ : set β) = {0} :=
span_eq is_submodule.single_zero (empty_subset _) (by simp [subset_def, is_submodule.zero])

lemma is_submodule_range_smul : is_submodule $ range (λa, a • b) :=
is_submodule.range $ is_linear_map.map_smul_left is_linear_map.id

lemma span_singleton : span {b} = range (λa, a • b) :=
span_eq is_submodule_range_smul
  (assume b' hb', ⟨1, by simp * at *⟩)
  (assume b' ⟨a, eq⟩, eq ▸ is_submodule.smul _ $ subset_span $ mem_singleton _)

lemma span_union : span (s ∪ t) = {z | ∃x∈span s, ∃y∈span t, z = x + y } :=
span_eq is_submodule.add_submodule
  (union_subset
    (assume x hx, ⟨x, subset_span hx, 0, is_submodule.zero, by simp⟩)
    (assume y hy, ⟨0, is_submodule.zero, y, subset_span hy, by simp⟩))
  (assume b ⟨x, hx, y, hy, eq⟩, eq.symm ▸ is_submodule.add
    (span_mono (subset_union_left _ _) hx)
    (span_mono (subset_union_right _ _) hy))

lemma span_insert_eq_span (h : b ∈ span s) : span (insert b s) = span s :=
span_eq is_submodule_span (set.insert_subset.mpr ⟨h, subset_span⟩) (span_mono $ subset_insert _ _)

lemma span_insert : span (insert b s) = {z | ∃a, ∃x∈span s, z = a • b + x } :=
set.ext $ assume b',
begin
  split; rw [insert_eq, span_union]; simp [span_singleton, set.ext_iff, range, -add_comm],
  exact (assume y a eq_y x hx eq, ⟨a, x, hx, by simp [eq_y, eq]⟩),
  exact (assume a b₂ hb₂ eq, ⟨a • b, ⟨a, rfl⟩, b₂, hb₂, eq⟩)
end

lemma mem_span_insert : b₁ ∈ span (insert b s) ↔ ∃a, b₁ + a • b ∈ span s :=
begin
  simp [span_insert],
  constructor,
  exact assume ⟨a, b, hb, eq⟩, ⟨-a, by simp [eq, hb]⟩,
  exact assume ⟨a, hb⟩, ⟨-a, _, hb, by simp⟩
end

@[simp] lemma span_span : span (span s) = span s :=
span_eq_of_is_submodule is_submodule_span

@[simp] lemma span_image_of_linear_map {f : β → γ} (hf : is_linear_map f) :
  span (f '' s) = f '' span s :=
subset.antisymm
  (span_minimal (is_submodule.image hf) (image_subset _ subset_span))
  (image_subset_iff.mpr $
    span_minimal (is_submodule.preimage hf) (image_subset_iff.mp subset_span))

lemma linear_eq_on {f g : β → γ} (hf : is_linear_map f) (hg : is_linear_map g)
  (h : ∀x∈s, f x = g x) : ∀{x}, x ∈ span s → f x = g x
| _ ⟨l, hl, rfl⟩ :=
  begin
    simp [hf.finsupp_sum, hg.finsupp_sum],
    apply finset.sum_congr rfl,
    assume b hb,
    have : b ∈ s, { by_contradiction, simp * at * },
    simp [this, h, hf.smul, hg.smul]
  end

/-- Linearly independent set of vectors -/
def linear_independent (s : set β) : Prop :=
∀l : lc α β, (∀x∉s, l x = 0) → l.sum (λv c, c • v) = 0 → l = 0

lemma linear_independent_empty : linear_independent (∅ : set β) :=
assume l hl eq, finsupp.ext $ by simp * at *

lemma linear_independent.mono (hs : linear_independent s) (h : t ⊆ s) : linear_independent t :=
assume l hl eq, hs l (assume b, hl b ∘ mt (@h b)) eq

lemma zero_not_mem_of_linear_independent (ne : 0 ≠ (1:α)) (hs : linear_independent s) : (0:β) ∉ s :=
assume (h : 0 ∈ s),
let l : lc α β := finsupp.single 0 1 in
have l = 0,
  from hs l
    (by intro x; by_cases 0 = x; simp [l, finsupp.single_apply, *] at *)
    (by simp [finsupp.sum_single_index]),
have l 0 = 1, from finsupp.single_eq_same,
by rw [‹l = 0›] at this; simp * at *

lemma linear_independent_union {s t : set β}
  (hs : linear_independent s) (ht : linear_independent t) (hst : span s ∩ span t = {0}) :
  linear_independent (s ∪ t) :=
(zero_ne_one_or_forall_eq_0 α).elim
  (assume ne l hl eq0,
    let ls := l.filter $ λb, b ∈ s, lt := l.filter $ λb, b ∈ t in
    have hls : ↑ls.support ⊆ s, by simp [ls, subset_def],
    have hlt : ↑lt.support ⊆ t, by simp [ls, subset_def],
    have lt.sum (λb a, a • b) ∈ span t,
      from is_submodule.sum $ assume b hb, is_submodule.smul _ $ subset_span $ hlt hb,
    have l = ls + lt,
      from
      have ∀b, b ∈ s → b ∉ t,
        from assume b hbs hbt,
        have b ∈ span s ∩ span t, from ⟨subset_span hbs, subset_span hbt⟩,
        have b = 0, by rw [hst] at this; simp * at *,
        zero_not_mem_of_linear_independent ne hs $ this ▸ hbs,
      have lt = l.filter (λb, b ∉ s),
        from finsupp.ext $ assume b, by by_cases b ∈ t; by_cases b ∈ s; simp * at *,
      by rw [this]; exact finsupp.filter_pos_add_filter_neg.symm,
    have ls.sum (λb a, a • b) + lt.sum (λb a, a • b) = l.sum (λb a, a • b),
      by rw [this, finsupp.sum_add_index]; simp [add_smul],
    have ls_eq_neg_lt : ls.sum (λb a, a • b) = - lt.sum (λb a, a • b),
      from eq_of_sub_eq_zero $ by simp [this, eq0],
    have ls_sum_eq : ls.sum (λb a, a • b) = 0,
      from
      have - lt.sum (λb a, a • b) ∈ span t,
        from is_submodule.neg $ is_submodule.sum $
          assume b hb, is_submodule.smul _ $ subset_span $ hlt hb,
      have ls.sum (λb a, a • b) ∈ span s ∩ span t,
        from ⟨is_submodule.sum $ assume b hb, is_submodule.smul _ $ subset_span $ hls hb,
          ls_eq_neg_lt.symm ▸ this⟩,
      by rw [hst] at this; simp * at *,
    have ls = 0, from hs _ (finsupp.support_subset_iff.mp hls) ls_sum_eq,
    have lt_sum_eq : lt.sum (λb a, a • b) = 0,
      from eq_of_neg_eq_neg $ by rw [←ls_eq_neg_lt, ls_sum_eq]; simp,
    have lt = 0, from ht _ (finsupp.support_subset_iff.mp hlt) lt_sum_eq,
    by simp [‹l = ls + lt›, ‹ls = 0›, ‹lt = 0›])
  (assume eq_0 l _ _, finsupp.ext $ assume b, eq_0 _)

lemma linear_independent_Union_of_directed {s : set (set β)} (hs : ∀a∈s, ∀b∈s, ∃c∈s, a ∪ b ⊆ c)
  (h : ∀a∈s, linear_independent a) : linear_independent (⋃₀s) :=
assume l hl eq,
have ∀f:finset β, {x | x ∈ f} ⊆ ⋃₀ s → f = ∅ ∨ (∃t∈s, {x | x ∈ f} ⊆ t),
  from assume f, finset.induction_on f (by simp) $
    assume a f haf ih haf_s,
    let ⟨t, ht, hat⟩ := haf_s $ finset.mem_insert_self _ _ in
    have f = ∅ ∨ ∃ (t : set β) (H : t ∈ s), {x : β | x ∈ f} ⊆ t,
      from ih $ assume x hx, haf_s $ finset.mem_insert_of_mem hx,
    or.inr $ this.elim
      (assume : f = ∅, ⟨t, ht, by simp [this, hat, subset_def]⟩)
      (assume ⟨t', ht', hft⟩,
        let ⟨t'', ht''s, ht''⟩ := hs t ht t' ht' in
        have a ∈ t'',
          from ht'' $ or.inl hat,
        have ∀x, x ∈ f → x ∈ t'',
          from subset.trans (subset.trans hft $ subset_union_right _ _) ht'',
        ⟨t'', ht''s, by simp [subset_def, or_imp_distrib, *] {contextual := tt}⟩),
have l.support = ∅ ∨ (∃t∈s, {x | x ∈ l.support} ⊆ t),
  from this _ $ by intros x hx; by_contradiction; simp * at *,
this.elim
  (assume : l.support = ∅, by simp [finset.ext] at this; exact finsupp.ext this)
  (assume ⟨t, ht, hts⟩,
    have ∀x, l x ≠ 0 → x ∈ t, by simpa using hts,
    h t ht l (assume x, not_imp_comm.mp $ this x) eq)

lemma linear_independent_bUnion_of_directed {ι : Type w} {i : set ι} {s : ι → set β}
  (hs : ∀a∈i, ∀b∈i, ∃c∈i, s a ∪ s b ⊆ s c)
  (h : ∀a∈i, linear_independent (s a)) : linear_independent (⋃a∈i, s a) :=
have linear_independent (⋃₀ (s '' i)),
  from linear_independent_Union_of_directed
    (assume a ⟨j, hj, a_eq⟩ b ⟨l, hl, b_eq⟩, let ⟨k, hk, h⟩ := hs j hj l hl in
      ⟨s k, mem_image_of_mem _ hk, a_eq ▸ b_eq ▸ h⟩)
    (assume a ⟨j, hj, a_eq⟩, a_eq ▸ h j hj),
by rwa [sUnion_image] at this

lemma linear_independent.unique (hs : linear_independent s) {l₁ l₂ : lc α β}
  (h₁ : ∀x∉s, l₁ x = 0) (h₂ : ∀x∉s, l₂ x = 0) (eq : l₁.sum (λv c, c • v) = l₂.sum (λv c, c • v)) :
  l₁ = l₂ :=
eq_of_sub_eq_zero $ show l₁ - l₂ = 0,
  from hs (l₁ - l₂)
    (by simp [h₁, h₂] {contextual:=tt})
    (by simp [finsupp.sum_sub_index, eq, sub_smul, -sub_eq_add_neg, sub_self])

section repr
variables (hs : linear_independent s)

def linear_independent.repr (hs : linear_independent s) (b : β) : lc α β :=
if h : b ∈ span s then classical.some h else 0

lemma repr_not_span (h : b ∉ span s) : hs.repr b = 0 := dif_neg h

lemma repr_spec (h : b ∈ span s) : (∀b'∉s, hs.repr b b' = 0) ∧ b = (hs.repr b).sum (λb a, a • b) :=
have hs.repr b = classical.some h, from dif_pos h,
by rw [this]; exact classical.some_spec h

lemma repr_eq_zero (hb' : b' ∉ s) : hs.repr b b' = 0 :=
by_cases
  (assume : b ∈ span s, (repr_spec hs this).left _ hb')
  (assume : b ∉ span s, by rw [repr_not_span hs this]; refl)

lemma repr_sum_eq (hb : b ∈ span s) : (hs.repr b).sum (λb a, a • b) = b :=
(repr_spec hs hb).right.symm

lemma repr_eq {l : lc α β} (hb : b ∈ span s) (h : ∀x∉s, l x = 0) (eq : l.sum (λv c, c • v) = b) :
  hs.repr b = l :=
hs.unique (assume b, repr_eq_zero hs) h (by rw [repr_sum_eq hs hb, eq])

lemma repr_eq_single (hb : b ∈ s) : hs.repr b = finsupp.single b 1 :=
repr_eq hs (subset_span hb)
  (assume b' hb', finsupp.single_eq_of_ne $ show b ≠ b', from assume eq, by simp * at *)
  (by simp [finsupp.sum_single_index, add_smul])

@[simp] lemma repr_zero : hs.repr 0 = 0 :=
repr_eq hs is_submodule.zero (by simp) (by simp [finsupp.sum_zero_index])

lemma repr_support : ↑(hs.repr b).support ⊆ s :=
assume x hx, classical.by_contradiction $ assume hxs,
  by simp at hx; exact hx (repr_eq_zero hs hxs)

@[simp] lemma repr_add (hb : b ∈ span s) (hb' : b' ∈ span s) :
  hs.repr (b + b') = hs.repr b + hs.repr b' :=
repr_eq hs (is_submodule.add hb hb')
  (by simp [repr_eq_zero] {contextual := tt})
  (by simp [finsupp.sum_add_index, add_smul, repr_sum_eq hs, hb, hb'])

@[simp] lemma repr_smul (hb : b ∈ span s) : hs.repr (a • b) = a • hs.repr b :=
repr_eq hs (is_submodule.smul _ hb)
  (by simp [repr_eq_zero] {contextual := tt})
  (calc (a • hs.repr b).sum (λb a, a • b) = (hs.repr b).sum (λb a', a • (a' • b)) :
      by simp [finsupp.sum_smul_index, add_smul, smul_smul]
    ... = a • (hs.repr b).sum (λb a', a' • b) : finsupp.smul_sum.symm
    ... = a • b : by rw [repr_sum_eq hs hb])

@[simp] lemma repr_neg : hs.repr (- b) = - hs.repr b :=
by_cases
  (assume hb : b ∈ span s,
    have hs.repr ((-1) • b) = (-1) • hs.repr b, from repr_smul hs hb,
    by simpa)
  (assume hb : b ∉ span s,
    have -b ∉ span s, from assume hb, have - - b ∈ span s, from is_submodule.neg hb, by simpa,
    by simp [repr_not_span, this, hb])

@[simp] lemma repr_sub (hb : b ∈ span s) (hb' : b' ∈ span s) :
  hs.repr (b - b') = hs.repr b - hs.repr b' :=
by simp [repr_add hs hb, repr_neg hs, is_submodule.neg hb']

@[simp] lemma repr_sum {ι : Type w} {f : finset ι} {b : ι → β} :
  (∀i∈f, b i ∈ span s) → hs.repr (f.sum b) = f.sum (λi, hs.repr (b i)) :=
by apply f.induction_on;
   simp [or_imp_distrib, forall_and_distrib, repr_add hs, is_submodule.sum] {contextual := tt}

@[simp] lemma repr_finsupp_sum {ι : Type w} {δ : Type x} [has_zero δ] {f : ι →₀ δ} {b : ι → δ → β} :
  (∀i∈f.support, b i (f i) ∈ span s) → hs.repr (f.sum b) = f.sum (λi d, hs.repr (b i d)) :=
repr_sum hs

lemma repr_eq_repr_of_subset {ht : linear_independent t} (h : t ⊆ s) (hb : b ∈ span t) :
  ht.repr b = hs.repr b :=
eq.symm $ repr_eq hs (span_mono h hb)
  (assume x hx, repr_eq_zero _ $ assume hxt, hx $ h hxt)
  (repr_sum_eq ht hb)

end repr

section
variables {f : β → γ} {l : lc α β}
  (hs : linear_independent (f '' s)) (hf : is_linear_map f)
  (hf_inj : ∀a∈s, ∀b∈s, f a = f b → a = b) (hl : ∀x∉s, l x = 0)
include hs hf hf_inj

private lemma l_eq_0 (h : f (l.sum (λb a, a • b)) = 0) : l = 0 :=
have l_imp_s : ∀{x}, l x ≠ 0 → x ∈ s,
  from assume x hx, classical.by_contradiction $ assume hnx, hx $ hl _ $ hnx,
have ∀c, c ∉ f '' s → c ∉ (l.map_domain f).support,
  from assume c, mt $ assume hb,
  have c ∈ l.support.image f, from finsupp.map_domain_support hb,
  have ∃b, l b ≠ 0 ∧ f b = c, by simpa,
  let ⟨b, hb, c_eq⟩ := this in
  ⟨b, l_imp_s hb, c_eq⟩,
have l.map_domain f = 0,
  from hs _ (by simpa) $
    calc (l.map_domain f).sum (λb a, a • b) = f (l.sum (λb a, a • b)):
        by simp [finsupp.sum_map_domain_index, add_smul, hf.finsupp_sum, hf.smul]
      ... = 0 : h,
calc l = l.map_domain id :
    by rw [finsupp.map_domain_id]
   ... = l.map_domain (@inv_fun_on _ ⟨0⟩ _ f s ∘ f) :
    finsupp.map_domain_congr $
      assume b hb, (@inv_fun_on_eq' _ ⟨0⟩ _ _ _ _ hf_inj $ l_imp_s $ by simpa using hb).symm
  ... = 0 :
    by rw [finsupp.map_domain_comp, this, finsupp.map_domain_zero]

lemma linear_independent.of_image : linear_independent s :=
assume l hl eq, l_eq_0 hs hf hf_inj hl $ by simp [eq, hf.zero]

lemma linear_independent.eq_0_of_span : ∀a∈span s, f a = 0 → a = 0
| _ ⟨l, hl, rfl⟩ eq_0 := by simp [l_eq_0 hs hf hf_inj hl eq_0, finsupp.sum_zero_index]

end

/-- A set of vectors is a basis if it is linearly independent and all vectors are in the span -/
def is_basis (s : set β) := linear_independent s ∧ (∀x, x ∈ span s)

section is_basis

lemma is_basis.map_repr (hs : is_basis s) : is_linear_map hs.1.repr :=
⟨assume b₁ b₂, repr_add hs.1 (hs.2 _) (hs.2 _), assume a b, repr_smul hs.1 (hs.2 _)⟩

def is_basis.constr (hs : is_basis s) (f : β → γ) (b : β) : γ := (hs.1.repr b).sum (λb a, a • f b)

lemma is_basis.map_constr (hs : is_basis s) {f : β → γ} : is_linear_map (hs.constr f) :=
lc.is_linear_map_sum (assume b, is_linear_map.map_smul_left is_linear_map.id) hs.map_repr

lemma is_basis.eq_linear_map {f g : β → γ} (hf : is_linear_map f) (hg : is_linear_map g)
  (hs : is_basis s) (h : ∀b∈s, f b = g b) : f = g :=
funext $ assume b, linear_eq_on hf hg h (hs.2 b)

lemma constr_congr {f g : β → γ} {b : β} (hs : is_basis s) (h : ∀b∈s, f b = g b) :
  hs.constr f = hs.constr g :=
funext $ assume b', finset.sum_congr rfl $ assume b hb,
  have b ∈ s, from repr_support hs.1 hb,
  by simp [h b this]

lemma constr_basis {f : β → γ} {b : β} (hs : is_basis s) (hb : b ∈ s) :
  (hs.constr f : β → γ) b = f b :=
show (hs.1.repr b).sum (λb a, a • f b) = f b,
  by simp [hs.1, hs.2, hb, repr_eq_single, finsupp.sum_single_index]

lemma constr_eq {g : β → γ} {f : β → γ} (hs : is_basis s)
  (hf : is_linear_map f) (h : ∀x∈s, g x = f x) : hs.constr g = f :=
hs.eq_linear_map hs.map_constr hf $ assume b hb, h b hb ▸ constr_basis hs hb

lemma constr_zero (hs : is_basis s) : hs.constr (λb, (0 : γ)) = (λb, 0) :=
constr_eq hs is_linear_map.map_zero $ by simp

lemma constr_add {g f : β → γ} (hs : is_basis s) :
  hs.constr (λb, f b + g b) = (λb, hs.constr f b + hs.constr g b) :=
constr_eq hs (is_linear_map.map_add hs.map_constr hs.map_constr) $
  by simp [constr_basis hs] {contextual := tt}

lemma constr_sub {g f : β → γ} (hs : is_basis s) :
  hs.constr (λb, f b - g b) = (λb, hs.constr f b - hs.constr g b) :=
constr_eq hs (is_linear_map.map_sub hs.map_constr hs.map_constr) $
  by simp [constr_basis hs] {contextual := tt}

lemma constr_neg {f : β → γ} (hs : is_basis s) : hs.constr (λb, - f b) = (λb, - hs.constr f b) :=
constr_eq hs hs.map_constr.map_neg $ by simp [constr_basis hs] {contextual := tt}

-- this only works on functions if `α` is a commutative ring
lemma constr_smul {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [module α β] [module α γ]
  {f : β → γ} {a : α} {s : set β} (hs : is_basis s) {b : β} :
  hs.constr (λb, a • f b) = (λb, a • (hs.constr f) b) :=
constr_eq hs hs.map_constr.map_smul_right $ by simp [constr_basis hs] {contextual := tt}

lemma constr_mem_span (hs : is_basis s) {f : β → γ} : (hs.constr f : β → γ) b ∈ span (f '' s) :=
is_submodule.sum $ assume b' hb',
  have b' ∈ s, from repr_support hs.1 hb',
  is_submodule.smul _ $ subset_span $ mem_image_of_mem _ this

lemma constr_im_eq_span (hs : is_basis s) {f : β → γ} : range (hs.constr f) = span (f '' s) :=
eq.symm $ span_eq (is_submodule.range hs.map_constr)
  (assume b' ⟨b, hb, eq⟩, ⟨b, eq ▸ constr_basis hs hb⟩)
  (assume b' ⟨b, hb⟩, hb ▸ constr_mem_span hs)

def module_equiv_lc (hs : is_basis s) : β ≃ (s →₀ α) :=
{ to_fun    := assume b, (hs.1.repr b).subtype_domain _,
  inv_fun   := assume v, v.sum $ λb a, a • b.1,
  left_inv  := assume b,
    calc ((hs.1.repr b).subtype_domain s).sum (λb a, a • b.1) = (hs.1.repr b).sum (λb a, a • b) :
      @finsupp.sum_subtype_domain_index β _ _ _ _ (λx, x ∈ s) _ _ _ _ (λb a, a • b) (repr_support hs.1)
      ... = _ : repr_sum_eq _ $ hs.2 _,
  right_inv := assume v, finsupp.ext $ assume ⟨b, hb⟩,
    have v.sum (λb' a, hs.1.repr (a • b'.val) b) = v ⟨b, hb⟩,
      from calc v.sum (λb' a, hs.1.repr (a • b'.val) b) =
          v.sum (λb' a, a * (finsupp.single b'.val 1 : lc α β) b) :
            finset.sum_congr rfl $ assume ⟨b', hb'⟩ h',
              by dsimp; rw [repr_smul hs.1 (hs.2 _), repr_eq_single _ hb']; refl
        ... = ({⟨b, hb⟩} : finset s).sum (λb', v b' * (finsupp.single b'.val 1 : lc α β) b) :
          finset.sum_bij_ne_zero (λx hx x0, x)
            (assume ⟨x, hx⟩, by by_cases x = b; simp [*]) (by simp)
            (assume ⟨x, hx⟩, by simp; intro e; subst x;
               exact assume h, ⟨b, hb, assume h', by simp * at *, h, rfl⟩)
            (by simp)
        ... = v ⟨b, hb⟩ : by simp,
    begin
      dsimp,
      rw [repr_finsupp_sum, finsupp.sum_apply],
      { exact this },
      { simp [hs.2] }
    end }

def equiv_of_is_basis {s : set β} {t : set γ} {f : β → γ} {g : γ → β}
  (hs : is_basis s) (ht : is_basis t) (hf : ∀b∈s, f b ∈ t) (hg : ∀c∈t, g c ∈ s)
  (hgf : ∀b∈s, g (f b) = b) (hfg : ∀c∈t, f (g c) = c) :
  β ≃ₗ γ :=
{ to_fun := hs.constr f,
  inv_fun := ht.constr g,
  left_inv := assume b,
    congr_fun (hs.eq_linear_map (ht.map_constr.comp hs.map_constr) is_linear_map.id $
      by simp [constr_basis, hs, ht, hf, hgf, (∘)] {contextual := tt}) b,
  right_inv := assume c,
    congr_fun (ht.eq_linear_map (hs.map_constr.comp ht.map_constr) is_linear_map.id $
      by simp [constr_basis, hs, ht, hg, hfg, (∘)] {contextual := tt}) c,
  linear_fun := hs.map_constr }

end is_basis

lemma linear_independent.inj_span_iff_inj {s : set β} {f : β → γ}
  (hf : is_linear_map f) (hfs : linear_independent (f '' s)) :
  (∀a∈span s, ∀b∈span s, f a = f b → a = b) ↔ (∀a∈s, ∀b∈s, f a = f b → a = b) :=
iff.intro
  (assume h a ha b hb eq, h a (subset_span ha) b (subset_span hb) eq)
  (assume h a ha b hb eq, eq_of_sub_eq_zero $ hfs.eq_0_of_span hf h _ (is_submodule.sub ha hb)
    (by simp [eq, hf.add, hf.neg]))

-- TODO: clean up proof / alternative proof
lemma linear_independent.image {s : set β} {f : β → γ}
  (hf : is_linear_map f) (hs : linear_independent s)
  (hf_inj : ∀a∈span s, ∀b∈span s, f a = f b → a = b) :
  linear_independent (f '' s) :=
let g := @inv_fun_on _ ⟨0⟩ _ f (span s) in
have hg : ∀x∈span s, g (f x) = x,
  from assume x, @inv_fun_on_eq' _ ⟨0⟩ _ _ _ _ hf_inj,
assume l hl eq,
have l_g : ∀b∈(l.map_domain g).support, b ∈ s, from
  assume b hb,
  have b ∈ l.support.image g, from finsupp.map_domain_support hb,
  have ∃c, l c ≠ 0 ∧ g c = b, by simpa,
  let ⟨c, hc, b_eq⟩ := this in
  have c ∈ f '' s, by by_contradiction h; simp * at *,
  let ⟨b', hb', c_eq⟩ := this in
  have b' = b, from b_eq ▸ c_eq ▸ (hg _ $ subset_span hb').symm,
  this ▸ hb',
have l_f_g : l.map_domain (f ∘ g) = l.map_domain id, from
  finsupp.map_domain_congr $ assume c hc,
    have c ∈ f '' s, by by_contradiction h; simp * at *,
    let ⟨b, hb, c_eq⟩ := this in
    by simp [c_eq.symm, (∘), hg, subset_span hb],
have l.map_domain g = 0, from
  have l_g_s : (l.map_domain g).sum (λb a, a • b) ∈ span s,
    from is_submodule.sum $ assume b hb, is_submodule.smul _ $ subset_span $ l_g b hb,
  have f_sum : f ((l.map_domain g).sum (λb a, a • b)) = 0,
    from calc f ((l.map_domain g).sum (λb a, a • b)) =
          ((l.map_domain g).map_domain f).sum (λb a, a • b) :
        by simp [finsupp.sum_map_domain_index, add_smul, hf.finsupp_sum, hf.smul]
      ... = 0 :
        by rw [←finsupp.map_domain_comp, l_f_g, finsupp.map_domain_id, eq],
  have ∀b∉s, (l.map_domain g) b = 0,
    from assume b hb, classical.by_contradiction $ assume hnb, hb $ l_g b $ by simp *,
  hs _ this $ hf_inj _ l_g_s _ is_submodule.zero (by simpa [hf.zero] using f_sum),
calc l = (l.map_domain g).map_domain f :
    by rw [←finsupp.map_domain_comp, l_f_g, finsupp.map_domain_id]
  ... = 0 :
    by rw [this, finsupp.map_domain_zero]

lemma linear_map.linear_independent_image_iff {s : set β} {f : β → γ}
  (hf : is_linear_map f) (hf_inj : ∀a∈span s, ∀b∈span s, f a = f b → a = b) :
  linear_independent (f '' s) ↔ linear_independent s :=
iff.intro
  (assume h, h.of_image hf $ assume x hx y hy, hf_inj x (subset_span hx) y (subset_span hy))
  (assume h, h.image hf hf_inj)

end module

section vector_space
variables [field α] [vector_space α β] [vector_space α γ] {s t : set β} {b b₁ b₂ : β}
include α

local attribute [instance] is_submodule_span

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type classs) -/

lemma mem_span_insert_exchange : b₁ ∈ span (insert b₂ s) → b₁ ∉ span s → b₂ ∈ span (insert b₁ s) :=
begin
  simp [span_insert],
  exact assume a b₃ hb₃ b₁_eq hb₁,
    have a ≠ 0, from assume a0, by simp * at *,
    ⟨1/a, (- 1/a) • b₃, is_submodule.smul _ hb₃,
      by simp [b₁_eq, smul_add, smul_smul, mul_inv_cancel, this, neg_div]⟩
end

lemma linear_independent_iff_not_mem_span : linear_independent s ↔ (∀b∈s, b ∉ span (s \ {b})) :=
iff.intro
  (assume (hs : linear_independent s) b hb ⟨l, hl, b_eq⟩,
    let l' := l - finsupp.single b 1 in
    have ∀b', b' ∉ s → l' b' = 0,
      from assume b' hb',
      have ne: b ≠ b', from assume h, hb' $ h ▸ hb,
      have b' ∉ s \ {b}, from assume ⟨h₁, h₂⟩, hb' h₁,
      by simp [ne, hl b' this],
    have l' = 0, from hs l' this $
      by simp [l', finsupp.sum_add_index, finsupp.sum_neg_index, add_smul, b_eq.symm, finsupp.sum_single_index],
    have - l' b = 1, from have b ∉ s \ {b}, by simp, by simp [hl _ this],
    by rw [‹l' = 0›] at this; simp at this; assumption)
  (assume hs l hl eq, finsupp.ext $ assume b, classical.by_contradiction $ assume h : l b ≠ 0,
    let a := -1 / l b in
    hs b
      (show b ∈ s, from classical.by_contradiction $ assume hnb, h $ hl b hnb)
      ⟨a • l + finsupp.single b 1,
        assume b', by_cases
          (assume : b' = b, by simp [this, h, neg_div, a])
          (assume : b' ≠ b, by simp [finsupp.sub_apply, hl, this, this.symm] {contextual:=tt}),
        have l.sum (λb a', (a * a') • b) = a • l.sum (λb a, a • b),
          by simp [finsupp.smul_sum, smul_smul],
        by simp [-sub_eq_add_neg, add_smul, finsupp.sum_add_index, finsupp.sum_single_index,
                finsupp.sum_smul_index, this, eq]⟩)

lemma linear_independent_singleton {b : β} (hb : b ≠ 0) : linear_independent ({b} : set β) :=
linear_independent_iff_not_mem_span.mpr $ by simp [hb] {contextual := tt}

lemma linear_independent.insert (hs : linear_independent s) (hb : b ∉ span s) :
  linear_independent (insert b s) :=
assume l hl eq, by_cases
  (assume : l b = 0,
    hs l (assume x hx,
      by_cases (assume h : x = b, h.symm ▸ this) (assume h', hl _ $ by simp [not_or_distrib, hx, h']))
      eq)
  (assume lb_ne_zero : l b ≠ 0,
    have (1 / l b) • (- (- l b • b)) ∈ span s,
      from is_submodule.smul _ $ is_submodule.neg ⟨l - finsupp.single b (l b),
        assume x hx, by_cases
          (assume : b = x, by simp [this.symm])
          (assume ne : b ≠ x,
            have x ∉ insert b s, by simp [not_or_distrib, hx, ne.symm],
            by simp [hl x this, ne] {contextual := tt}),
        by simp [finsupp.sum_sub_index, finsupp.sum_single_index, -sub_eq_add_neg, sub_smul, eq]; simp⟩,
    have (1 / l b) • (- (- l b • b)) = b,
      by simp [smul_smul, mul_comm, mul_inv_cancel lb_ne_zero],
    by simp * at *)

lemma exists_linear_independent (hs : linear_independent s) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span b ∧ linear_independent b :=
let C := { b : set β // s ⊆ b ∧ b ⊆ t ∧ linear_independent b }, s' : C := ⟨s, le_refl s, hst, hs⟩ in
have ∀c, zorn.chain (λa b:C, a.val ⊆ b.val) c → c ≠ ∅ → ∃(m : C), ∀a:C, a ∈ c → a.val ⊆ m.val, from
  assume c hc ne,
  let ⟨a, ha⟩ := exists_mem_of_ne_empty ne in
  ⟨⟨(⋃a ∈ c, (a : C).val),
    subset.trans a.property.1 $ subset_bUnion_of_mem ha,
    bUnion_subset $ assume c hc, c.property.right.left,
    linear_independent_bUnion_of_directed
      (assume a ha b hb, by_cases
        (assume h : a = b, ⟨a, ha, h ▸ le_of_eq (@sup_idem (set _) _ a.val)⟩)
        (assume h : a ≠ b, (hc a ha b hb h).elim
          (assume h, ⟨b, hb, union_subset h (subset.refl _)⟩)
          (assume h, ⟨a, ha, union_subset (subset.refl _) h⟩)))
      (assume a ha, a.property.2.2)⟩,
    assume a ha, subset_bUnion_of_mem ha⟩,
have ∃m:C, ∀a:C, m.val ⊆ a.val → a.val ⊆ m.val, from
  zorn.zorn
    (assume c hc, by_cases (assume : c = ∅, ⟨s', assume a, this.symm ▸ false.elim⟩) (this c hc))
    (assume a b c, subset.trans),
let ⟨⟨m, hsm, hmt, hml⟩, hm⟩ := this in
have t ⊆ span m,
  from classical.by_contradiction $ assume : ¬ t ⊆ span m,
  let ⟨b, hb⟩ := classical.not_forall.mp this, ⟨hbt, hbm⟩ := not_imp.mp hb in
  have insert b m ⊆ m,
    from hm
      ⟨_, subset.trans hsm $ subset_insert _ _, by simp [set.insert_subset, hmt, hbt], hml.insert hbm⟩
      (subset_insert _ _),
  have b ∈ span m, from subset_span $ this $ mem_insert _ _,
  hbm this,
⟨m, hmt, hsm, this, hml⟩

lemma exists_subset_is_basis (hs : linear_independent s) : ∃b, s ⊆ b ∧ is_basis b :=
let ⟨b, hb₀, hb₁, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨b, hb₁, hb₃, assume x, hb₂ trivial⟩

variable (β)
lemma exists_is_basis : ∃b : set β, is_basis b :=
let ⟨b, _, hb⟩ := exists_subset_is_basis linear_independent_empty in ⟨b, hb⟩
variable {β}

lemma eq_of_linear_independent_of_span
  (hs : linear_independent s) (h : t ⊆ s) (hst : s ⊆ span t) : s = t :=
suffices s ⊆ t, from subset.antisymm this h,
assume b hb,
have (hs.mono h).repr b = finsupp.single b 1,
  from calc (hs.mono h).repr b = hs.repr b : repr_eq_repr_of_subset hs h $ hst hb
    ... = finsupp.single b 1 : repr_eq_single hs hb,
have b ∈ (↑((hs.mono h).repr b).support : set β), by simp [this],
repr_support _ this

lemma exists_of_linear_independent_of_finite_span {t : finset β}
  (hs : linear_independent s) (hst : s ⊆ span ↑t) :
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset β), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ span ↑(s' ∪ t) →
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s', from eq_of_linear_independent_of_span hs hs' $ by simpa using hss',
    ⟨s', by simp [this]⟩)
  (assume b₁ t hb₁t ih s' hs' hst hss',
    have hb₁s : b₁ ∉ s,
      from assume h,
      have b₁ ∈ s ∩ ↑(insert b₁ t), from ⟨h, finset.mem_insert_self _ _⟩,
      by rwa [hst] at this,
    have hb₁s' : b₁ ∉ s', from assume h, hb₁s $ hs' h,
    have hst : s ∩ ↑t = ∅,
      from eq_empty_of_subset_empty $ subset.trans
        (by simp [inter_subset_inter, subset.refl]) (le_of_eq hst),
    by_cases
      (assume : s ⊆ span ↑(s' ∪ t),
        let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
        have hb₁u : b₁ ∉ u, from assume h, (hust h).elim hb₁s hb₁t,
        ⟨insert b₁ u, by simp [set.insert_subset_insert hust],
          subset.trans hsu (by simp), by simp [eq, hb₁t, hb₁s', hb₁u]⟩)
      (assume : ¬ s ⊆ span ↑(s' ∪ t),
        let ⟨b₂, hb₂s, hb₂t⟩ := set.not_subset.mp this in
        have hb₂t' : b₂ ∉ s' ∪ t, from assume h, hb₂t $ subset_span h,
        have s ⊆ span ↑(insert b₂ s' ∪ t), from
          assume b₃ hb₃,
          have ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : set β),
            by simp [insert_eq, -singleton_union, -union_singleton, union_subset_union, subset.refl, subset_union_right],
          have hb₃ : b₃ ∈ span (insert b₁ (insert b₂ ↑(s' ∪ t) : set β)),
            from span_mono this (hss' hb₃),
          have s ⊆ span (insert b₁ ↑(s' ∪ t)),
            by simpa [insert_eq, -singleton_union, -union_singleton] using hss',
          have hb₁ : b₁ ∈ span (insert b₂ ↑(s' ∪ t)),
            from mem_span_insert_exchange (this hb₂s) hb₂t,
          by rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃,
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [set.insert_subset, hb₂s, hs']) hst this in
        ⟨u, subset.trans hust $ union_subset_union (subset.refl _) (by simp [subset_insert]),
          hsu, by rw [finset.union_comm] at hb₂t'; simp [eq, hb₂t', hb₁t, hb₁s']⟩)),
have eq : t.filter (λx, x ∈ s) ∪ t.filter (λx, x ∉ s) = t,
  from finset.ext.mpr $ assume x, by by_cases x ∈ s; simp *,
let ⟨u, h₁, h₂, h⟩ := this (t.filter (λx, x ∉ s)) (t.filter (λx, x ∈ s))
  (by simp [set.subset_def]) (by simp [set.ext_iff] {contextual := tt}) (by rwa [eq]) in
⟨u, subset.trans h₁ (by simp [subset_def, and_imp, or_imp_distrib] {contextual:=tt}),
  h₂, by rwa [eq] at h⟩

lemma exists_finite_card_le_of_finite_of_linear_independent_of_span
  (ht : finite t) (hs : linear_independent s) (hst : s ⊆ span t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ span ↑(ht.to_finset), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_linear_independent_of_finite_span hs this in
have finite s, from finite_subset u.finite_to_set hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

lemma exists_left_inverse_linear_map_of_injective {f : β → γ}
  (hf : is_linear_map f) (hf_inj : injective f) : ∃g:γ → β, is_linear_map g ∧ g ∘ f = id :=
let ⟨bβ, hbβ⟩ := exists_is_basis β in
have linear_independent (f '' bβ),
  from hbβ.1.image hf $ assume b₁ _ b₂ _ eq, hf_inj eq,
let ⟨bγ, hbγ₁, hbγ₂⟩ := exists_subset_is_basis this in
have ∀b∈bβ, (hbγ₂.constr (@inv_fun _ ⟨0⟩ _ f) : γ → β) (f b) = b,
  begin
    assume b hb,
    rw [constr_basis],
    { exact @inv_fun_on_eq' β ⟨0⟩ γ f univ b (assume b₁ _ b₂ _ eq, hf_inj eq) trivial },
    { exact hbγ₁ (mem_image_of_mem _ hb) }
  end,
⟨hbγ₂.constr $ @inv_fun _ ⟨0⟩ _ f, hbγ₂.map_constr,
  hbβ.eq_linear_map (hbγ₂.map_constr.comp hf) is_linear_map.id this⟩

lemma exists_right_inverse_linear_map_of_surjective {f : β → γ}
  (hf : is_linear_map f) (hf_surj : surjective f) :
  ∃g:γ → β, is_linear_map g ∧ f ∘ g = id :=
let g := @inv_fun _ ⟨0⟩ _ f in
have ri_gf : right_inverse g f, from @right_inverse_inv_fun _ ⟨0⟩ _ _ hf_surj,
have injective g, from injective_of_left_inverse ri_gf,
let ⟨bγ, hbγ⟩ := exists_is_basis γ in
have ∀c∈bγ, f ((hbγ.constr g : γ → β) c) = c,
  from assume c hc, by rw [constr_basis hbγ hc, ri_gf],
⟨hbγ.constr g, hbγ.map_constr, hbγ.eq_linear_map (hf.comp hbγ.map_constr) is_linear_map.id this⟩

end vector_space
