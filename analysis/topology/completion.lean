/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Hausdorff completions of uniform spaces.

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `to_completion : α → completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`completion.map f : completion α → β` such that `f = completion_extension f ∘ to_completion α`.
Actually `completion_extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `to_completion α` is not injective if `α` is not Hausdorff. But its image is always
dense.

The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, if turns `f : α → β` into
a morphism `completion.map f : completion α → completion β` such that
`(to_completion β) ∘ f = (completion.map f) ∘ to_completion α` provided `f` is uniformly continuous.
This construction is compatible with composition.

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in analysis.topology.uniform_space.
-/
import analysis.topology.uniform_space
import analysis.topology.continuity
import data.set.basic data.set.function

open filter set
local attribute [instance] classical.prop_decidable
universes u v w

/- separation space -/
namespace uniform_space
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]

def separation_setoid (α : Type u) [uniform_space α] : setoid α :=
⟨λx y, (x, y) ∈ separation_rel α, separated_equiv⟩

local attribute [instance] separation_setoid

instance {α : Type u} [u : uniform_space α] : uniform_space (quotient (separation_setoid α)) :=
{ to_topological_space := u.to_topological_space.coinduced (λx, ⟦x⟧),
  uniformity := map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity,
  refl := assume s hs ⟨a, b⟩ (h : a = b),
    have ∀a:α, (a, a) ∈ preimage (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) s,
      from assume a, refl_mem_uniformity hs,
    h ▸ quotient.induction_on a this,
  symm := tendsto_map' $
    by simp [prod.swap, (∘)]; exact tendsto_swap_uniformity.comp tendsto_map,
  comp := calc (map (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) uniformity).lift' (λs, comp_rel s s) =
          uniformity.lift' ((λs, comp_rel s s) ∘ image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧))) :
      map_lift'_eq2 $ monotone_comp_rel monotone_id monotone_id
    ... ≤ uniformity.lift' (image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ∘ (λs:set (α×α), comp_rel s (comp_rel s s))) :
      lift'_mono' $ assume s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩,
      begin
        simp at a_eq,
        simp at b_eq,
        have h : ⟦a₂⟧ = ⟦b₁⟧, { rw [a_eq.right, b_eq.left] },
        have h : (a₂, b₁) ∈ separation_rel α := quotient.exact h,
        simp [function.comp, set.image, comp_rel, and.comm, and.left_comm, and.assoc],
        exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩
      end
    ... = map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) (uniformity.lift' (λs:set (α×α), comp_rel s (comp_rel s s))) :
      by rw [map_lift'_eq];
        exact monotone_comp_rel monotone_id (monotone_comp_rel monotone_id monotone_id)
    ... ≤ map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity :
      map_mono comp_le_uniformity3,
  is_open_uniformity := assume s,
    have ∀a, ⟦a⟧ ∈ s →
        ({p:α×α | p.1 = a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets ↔
          {p:α×α | p.1 ≈ a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets),
      from assume a ha,
      ⟨assume h,
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h in
        have hts : ∀{a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s,
          from assume a₁ a₂ ha₁ ha₂, @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl,
        have ht' : ∀{a₁ a₂}, a₁ ≈ a₂ → (a₁, a₂) ∈ t,
          from assume a₁ a₂ h, sInter_subset_of_mem ht h,
        uniformity.sets_of_superset ht $ assume ⟨a₁, a₂⟩ h₁ h₂, hts (ht' $ setoid.symm h₂) h₁,
        assume h, uniformity.sets_of_superset h $ by simp {contextual := tt}⟩,
    begin
      simp [topological_space.coinduced, u.is_open_uniformity, uniformity, forall_quotient_iff],
      exact ⟨λh a ha, (this a ha).mp $ h a ha, λh a ha, (this a ha).mpr $ h a ha⟩
    end }

lemma uniform_continuous_quotient_mk :
  uniform_continuous (quotient.mk : α → quotient (separation_setoid α)) :=
le_refl _

lemma uniform_continuous_quotient {f : quotient (separation_setoid α) → β}
  (hf : uniform_continuous (λx, f ⟦x⟧)) : uniform_continuous f :=
hf

lemma uniform_continuous_quotient_lift
  {f : α → β} {h : ∀a b, (a, b) ∈ separation_rel α → f a = f b}
  (hf : uniform_continuous f) : uniform_continuous (λa, quotient.lift f h a) :=
uniform_continuous_quotient hf

lemma uniformity_quotient :
  @uniformity (quotient (separation_setoid α)) _ = uniformity.map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) :=
rfl

lemma comap_quotient_le_uniformity :
  uniformity.comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ≤ uniformity :=
assume t' ht',
let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht' in
let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht in
⟨(λp:α×α, (⟦p.1⟧, ⟦p.2⟧)) '' s,
  (@uniformity α _).sets_of_superset hs $ assume x hx, ⟨x, hx, rfl⟩,
  assume ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩,
  have ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧, from prod.mk.inj ab_eq,
  have b₁ ≈ a₁ ∧ b₂ ≈ a₂, from and.imp quotient.exact quotient.exact this,
  have ab₁ : (a₁, b₁) ∈ t, from (setoid.symm this.left) t ht,
  have ba₂ : (b₂, a₂) ∈ s, from this.right s hs,
  tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t, from ab₁,
    ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s, from hb, ba₂⟩⟩⟩

lemma comap_quotient_eq_uniformity :
  uniformity.comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) = uniformity :=
le_antisymm comap_quotient_le_uniformity le_comap_map

lemma complete_space_separation [h : complete_space α] :
  complete_space (quotient (separation_setoid α)) :=
⟨assume f, assume hf : cauchy f,
  have cauchy (f.comap (λx, ⟦x⟧)), from
    cauchy_comap comap_quotient_le_uniformity hf $
      comap_neq_bot_of_surj hf.left $ assume b, quotient.exists_rep _,
  let ⟨x, (hx : f.comap (λx, ⟦x⟧) ≤ nhds x)⟩ := complete_space.complete this in
  ⟨⟦x⟧, calc f ≤ map (λx, ⟦x⟧) (f.comap (λx, ⟦x⟧)) : le_map_comap $ assume b, quotient.exists_rep _
    ... ≤ map (λx, ⟦x⟧) (nhds x) : map_mono hx
    ... ≤ _ : continuous_iff_tendsto.mp uniform_continuous_quotient_mk.continuous _⟩⟩

lemma separated_separation [h : complete_space α] : separated (quotient (separation_setoid α)) :=
set.ext $ assume ⟨a, b⟩, quotient.induction_on₂ a b $ assume a b,
  ⟨assume h,
    have a ≈ b, from assume s hs,
      have s ∈ (uniformity.comap (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧))).sets,
        from comap_quotient_le_uniformity hs,
      let ⟨t, ht, hts⟩ := this in
      hts begin dsimp, exact h t ht end,
    show ⟦a⟧ = ⟦b⟧, from quotient.sound this,

  assume heq : ⟦a⟧ = ⟦b⟧, assume h hs,
  heq ▸ refl_mem_uniformity hs⟩

lemma separated_of_uniform_continuous {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma eq_of_separated_of_uniform_continuous [separated β] {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separated_of_uniform_continuous H h

lemma uniform_continuous_quotient_lift₂ [uniform_space γ]
  {f : α → β → γ} {h : ∀a c b d, (a, b) ∈ separation_rel α → (c, d) ∈ separation_rel β → f a c = f b d}
  (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  uniform_continuous (λp:_×_, quotient.lift₂ f h p.1 p.2) :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    filter.prod_map_map_eq, filter.tendsto_map'_iff, filter.tendsto_map'_iff],
  rwa [uniform_continuous, uniformity_prod_eq_prod, filter.tendsto_map'_iff] at hf
end

lemma separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
begin
  split,
  { assume h,
    exact ⟨separated_of_uniform_continuous uniform_continuous_fst h,
           separated_of_uniform_continuous uniform_continuous_snd h⟩ },
  { rintros ⟨eqv_α, eqv_β⟩ r r_in,
    rw uniformity_prod at r_in,
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, H⟩,

    let p_α := λ(p : (α × β) × (α × β)), (p.1.1, p.2.1),
    let p_β := λ(p : (α × β) × (α × β)), (p.1.2, p.2.2),
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α, { simp [p_α, eqv_α r_α r_α_in] },
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β, { simp [p_β, eqv_β r_β r_β_in] },
    exact H ⟨h_α key_α, h_β key_β⟩ },
end

instance separated.prod [separated α] [separated β] : separated (α × β) :=
separated_def.2 $ assume x y H, prod.ext
  (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
  (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)

end uniform_space

/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f }

namespace Cauchy

section
parameters {α : Type u} [uniform_space α]
variables {β : Type v} {γ : Type w}
variables [uniform_space β] [uniform_space γ]

def gen (s : set (α × α)) : set (Cauchy α × Cauchy α) :=
{p | s ∈ (filter.prod (p.1.val) (p.2.val)).sets }

lemma monotone_gen : monotone gen :=
monotone_set_of $ assume p, @monotone_mem_sets (α×α) (filter.prod (p.1.val) (p.2.val))

private lemma symm_gen : map prod.swap (uniformity.lift' gen) ≤ uniformity.lift' gen :=
calc map prod.swap (uniformity.lift' gen) =
  uniformity.lift' (λs:set (α×α), {p | s ∈ (filter.prod (p.2.val) (p.1.val)).sets }) :
  begin
    delta gen,
    simp [map_lift'_eq, monotone_set_of, monotone_mem_sets,
          function.comp, image_swap_eq_preimage_swap]
  end
  ... ≤ uniformity.lift' gen :
    uniformity_lift_le_swap
      (monotone_comp (monotone_set_of $ assume p,
        @monotone_mem_sets (α×α) ((filter.prod ((p.2).val) ((p.1).val)))) monotone_principal)
      begin
        have h := λ(p:Cauchy α×Cauchy α), @filter.prod_comm _ _ (p.2.val) (p.1.val),
        simp [function.comp, h],
        exact le_refl _
      end

private lemma comp_rel_gen_gen_subset_gen_comp_rel {s t : set (α×α)} : comp_rel (gen s) (gen t) ⊆
  (gen (comp_rel s t) : set (Cauchy α × Cauchy α)) :=
assume ⟨f, g⟩ ⟨h, h₁, h₂⟩,
let ⟨t₁, (ht₁ : t₁ ∈ f.val.sets), t₂, (ht₂ : t₂ ∈ h.val.sets), (h₁ : set.prod t₁ t₂ ⊆ s)⟩ :=
  mem_prod_iff.mp h₁ in
let ⟨t₃, (ht₃ : t₃ ∈ h.val.sets), t₄, (ht₄ : t₄ ∈ g.val.sets), (h₂ : set.prod t₃ t₄ ⊆ t)⟩ :=
  mem_prod_iff.mp h₂ in
have t₂ ∩ t₃ ∈ h.val.sets,
  from inter_mem_sets ht₂ ht₃,
let ⟨x, xt₂, xt₃⟩ :=
  inhabited_of_mem_sets (h.property.left) this in
(filter.prod f.val g.val).sets_of_superset
  (prod_mem_prod ht₁ ht₄)
  (assume ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩,
    ⟨x,
      h₁ (show (a, x) ∈ set.prod t₁ t₂, from ⟨ha, xt₂⟩),
      h₂ (show (x, b) ∈ set.prod t₃ t₄, from ⟨xt₃, hb⟩)⟩)

private lemma comp_gen :
  (uniformity.lift' gen).lift' (λs, comp_rel s s) ≤ uniformity.lift' gen :=
calc (uniformity.lift' gen).lift' (λs, comp_rel s s) =
    uniformity.lift' (λs, comp_rel (gen s) (gen s)) :
  begin
    rw [lift'_lift'_assoc],
    exact monotone_gen,
    exact (monotone_comp_rel monotone_id monotone_id)
  end
  ... ≤ uniformity.lift' (λs, gen $ comp_rel s s) :
    lift'_mono' $ assume s hs, comp_rel_gen_gen_subset_gen_comp_rel
  ... = (uniformity.lift' $ λs:set(α×α), comp_rel s s).lift' gen :
  begin
    rw [lift'_lift'_assoc],
    exact (monotone_comp_rel monotone_id monotone_id),
    exact monotone_gen
  end
  ... ≤ uniformity.lift' gen : lift'_mono comp_le_uniformity (le_refl _)

instance completion_space : uniform_space (Cauchy α) :=
uniform_space.of_core
{ uniformity  := uniformity.lift' gen,
  refl        := principal_le_lift' $ assume s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a.property.right hs,
  symm        := symm_gen,
  comp        := comp_gen }

theorem mem_uniformity {s : set (Cauchy α × Cauchy α)} :
  s ∈ (@uniformity (Cauchy α) _).sets ↔ ∃ t ∈ (@uniformity α _).sets, gen t ⊆ s :=
mem_lift'_sets monotone_gen

theorem mem_uniformity' {s : set (Cauchy α × Cauchy α)} :
  s ∈ (@uniformity (Cauchy α) _).sets ↔ ∃ t ∈ (@uniformity α _).sets,
    ∀ f g : Cauchy α, t ∈ (filter.prod f.1 g.1).sets → (f, g) ∈ s :=
mem_uniformity.trans $ bex_congr $ λ t h, prod.forall

/-- Embedding of `α` into its completion -/
def pure_cauchy (a : α) : Cauchy α :=
⟨pure a, cauchy_pure⟩

lemma uniform_embedding_pure_cauchy : uniform_embedding (pure_cauchy : α → Cauchy α) :=
⟨assume a₁ a₂ h,
  have (pure_cauchy a₁).val = (pure_cauchy a₂).val, from congr_arg _ h,
  have {a₁} = ({a₂} : set α),
    from principal_eq_iff_eq.mp this,
  by simp at this; assumption,

  have (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) = id,
    from funext $ assume s, set.ext $ assume ⟨a₁, a₂⟩,
      by simp [preimage, gen, pure_cauchy, prod_principal_principal],
  calc comap (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) (uniformity.lift' gen)
        = uniformity.lift' (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) :
      comap_lift'_eq monotone_gen
    ... = uniformity : by simp [this]⟩

lemma pure_cauchy_dense : ∀x, x ∈ closure (range pure_cauchy) :=
assume f,
have h_ex : ∀s∈(@uniformity (Cauchy α) _).sets, ∃y:α, (f, pure_cauchy y) ∈ s, from
  assume s hs,
  let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs in
  let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁ in
  have t' ∈ (filter.prod (f.val) (f.val)).sets,
    from f.property.right ht'₁,
  let ⟨t, ht, (h : set.prod t t ⊆ t')⟩ := mem_prod_same_iff.mp this in
  let ⟨x, (hx : x ∈ t)⟩ := inhabited_of_mem_sets f.property.left ht in
  have t'' ∈ (filter.prod f.val (pure x)).sets,
    from mem_prod_iff.mpr ⟨t, ht, {y:α | (x, y) ∈ t'},
      assume y, begin simp, intro h, simp [h], exact refl_mem_uniformity ht'₁ end,
      assume ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩,
        ht'₂ $ prod_mk_mem_comp_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩,
  ⟨x, ht''₂ $ by dsimp [gen]; exact this⟩,
begin
  simp [closure_eq_nhds, nhds_eq_uniformity, lift'_inf_principal_eq, set.inter_comm],
  exact (lift'_neq_bot_iff $ monotone_inter monotone_const monotone_preimage).mpr
    (assume s hs,
      let ⟨y, hy⟩ := h_ex s hs in
      have pure_cauchy y ∈ range pure_cauchy ∩ {y : Cauchy α | (f, y) ∈ s},
        from ⟨mem_range_self y, hy⟩,
      ne_empty_of_mem this)
end

section
set_option eqn_compiler.zeta true
instance : complete_space (Cauchy α) :=
complete_space_extension
  uniform_embedding_pure_cauchy
  pure_cauchy_dense $
  assume f hf,
  let f' : Cauchy α := ⟨f, hf⟩ in
  have map pure_cauchy f ≤ uniformity.lift' (preimage (prod.mk f')),
    from le_lift' $ assume s hs,
    let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs in
    let ⟨t', ht', (h : set.prod t' t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁) in
    have t' ⊆ { y : α | (f', pure_cauchy y) ∈ gen t },
      from assume x hx, (filter.prod f (pure x)).sets_of_superset (prod_mem_prod ht' $ mem_pure hx) h,
    f.sets_of_superset ht' $ subset.trans this (preimage_mono ht₂),
  ⟨f', by simp [nhds_eq_uniformity]; assumption⟩
end
end

instance {α : Type u} [inhabited α] [uniform_space α] : inhabited (Cauchy α) :=
⟨Cauchy.pure_cauchy $ default α⟩

instance {α : Type u} [h : nonempty α] [uniform_space α] : nonempty (Cauchy α) :=
h.rec_on $ assume a, nonempty.intro $ Cauchy.pure_cauchy a

end Cauchy

namespace uniform_space
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]
open Cauchy

local attribute [instance] separation_setoid

lemma prod_cauchy {f : filter α} {g : filter β} : cauchy f → cauchy g → cauchy (filter.prod f g)
| ⟨f_proper, hf⟩ ⟨g_proper, hg⟩ := ⟨filter.prod_neq_bot.2 ⟨f_proper, g_proper⟩,
  let p_α := λp:(α×β)×(α×β), (p.1.1, p.2.1), p_β := λp:(α×β)×(α×β), (p.1.2, p.2.2) in
  suffices (f.prod f).comap p_α ⊓ (g.prod g).comap p_β ≤ uniformity.comap p_α ⊓ uniformity.comap p_β,
    by simpa [uniformity_prod, filter.prod, filter.comap_inf, filter.comap_comap_comp, (∘),
        lattice.inf_assoc, lattice.inf_comm, lattice.inf_left_comm],
  lattice.inf_le_inf (filter.comap_mono hf) (filter.comap_mono hg)⟩

def pure_cauchy₂ : α × β → Cauchy α × Cauchy β := λ x, (pure_cauchy x.1, pure_cauchy x.2)

lemma pure_cauchy_dense₂ : ∀x : Cauchy α × Cauchy β, x ∈ closure (range (@pure_cauchy₂ α β _ _)) :=
begin
  intro x,
  dsimp[pure_cauchy₂],
  rw [←prod_range_range_eq, closure_prod_eq],
  simp[prod.ext_iff, pure_cauchy_dense],
end

namespace pure_cauchy

def de := uniform_embedding_pure_cauchy.dense_embedding (@pure_cauchy_dense α _)

lemma prod.de : dense_embedding (λ p : α × β, (pure_cauchy p.1, pure_cauchy p.2)) :=
dense_embedding.prod pure_cauchy.de pure_cauchy.de

end pure_cauchy

lemma injective_separated_pure_cauchy {α : Type*} [uniform_space α] [s : separated α] :
  function.injective (λa:α, ⟦pure_cauchy a⟧) | a b h :=
separated_def.1 s _ _ $ assume s hs,
let ⟨t, ht, hts⟩ :=
  by rw [← (@uniform_embedding_pure_cauchy α _).right, filter.mem_comap_sets] at hs; exact hs in
have (pure_cauchy a, pure_cauchy b) ∈ t, from quotient.exact h t ht,
@hts (a, b) this

end uniform_space

local attribute [instance] uniform_space.separation_setoid

open Cauchy set

namespace uniform_space
variables (α : Type*) [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]

/-- Hausdorff completion of `α` -/
def completion := quotient (separation_setoid $ Cauchy α)

@[priority 50]
instance completion_uniform_space : uniform_space (completion α) := by unfold completion ; apply_instance

instance completion_complete : complete_space (completion α) := complete_space_separation

instance completion_separated : separated (completion α) := separated_separation

instance completion_t2 : t2_space (completion α) := separated_t2

instance completion_regular : regular_space (completion α) := separated_regular

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance : has_coe α (completion α) := ⟨quotient.mk ∘ pure_cauchy⟩

namespace to_completion
open set

lemma uniform_continuous : uniform_continuous (coe : α → completion α) :=
uniform_continuous.comp uniform_embedding_pure_cauchy.uniform_continuous
  uniform_continuous_quotient_mk

lemma continuous : continuous (coe : α → completion α) :=
uniform_continuous.continuous (uniform_continuous α)

variable {α}

lemma dense : closure (range (coe : α → completion α)) = univ   :=
begin
  unfold_coes,
  rw range_comp,
  exact quotient_dense_of_dense pure_cauchy_dense
end

lemma dense₁ : closure (range (λ x : α, (x : completion α))) = univ :=
to_completion.dense

lemma dense₂ : let φ : α × β → (completion α) × (completion β) := λ x, ⟨x.1, x.2⟩ in
  closure (range φ) = univ :=
begin
  intro φ,
  have : range φ = set.prod (range (coe : α → completion α)) (range (coe : β → completion β)),
  { ext x,
    dsimp[φ],
    unfold_coes,
    simp[prod.ext_iff] },
  simp [this, closure_prod_eq, dense]
end

lemma dense₃ : let β := completion α in let φ : α × α × α → β × β × β := λ x, ⟨x.1, x.2.1, x.2.2⟩ in
  closure (range φ) = univ :=
begin
  intros β φ,
  have : range φ = set.prod (range (coe : α → completion α)) (set.prod (range (coe : α → completion α)) (range (coe : α → completion α))),
  { ext x,
    dsimp[φ],
    unfold_coes,
    simp[prod.ext_iff] },
  simp [this, closure_prod_eq, dense]
end
end to_completion

variable {α}
lemma nonempty_completion_iff : nonempty (completion α) ↔ nonempty α :=
begin
  split ; rintro ⟨c⟩,
  { have := eq_univ_iff_forall.1 to_completion.dense c,
    have := mem_closure_iff.1 this _ is_open_univ trivial,
    rcases exists_mem_of_ne_empty this with ⟨_, ⟨_, a, _⟩⟩,
    exact ⟨a⟩ },
  { exact ⟨(c : completion α)⟩ }
end

variables [complete_space β] [separated β]

/-- "Extension" to the completion.
    Defined for any map `f` but returns garbage if `f` is not uniformly continuous -/
noncomputable
def completion_extension (f : α → β) : completion α → β :=
if H : uniform_continuous f then
  let g₀ := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend f in
  have g₀_unif : uniform_continuous g₀ :=
    uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense H,
  have compat : ∀ p q : Cauchy α, p ≈ q → g₀ p = g₀ q :=
    assume p q h, eq_of_separated_of_uniform_continuous g₀_unif h,
  quotient.lift g₀ compat
else
  λ x, f (classical.inhabited_of_nonempty $ nonempty_completion_iff.1 ⟨x⟩).default

/-- Completion functor acting on morphisms -/
noncomputable def completion.map (f : α → γ) : completion α → completion γ :=
completion_extension (coe ∘ f)
end uniform_space

namespace completion_extension
open uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables [complete_space β] [separated β]

variables {f : α → β} (H : uniform_continuous f)
include H

lemma lifts : f = (completion_extension f) ∘ coe :=
begin
  unfold completion_extension,
  simp [H],
  ext x,
  let lim := H.continuous.tendsto x,
  have := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend_e_eq lim,
  rw ←this,
  refl
end

@[simp]
lemma lifts' : ∀ a : α, f a = (completion_extension f) a := λ a, congr_fun (lifts H) a

lemma uniform_continuity : uniform_continuous (completion_extension f) :=
begin
  unfold completion_extension,
  split_ifs,
  let g := completion_extension f,
  intros r r_in,
  let g₀ := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend f,
  have g₀_unif : uniform_continuous g₀ :=
    uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense H,

  rw filter.mem_map,
  dsimp[completion],
  rw prod_quotient_preimage_eq_image _ rfl r,
  exact filter.image_mem_map (g₀_unif r_in)
end

lemma continuity : continuous (completion_extension f) :=
uniform_continuous.continuous (uniform_continuity H)

lemma unique {h : completion α → β} :
  uniform_continuous h → f = h ∘ coe → h = completion_extension f :=
begin
  let g := completion_extension f,
  have g_unif : uniform_continuous g := uniform_continuity H,
  intros h_unif h_lifts,
  change h = g,
  ext x,
  have closed_eq : is_closed {x | h x = g x} := is_closed_eq h_unif.continuous g_unif.continuous,
  have : f = g ∘ coe := lifts H,
  have eq_on_α : ∀ x, (h ∘ (coe : α → completion α)) x = (g ∘ (coe : α → completion α)) x, by cc,
  exact (is_closed_property to_completion.dense closed_eq eq_on_α x : _)
end
end completion_extension

namespace completion
variables {α : Type*} [uniform_space α] {β : Type*} [uniform_space β]
open uniform_space uniform_space.pure_cauchy

noncomputable def prod : (completion α) × (completion β) → completion (α × β) :=
begin
  let g₀ := λ (a : Cauchy α) (b : Cauchy β),
    (prod.de.extend (coe : (α × β) → completion (α × β))) (a, b),

  refine function.uncurry (quotient.lift₂ g₀ _),
  { intros a₁ b₁ a₂ b₂ eqv₁ eqv₂,
    have g₁_uc : uniform_continuous (prod.de.extend (coe : α × β → completion (α × β))),
    { let ue : uniform_embedding (λ (p : α × β), (pure_cauchy (p.fst), pure_cauchy (p.snd))) :=
        uniform_embedding.prod uniform_embedding_pure_cauchy uniform_embedding_pure_cauchy,
      refine uniform_continuous_uniformly_extend ue _ (to_completion.uniform_continuous (α × β)) },

    exact (eq_of_separated_of_uniform_continuous g₁_uc (separation_prod.2 ⟨eqv₁, eqv₂⟩) : _) },
end

lemma prod.uc : uniform_continuous (@prod α _ β _) :=
begin
  dsimp[prod],
  rw function.uncurry_def,
  apply uniform_continuous_quotient_lift₂,
  suffices : uniform_continuous (dense_embedding.extend prod.de (coe : α × β → completion (α × β))),
  by simpa,
  exact uniform_continuous_uniformly_extend
    (uniform_embedding.prod uniform_embedding_pure_cauchy uniform_embedding_pure_cauchy)
    prod.de.dense (to_completion.uniform_continuous _)
end

@[simp]
lemma prod.lifts (a : α) (b : β) : @prod α _ β _ (a, b) = (a, b) :=
begin
  let f := (coe : (α × β) → completion (α × β)),
  change dense_embedding.extend prod.de f (pure_cauchy a, pure_cauchy b) = ⟦pure_cauchy (a, b)⟧,

  have hf : filter.tendsto f (nhds (a, b)) (nhds (f (a,b))) :=
    continuous.tendsto (to_completion.continuous _) _,

  exact (prod.de.extend_e_eq hf : _)
end
/-- Canonical map completion (α × β) → (completion α) × (completion β). Not used in group_completion. -/
noncomputable def prod_inv : completion (α × β) → (completion α) × (completion β) :=
completion_extension (λ x, (x.1, x.2))

@[simp]
lemma prod_inv.lifts : ∀ x : α × β, prod_inv (x : completion (α × β)) = ((x.1 : completion α), (x.2 : completion β)) :=
begin
  intros x,
  have u1 := uniform_continuous.comp uniform_continuous_fst (to_completion.uniform_continuous α),
  have u2 := uniform_continuous.comp uniform_continuous_snd (to_completion.uniform_continuous β),
  have := completion_extension.lifts' (uniform_continuous.prod_mk u1 u2) x,
  finish
end

lemma prod_inv.uc : uniform_continuous (@prod_inv α _ β _) :=
begin
  have u1 := uniform_continuous.comp uniform_continuous_fst (to_completion.uniform_continuous α),
  have u2 := uniform_continuous.comp uniform_continuous_snd (to_completion.uniform_continuous β),
  exact completion_extension.uniform_continuity (uniform_continuous.prod_mk u1 u2)
end
end completion

namespace uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]
open uniform_space function

noncomputable def completion.map₂ (f : α → β → γ) : completion α × completion β → completion γ :=
  completion.map (uncurry f) ∘ completion.prod
end uniform_space

namespace completion.map
open uniform_space uniform_space.completion
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]
variables {δ : Type*} [uniform_space δ]

variables {f : α → β} (H : uniform_continuous f)
variables {g : β → γ} (H' : uniform_continuous g)

lemma lifts : coe ∘ f = (map f) ∘ coe :=
completion_extension.lifts $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma lifts' : ∀ a : α, (f a : completion β) = map f a :=
congr_fun (lifts H)

lemma unique {f' : completion α → completion β} :
  uniform_continuous f' → coe ∘ f = f' ∘ coe → f' = map f :=
completion_extension.unique $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma uniform_continuity : uniform_continuous (map f) :=
completion_extension.uniform_continuity $ uniform_continuous.comp H (to_completion.uniform_continuous β)

protected lemma id : completion.map (@id α) = id :=
by rw (unique uniform_continuous_id uniform_continuous_id) ; simp

@[simp]
protected lemma const (a : α) : completion.map (λ x : α, a) = (λ x, a) :=
by rw unique uniform_continuous_const uniform_continuous_const ; refl

lemma prod_prod_inv : completion.prod ∘ (@completion.prod_inv α _ β _) = id :=
begin
  rw ←completion.map.id,
  apply completion.map.unique uniform_continuous_id
    (uniform_continuous.comp completion.prod_inv.uc completion.prod.uc),
  ext x,
  simp
end

lemma prod_inv_prod : completion.prod_inv ∘ (@completion.prod α _ β _) = id :=
begin
  funext x,
  have closed : is_closed {x | (completion.prod_inv ∘ (@completion.prod α _ β _)) x = id x},
  { have c₁ : continuous (completion.prod_inv ∘ (@completion.prod α _ β _)) :=
      continuous.comp (completion.prod.uc.continuous) (completion.prod_inv.uc.continuous),
    exact is_closed_eq c₁ continuous_id },

  exact (is_closed_property to_completion.dense₂ closed (by simp) x : _)
end

include H H'
lemma comp : completion.map (g ∘ f) = (map g) ∘ map f :=
begin
  let l  := completion.map f,
  let l' := completion.map g,
  have : uniform_continuous (g ∘ f) := uniform_continuous.comp H H',
  have : uniform_continuous (l' ∘ l ):=
    uniform_continuous.comp (uniform_continuity H) (uniform_continuity H'),
  have : coe ∘ g ∘ f = l' ∘ l ∘ coe  := calc
    (coe ∘ g) ∘ f = (l' ∘ coe) ∘ f : by rw completion.map.lifts H'
    ... = l' ∘ (coe ∘ f) : rfl
    ... = l' ∘ (l  ∘ coe) : by rw completion.map.lifts H,
  apply eq.symm,
  apply unique ; assumption
end
omit H H'

open function
variables {h : α → β → γ} (h_uc : uniform_continuous (uncurry h))

include h_uc
lemma lifts₂ : coe ∘ (uncurry h) = (map₂ h) ∘ (λ p, (p.1, p.2)) :=
begin
  ext x,
  rw lifts h_uc,
  apply congr_arg (completion.map (uncurry h)),
  simp
end

lemma lifts₂' : ∀ (a : α) (b : β), (h a b : completion γ) = map₂ h (a, b) :=
λ a b, congr_fun (lifts₂ h_uc) (a,b)

lemma uniform_continuity₂ : uniform_continuous (map₂ h) :=
uniform_continuous.comp completion.prod.uc (uniform_continuity h_uc)

lemma map₂_map_map {f : δ → α} {g : δ → β} (f_uc : uniform_continuous f) (g_uc : uniform_continuous g) :
  completion.map (λ x, h (f x) (g x)) = λ y, map₂ h (map f y, map g y) :=
begin
  apply eq.symm,
  have uc₁ := (f_uc.prod_mk g_uc).comp h_uc,
  have uc₂ := ((uniform_continuity f_uc).prod_mk (uniform_continuity g_uc)).comp (uniform_continuity₂ h_uc),
  apply unique uc₁ uc₂,
  ext x,
  change (h (f x) (g x) : completion γ) = map₂ h (map f x, map g x),
  rw [←lifts' f_uc x, ←lifts' g_uc x, lifts₂' h_uc]
end

end completion.map
