/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Theory of topological spaces.

Parts of the formalization is based on the books:
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
A major difference is that this formalization is heavily based on the filter library.
-/
import order.filter data.set.countable tactic

open set filter lattice classical
local attribute [instance] prop_decidable

universes u v w

structure topological_space (α : Type u) :=
(is_open       : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

attribute [class] topological_space

section topological_space

variables {α : Type u} {β : Type v} {ι : Sort w} {a a₁ a₂ : α} {s s₁ s₂ : set α} {p p₁ p₂ : α → Prop}

lemma topological_space_eq : ∀ {f g : topological_space α}, f.is_open = g.is_open → f = g
| ⟨a, _, _, _⟩ ⟨b, _, _, _⟩ rfl := rfl

section
variables [t : topological_space α]
include t

/-- `is_open s` means that `s` is open in the ambient topological space on `α` -/
def is_open (s : set α) : Prop := topological_space.is_open t s

@[simp]
lemma is_open_univ : is_open (univ : set α) := topological_space.is_open_univ t

lemma is_open_inter (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∩ s₂) :=
topological_space.is_open_inter t s₁ s₂ h₁ h₂

lemma is_open_sUnion {s : set (set α)} (h : ∀t ∈ s, is_open t) : is_open (⋃₀ s) :=
topological_space.is_open_sUnion t s h

end

lemma is_open_fold {s : set α} {t : topological_space α} : t.is_open s = @is_open α t s :=
rfl

variables [topological_space α]

lemma is_open_union (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∪ s₂) :=
have (⋃₀ {s₁, s₂}) = (s₁ ∪ s₂), by simp [union_comm],
this ▸ is_open_sUnion $ show ∀(t : set α), t ∈ ({s₁, s₂} : set (set α)) → is_open t,
  by finish

lemma is_open_Union {f : ι → set α} (h : ∀i, is_open (f i)) : is_open (⋃i, f i) :=
is_open_sUnion $ assume t ⟨i, (heq : t = f i)⟩, heq.symm ▸ h i

lemma is_open_bUnion {s : set β} {f : β → set α} (h : ∀i∈s, is_open (f i)) :
  is_open (⋃i∈s, f i) :=
is_open_Union $ assume i, is_open_Union $ assume hi, h i hi

@[simp] lemma is_open_empty : is_open (∅ : set α) :=
have is_open (⋃₀ ∅ : set α), from is_open_sUnion (assume a, false.elim),
by simp at this; assumption

lemma is_open_sInter {s : set (set α)} (hs : finite s) : (∀t ∈ s, is_open t) → is_open (⋂₀ s) :=
finite.induction_on hs (by simp) $ λ a s has hs ih h, begin
  suffices : is_open (a ∩ ⋂₀ s), { simpa },
  exact is_open_inter (h _ $ mem_insert _ _) (ih $ assume t ht, h _ $ mem_insert_of_mem _ ht)
end

lemma is_open_bInter {s : set β} {f : β → set α} (hs : finite s) :
  (∀i∈s, is_open (f i)) → is_open (⋂i∈s, f i) :=
finite.induction_on hs
  (by simp)
  (by simp [or_imp_distrib, _root_.is_open_inter, forall_and_distrib] {contextual := tt})

lemma is_open_const {p : Prop} : is_open {a : α | p} :=
by_cases
  (assume : p, begin simp [*]; exact is_open_univ end)
  (assume : ¬ p, begin simp [*]; exact is_open_empty end)

lemma is_open_and : is_open {a | p₁ a} → is_open {a | p₂ a} → is_open {a | p₁ a ∧ p₂ a} :=
is_open_inter

/-- A set is closed if its complement is open -/
def is_closed (s : set α) : Prop := is_open (-s)

@[simp] lemma is_closed_empty : is_closed (∅ : set α) := by simp [is_closed]

@[simp] lemma is_closed_univ : is_closed (univ : set α) := by simp [is_closed]

lemma is_closed_union : is_closed s₁ → is_closed s₂ → is_closed (s₁ ∪ s₂) :=
by simp [is_closed]; exact is_open_inter

lemma is_closed_sInter {s : set (set α)} : (∀t ∈ s, is_closed t) → is_closed (⋂₀ s) :=
by simp [is_closed, compl_sInter]; exact assume h, is_open_Union $ assume t, is_open_Union $ assume ht, h t ht

lemma is_closed_Inter {f : ι → set α} (h : ∀i, is_closed (f i)) : is_closed (⋂i, f i ) :=
is_closed_sInter $ assume t ⟨i, (heq : t = f i)⟩, heq.symm ▸ h i

@[simp] lemma is_open_compl_iff {s : set α} : is_open (-s) ↔ is_closed s := iff.rfl

@[simp] lemma is_closed_compl_iff {s : set α} : is_closed (-s) ↔ is_open s :=
by rw [←is_open_compl_iff, compl_compl]

lemma is_open_diff {s t : set α} (h₁ : is_open s) (h₂ : is_closed t) : is_open (s \ t) :=
is_open_inter h₁ $ is_open_compl_iff.mpr h₂

lemma is_closed_inter (h₁ : is_closed s₁) (h₂ : is_closed s₂) : is_closed (s₁ ∩ s₂) :=
by rw [is_closed, compl_inter]; exact is_open_union h₁ h₂

lemma is_closed_Union {s : set β} {f : β → set α} (hs : finite s) :
  (∀i∈s, is_closed (f i)) → is_closed (⋃i∈s, f i) :=
finite.induction_on hs
  (by simp)
  (by simp [or_imp_distrib, is_closed_union, forall_and_distrib] {contextual := tt})

lemma is_closed_imp [topological_space α] {p q : α → Prop}
  (hp : is_open {x | p x}) (hq : is_closed {x | q x}) : is_closed {x | p x → q x} :=
have {x | p x → q x} = (- {x | p x}) ∪ {x | q x}, from set.ext $ by finish,
by rw [this]; exact is_closed_union (is_closed_compl_iff.mpr hp) hq

lemma is_open_neg : is_closed {a | p a} → is_open {a | ¬ p a} :=
is_open_compl_iff.mpr

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : set α) : set α := ⋃₀ {t | is_open t ∧ t ⊆ s}

lemma mem_interior {s : set α} {x : α} :
  x ∈ interior s ↔ ∃ t ⊆ s, is_open t ∧ x ∈ t :=
by simp [interior, and_comm, and.left_comm]

@[simp] lemma is_open_interior {s : set α} : is_open (interior s) :=
is_open_sUnion $ assume t ⟨h₁, h₂⟩, h₁

lemma interior_subset {s : set α} : interior s ⊆ s :=
sUnion_subset $ assume t ⟨h₁, h₂⟩, h₂

lemma interior_maximal {s t : set α} (h₁ : t ⊆ s) (h₂ : is_open t) : t ⊆ interior s :=
subset_sUnion_of_mem ⟨h₂, h₁⟩

lemma interior_eq_of_open {s : set α} (h : is_open s) : interior s = s :=
subset.antisymm interior_subset (interior_maximal (subset.refl s) h)

lemma interior_eq_iff_open {s : set α} : interior s = s ↔ is_open s :=
⟨assume h, h ▸ is_open_interior, interior_eq_of_open⟩

lemma subset_interior_iff_open {s : set α} : s ⊆ interior s ↔ is_open s :=
by simp [interior_eq_iff_open.symm, subset.antisymm_iff, interior_subset]

lemma subset_interior_iff_subset_of_open {s t : set α} (h₁ : is_open s) :
  s ⊆ interior t ↔ s ⊆ t :=
⟨assume h, subset.trans h interior_subset, assume h₂, interior_maximal h₂ h₁⟩

lemma interior_mono {s t : set α} (h : s ⊆ t) : interior s ⊆ interior t :=
interior_maximal (subset.trans interior_subset h) is_open_interior

@[simp] lemma interior_empty : interior (∅ : set α) = ∅ :=
interior_eq_of_open is_open_empty

@[simp] lemma interior_univ : interior (univ : set α) = univ :=
interior_eq_of_open is_open_univ

@[simp] lemma interior_interior {s : set α} : interior (interior s) = interior s :=
interior_eq_of_open is_open_interior

@[simp] lemma interior_inter {s t : set α} : interior (s ∩ t) = interior s ∩ interior t :=
subset.antisymm
  (subset_inter (interior_mono $ inter_subset_left s t) (interior_mono $ inter_subset_right s t))
  (interior_maximal (inter_subset_inter interior_subset interior_subset) $ by simp [is_open_inter])

lemma interior_union_is_closed_of_interior_empty {s t : set α} (h₁ : is_closed s) (h₂ : interior t = ∅) :
  interior (s ∪ t) = interior s :=
have interior (s ∪ t) ⊆ s, from
  assume x ⟨u, ⟨(hu₁ : is_open u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩,
  classical.by_contradiction $ assume hx₂ : x ∉ s,
    have u \ s ⊆ t,
      from assume x ⟨h₁, h₂⟩, or.resolve_left (hu₂ h₁) h₂,
    have u \ s ⊆ interior t,
      by simp [subset_interior_iff_subset_of_open, this, is_open_diff hu₁ h₁],
    have u \ s ⊆ ∅,
      by rw [h₂] at this; assumption,
    this ⟨hx₁, hx₂⟩,
subset.antisymm
  (interior_maximal this is_open_interior)
  (interior_mono $ subset_union_left _ _)

lemma is_open_iff_forall_mem_open : is_open s ↔ ∀ x ∈ s, ∃ t ⊆ s, is_open t ∧ x ∈ t :=
by rw ← subset_interior_iff_open; simp [subset_def, mem_interior]

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : set α) : set α := ⋂₀ {t | is_closed t ∧ s ⊆ t}

@[simp] lemma is_closed_closure {s : set α} : is_closed (closure s) :=
is_closed_sInter $ assume t ⟨h₁, h₂⟩, h₁

lemma subset_closure {s : set α} : s ⊆ closure s :=
subset_sInter $ assume t ⟨h₁, h₂⟩, h₂

lemma closure_minimal {s t : set α} (h₁ : s ⊆ t) (h₂ : is_closed t) : closure s ⊆ t :=
sInter_subset_of_mem ⟨h₂, h₁⟩

lemma closure_eq_of_is_closed {s : set α} (h : is_closed s) : closure s = s :=
subset.antisymm (closure_minimal (subset.refl s) h) subset_closure

lemma closure_eq_iff_is_closed {s : set α} : closure s = s ↔ is_closed s :=
⟨assume h, h ▸ is_closed_closure, closure_eq_of_is_closed⟩

lemma closure_subset_iff_subset_of_is_closed {s t : set α} (h₁ : is_closed t) :
  closure s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_closure, assume h, closure_minimal h h₁⟩

lemma closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_minimal (subset.trans h subset_closure) is_closed_closure

@[simp] lemma closure_empty : closure (∅ : set α) = ∅ :=
closure_eq_of_is_closed is_closed_empty

lemma closure_empty_iff (s : set α) : closure s = ∅ ↔ s = ∅ :=
begin
  split ; intro h,
  { rw set.eq_empty_iff_forall_not_mem,
    intros x H,
    simpa [h] using subset_closure H },
  { exact (eq.symm h) ▸ closure_empty },
end

@[simp] lemma closure_univ : closure (univ : set α) = univ :=
closure_eq_of_is_closed is_closed_univ

@[simp] lemma closure_closure {s : set α} : closure (closure s) = closure s :=
closure_eq_of_is_closed is_closed_closure

@[simp] lemma closure_union {s t : set α} : closure (s ∪ t) = closure s ∪ closure t :=
subset.antisymm
  (closure_minimal (union_subset_union subset_closure subset_closure) $ by simp [is_closed_union])
  (union_subset (closure_mono $ subset_union_left _ _) (closure_mono $ subset_union_right _ _))

lemma interior_subset_closure {s : set α} : interior s ⊆ closure s :=
subset.trans interior_subset subset_closure

lemma closure_eq_compl_interior_compl {s : set α} : closure s = - interior (- s) :=
begin
  simp [interior, closure],
  rw [compl_sUnion, compl_image_set_of],
  simp [compl_subset_compl]
end

@[simp] lemma interior_compl_eq {s : set α} : interior (- s) = - closure s :=
by simp [closure_eq_compl_interior_compl]

@[simp] lemma closure_compl_eq {s : set α} : closure (- s) = - interior s :=
by simp [closure_eq_compl_interior_compl]

lemma closure_compl {s : set α} : closure (-s) = - interior s :=
subset.antisymm
  (by simp [closure_subset_iff_subset_of_is_closed, compl_subset_compl, subset.refl])
  begin
    rw [compl_subset_comm, subset_interior_iff_subset_of_open, compl_subset_comm],
    exact subset_closure,
    exact is_open_compl_iff.mpr is_closed_closure
  end

lemma interior_compl {s : set α} : interior (-s) = - closure s :=
calc interior (- s) = - - interior (- s) : by simp
  ... = - closure (- (- s)) : by rw [closure_compl]
  ... = - closure s : by simp

theorem mem_closure_iff {s : set α} {a : α} : a ∈ closure s ↔ ∀ o, is_open o → a ∈ o → o ∩ s ≠ ∅ :=
⟨λ h o oo ao os,
  have s ⊆ -o, from λ x xs xo, @ne_empty_of_mem α (o∩s) x ⟨xo, xs⟩ os,
  closure_minimal this (is_closed_compl_iff.2 oo) h ao,
λ H c ⟨h₁, h₂⟩, classical.by_contradiction $ λ nc,
  let ⟨x, hc, hs⟩ := exists_mem_of_ne_empty (H _ h₁ nc) in hc (h₂ hs)⟩

lemma dense_iff_inter_open {s : set α} : closure s = univ ↔ ∀ U, is_open U → U ≠ ∅ → U ∩ s ≠ ∅ :=
begin
  split ; intro h,
  { intros U U_op U_ne,
    cases exists_mem_of_ne_empty U_ne with x x_in,
    exact  mem_closure_iff.1 (by simp[h]) U U_op x_in },
  { ext x,
    suffices : x ∈ closure s, by simp [this],
    rw mem_closure_iff,
    intros U U_op x_in,
    exact h U U_op (ne_empty_of_mem x_in) },
end

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : set α) : set α := closure s \ interior s

lemma frontier_eq_closure_inter_closure {s : set α} :
  frontier s = closure s ∩ closure (- s) :=
by rw [closure_compl, frontier, diff_eq]

@[simp] lemma frontier_compl (s : set α) : frontier (-s) = frontier s :=
by simp [frontier_eq_closure_inter_closure, inter_comm]

/-- neighbourhood filter -/
def nhds (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, principal s)

lemma tendsto_nhds {m : β → α} {f : filter β} (h : ∀s, a ∈ s → is_open s → m ⁻¹' s ∈ f.sets) :
  tendsto m f (nhds a) :=
show map m f ≤ (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, principal s),
  from le_infi $ assume s, le_infi $ assume ⟨ha, hs⟩, le_principal_iff.mpr $ h s ha hs

lemma tendsto_const_nhds {a : α} {f : filter β} : tendsto (λb:β, a) f (nhds a) :=
tendsto_nhds $ assume s ha hs, univ_mem_sets' $ assume _, ha

lemma nhds_sets {a : α} : (nhds a).sets = {s | ∃t⊆s, is_open t ∧ a ∈ t} :=
calc (nhds a).sets = (⋃s∈{s : set α| a ∈ s ∧ is_open s}, (principal s).sets) : infi_sets_eq'
  (assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩,
    ⟨x ∩ y, ⟨⟨hx₁, hy₁⟩, is_open_inter hx₂ hy₂⟩, by simp [ge]⟩)
  ⟨univ, by simp⟩
  ... = {s | ∃t⊆s, is_open t ∧ a ∈ t} :
    le_antisymm
      (supr_le $ assume i, supr_le $ assume ⟨hi₁, hi₂⟩ t ht, ⟨i, ht, hi₂, hi₁⟩)
      (assume t ⟨i, hi₁, hi₂, hi₃⟩, by simp; exact ⟨i, ⟨hi₃, hi₂⟩, hi₁⟩)

lemma map_nhds {a : α} {f : α → β} :
  map f (nhds a) = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, principal (image f s)) :=
calc map f (nhds a) = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, map f (principal s)) :
    map_binfi_eq
    (assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩,
      ⟨x ∩ y, ⟨⟨hx₁, hy₁⟩, is_open_inter hx₂ hy₂⟩, by simp [ge]⟩)
    ⟨univ, by simp⟩
  ... = _ : by simp

lemma mem_nhds_sets_iff {a : α} {s : set α} :
 s ∈ (nhds a).sets ↔ ∃t⊆s, is_open t ∧ a ∈ t :=
by simp [nhds_sets]

lemma mem_of_nhds {a : α} {s : set α} : s ∈ (nhds a).sets → a ∈ s :=
by simp [mem_nhds_sets_iff]; exact assume t ht _ hs, ht hs

lemma mem_nhds_sets {a : α} {s : set α} (hs : is_open s) (ha : a ∈ s) :
 s ∈ (nhds a).sets :=
by simp [nhds_sets]; exact ⟨s, subset.refl _, hs, ha⟩

lemma pure_le_nhds : pure ≤ (nhds : α → filter α) :=
assume a, le_infi $ assume s, le_infi $ assume ⟨h₁, _⟩, principal_mono.mpr $ by simp [h₁]

@[simp] lemma nhds_neq_bot {a : α} : nhds a ≠ ⊥ :=
assume : nhds a = ⊥,
have pure a = (⊥ : filter α),
  from lattice.bot_unique $ this ▸ pure_le_nhds a,
pure_neq_bot this

lemma interior_eq_nhds {s : set α} : interior s = {a | nhds a ≤ principal s} :=
set.ext $ by simp [mem_interior, nhds_sets]

lemma mem_interior_iff_mem_nhds {s : set α} {a : α} :
  a ∈ interior s ↔ s ∈ (nhds a).sets :=
by simp [interior_eq_nhds]

lemma is_open_iff_nhds {s : set α} : is_open s ↔ ∀a∈s, nhds a ≤ principal s :=
calc is_open s ↔ interior s = s : by rw [interior_eq_iff_open]
  ... ↔ s ⊆ interior s : ⟨assume h, by simp [*, subset.refl], subset.antisymm interior_subset⟩
  ... ↔ (∀a∈s, nhds a ≤ principal s) : by rw [interior_eq_nhds]; refl

lemma is_open_iff_mem_nhds {s : set α} : is_open s ↔ ∀a∈s, s ∈ (nhds a).sets :=
by simpa using @is_open_iff_nhds α _ _

lemma closure_eq_nhds {s : set α} : closure s = {a | nhds a ⊓ principal s ≠ ⊥} :=
calc closure s = - interior (- s) : closure_eq_compl_interior_compl
  ... = {a | ¬ nhds a ≤ principal (-s)} : by rw [interior_eq_nhds]; refl
  ... = {a | nhds a ⊓ principal s ≠ ⊥} : set.ext $ assume a, not_congr
    (inf_eq_bot_iff_le_compl
      (show principal s ⊔ principal (-s) = ⊤, by simp [principal_univ])
      (by simp)).symm

theorem mem_closure_iff_nhds {s : set α} {a : α} : a ∈ closure s ↔ ∀ t ∈ (nhds a).sets, t ∩ s ≠ ∅ :=
mem_closure_iff.trans
⟨λ H t ht, subset_ne_empty
  (inter_subset_inter_left _ interior_subset)
  (H _ is_open_interior (mem_interior_iff_mem_nhds.2 ht)),
 λ H o oo ao, H _ (mem_nhds_sets oo ao)⟩

lemma is_closed_iff_nhds {s : set α} : is_closed s ↔ ∀a, nhds a ⊓ principal s ≠ ⊥ → a ∈ s :=
calc is_closed s ↔ closure s = s : by rw [closure_eq_iff_is_closed]
  ... ↔ closure s ⊆ s : ⟨assume h, by simp [*, subset.refl], assume h, subset.antisymm h subset_closure⟩
  ... ↔ (∀a, nhds a ⊓ principal s ≠ ⊥ → a ∈ s) : by rw [closure_eq_nhds]; refl

lemma closure_inter_open {s t : set α} (h : is_open s) : s ∩ closure t ⊆ closure (s ∩ t) :=
assume a ⟨hs, ht⟩,
have s ∈ (nhds a).sets, from mem_nhds_sets h hs,
have nhds a ⊓ principal s = nhds a, from inf_of_le_left $ by simp [this],
have nhds a ⊓ principal (s ∩ t) ≠ ⊥,
  from calc nhds a ⊓ principal (s ∩ t) = nhds a ⊓ (principal s ⊓ principal t) : by simp
    ... = nhds a ⊓ principal t : by rw [←inf_assoc, this]
    ... ≠ ⊥ : by rw [closure_eq_nhds] at ht; assumption,
by rw [closure_eq_nhds]; assumption

lemma closure_diff {s t : set α} : closure s - closure t ⊆ closure (s - t) :=
calc closure s \ closure t = (- closure t) ∩ closure s : by simp [diff_eq, inter_comm]
  ... ⊆ closure (- closure t ∩ s) : closure_inter_open $ is_open_compl_iff.mpr $ is_closed_closure
  ... = closure (s \ closure t) : by simp [diff_eq, inter_comm]
  ... ⊆ closure (s \ t) : closure_mono $ diff_subset_diff (subset.refl s) subset_closure

lemma mem_of_closed_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  (hb : b ≠ ⊥) (hf : tendsto f b (nhds a)) (hs : is_closed s) (h : f ⁻¹' s ∈ b.sets) : a ∈ s :=
have b.map f ≤ nhds a ⊓ principal s,
  from le_trans (le_inf (le_refl _) (le_principal_iff.mpr h)) (inf_le_inf hf (le_refl _)),
is_closed_iff_nhds.mp hs a $ neq_bot_of_le_neq_bot (map_ne_bot hb) this

lemma mem_closure_of_tendsto {f : β → α} {x : filter β} {a : α} {s : set α}
  (hf : tendsto f x (nhds a)) (hs : is_closed s) (h : x ⊓ principal (f ⁻¹' s) ≠ ⊥) : a ∈ s :=
is_closed_iff_nhds.mp hs _ $ neq_bot_of_le_neq_bot (@map_ne_bot _ _ _ f h) $
  le_inf (le_trans (map_mono $ inf_le_left) hf) $
    le_trans (map_mono $ inf_le_right_of_le $ by simp; exact subset.refl _) (@map_comap_le _ _ _ f)

/- locally finite family [General Topology (Bourbaki, 1995)] -/
section locally_finite

/-- A family of sets in `set α` is locally finite if at every point `x:α`,
  there is a neighborhood of `x` which meets only finitely many sets in the family -/
def locally_finite (f : β → set α) :=
∀x:α, ∃t∈(nhds x).sets, finite {i | f i ∩ t ≠ ∅ }

lemma locally_finite_of_finite {f : β → set α} (h : finite (univ : set β)) : locally_finite f :=
assume x, ⟨univ, univ_mem_sets, finite_subset h $ by simp⟩

lemma locally_finite_subset
  {f₁ f₂ : β → set α} (hf₂ : locally_finite f₂) (hf : ∀b, f₁ b ⊆ f₂ b) : locally_finite f₁ :=
assume a,
let ⟨t, ht₁, ht₂⟩ := hf₂ a in
⟨t, ht₁, finite_subset ht₂ $ assume i hi,
  neq_bot_of_le_neq_bot hi $ inter_subset_inter (hf i) $ subset.refl _⟩

lemma is_closed_Union_of_locally_finite {f : β → set α}
  (h₁ : locally_finite f) (h₂ : ∀i, is_closed (f i)) : is_closed (⋃i, f i) :=
is_open_iff_nhds.mpr $ assume a, assume h : a ∉ (⋃i, f i),
  have ∀i, a ∈ -f i,
    from assume i hi, by simp at h; exact h i hi,
  have ∀i, - f i ∈ (nhds a).sets,
    by rw [nhds_sets]; exact assume i, ⟨- f i, subset.refl _, h₂ i, this i⟩,
  let ⟨t, h_sets, (h_fin : finite {i | f i ∩ t ≠ ∅ })⟩ := h₁ a in

  calc nhds a ≤ principal (t ∩ (⋂ i∈{i | f i ∩ t ≠ ∅ }, - f i)) :
  begin
    rw [le_principal_iff],
    apply @filter.inter_mem_sets _ (nhds a) _ _ h_sets,
    apply @filter.Inter_mem_sets _ (nhds a) _ _ _ h_fin,
    exact assume i h, this i
  end
  ... ≤ principal (- ⋃i, f i) :
  begin
    simp only [principal_mono, subset_def, mem_compl_eq, mem_inter_eq,
      mem_Inter, mem_set_of_eq, mem_Union, and_imp, not_exists,
      not_eq_empty_iff_exists, exists_imp_distrib, (≠)],
    exact assume x xt ht i xfi, ht i x xfi xt xfi
  end

end locally_finite

/- compact sets -/
section compact

/-- A set `s` is compact if for every filter `f` that contains `s`,
    every set of `f` also meets every neighborhood of some `a ∈ s`. -/
def compact (s : set α) := ∀f, f ≠ ⊥ → f ≤ principal s → ∃a∈s, f ⊓ nhds a ≠ ⊥

lemma compact_inter {s t : set α} (hs : compact s) (ht : is_closed t) : compact (s ∩ t) :=
assume f hnf hstf,
let ⟨a, hsa, (ha : f ⊓ nhds a ≠ ⊥)⟩ := hs f hnf (le_trans hstf (by simp)) in
have ∀a, principal t ⊓ nhds a ≠ ⊥ → a ∈ t,
  by intro a; rw [inf_comm]; rw [is_closed_iff_nhds] at ht; exact ht a,
have a ∈ t,
  from this a $ neq_bot_of_le_neq_bot ha $ inf_le_inf (le_trans hstf (by simp)) (le_refl _),
⟨a, ⟨hsa, this⟩, ha⟩

lemma compact_diff {s t : set α} (hs : compact s) (ht : is_open t) : compact (s \ t) :=
compact_inter hs (is_closed_compl_iff.mpr ht)

lemma compact_of_is_closed_subset {s t : set α}
  (hs : compact s) (ht : is_closed t) (h : t ⊆ s) : compact t :=
by convert ← compact_inter hs ht; exact inter_eq_self_of_subset_right h

lemma compact_adherence_nhdset {s t : set α} {f : filter α}
  (hs : compact s) (hf₂ : f ≤ principal s) (ht₁ : is_open t) (ht₂ : ∀a∈s, nhds a ⊓ f ≠ ⊥ → a ∈ t) :
  t ∈ f.sets :=
classical.by_cases mem_sets_of_neq_bot $
  assume : f ⊓ principal (- t) ≠ ⊥,
  let ⟨a, ha, (hfa : f ⊓ principal (-t) ⊓ nhds a ≠ ⊥)⟩ := hs _ this $ inf_le_left_of_le hf₂ in
  have a ∈ t,
    from ht₂ a ha $ neq_bot_of_le_neq_bot hfa $ le_inf inf_le_right $ inf_le_left_of_le inf_le_left,
  have nhds a ⊓ principal (-t) ≠ ⊥,
    from neq_bot_of_le_neq_bot hfa $ le_inf inf_le_right $ inf_le_left_of_le inf_le_right,
  have ∀s∈(nhds a ⊓ principal (-t)).sets, s ≠ ∅,
    from forall_sets_neq_empty_iff_neq_bot.mpr this,
  have false,
    from this _ ⟨t, mem_nhds_sets ht₁ ‹a ∈ t›, -t, subset.refl _, subset.refl _⟩ (by simp),
  by contradiction

lemma compact_iff_ultrafilter_le_nhds {s : set α} :
  compact s ↔ (∀f, ultrafilter f → f ≤ principal s → ∃a∈s, f ≤ nhds a) :=
⟨assume hs : compact s, assume f hf hfs,
  let ⟨a, ha, h⟩ := hs _ hf.left hfs in
  ⟨a, ha, le_of_ultrafilter hf h⟩,

  assume hs : (∀f, ultrafilter f → f ≤ principal s → ∃a∈s, f ≤ nhds a),
  assume f hf hfs,
  let ⟨a, ha, (h : ultrafilter_of f ≤ nhds a)⟩ :=
    hs (ultrafilter_of f) (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hfs) in
  have ultrafilter_of f ⊓ nhds a ≠ ⊥,
    by simp [inf_of_le_left, h]; exact (ultrafilter_ultrafilter_of hf).left,
  ⟨a, ha, neq_bot_of_le_neq_bot this (inf_le_inf ultrafilter_of_le (le_refl _))⟩⟩

lemma compact_elim_finite_subcover {s : set α} {c : set (set α)}
  (hs : compact s) (hc₁ : ∀t∈c, is_open t) (hc₂ : s ⊆ ⋃₀ c) : ∃c'⊆c, finite c' ∧ s ⊆ ⋃₀ c' :=
classical.by_contradiction $ assume h,
  have h : ∀{c'}, c' ⊆ c → finite c' → ¬ s ⊆ ⋃₀ c',
    from assume c' h₁ h₂ h₃, h ⟨c', h₁, h₂, h₃⟩,
  let
    f : filter α := (⨅c':{c' : set (set α) // c' ⊆ c ∧ finite c'}, principal (s - ⋃₀ c')),
    ⟨a, ha⟩ := @exists_mem_of_ne_empty α s
      (assume h', h (empty_subset _) finite_empty $ h'.symm ▸ empty_subset _)
  in
  have f ≠ ⊥, from infi_neq_bot_of_directed ⟨a⟩
    (assume ⟨c₁, hc₁, hc'₁⟩ ⟨c₂, hc₂, hc'₂⟩, ⟨⟨c₁ ∪ c₂, union_subset hc₁ hc₂, finite_union hc'₁ hc'₂⟩,
      principal_mono.mpr $ diff_subset_diff_right $ sUnion_mono $ subset_union_left _ _,
      principal_mono.mpr $ diff_subset_diff_right $ sUnion_mono $ subset_union_right _ _⟩)
    (assume ⟨c', hc'₁, hc'₂⟩, show principal (s \ _) ≠ ⊥, by simp [diff_eq_empty]; exact h hc'₁ hc'₂),
  have f ≤ principal s, from infi_le_of_le ⟨∅, empty_subset _, finite_empty⟩ $
    show principal (s \ ⋃₀∅) ≤ principal s, by simp; exact subset.refl s,
  let
    ⟨a, ha, (h : f ⊓ nhds a ≠ ⊥)⟩ := hs f ‹f ≠ ⊥› this,
    ⟨t, ht₁, (ht₂ : a ∈ t)⟩ := hc₂ ha
  in
  have f ≤ principal (-t),
    from infi_le_of_le ⟨{t}, by simp [ht₁], finite_insert _ finite_empty⟩ $
      principal_mono.mpr $
        show s - ⋃₀{t} ⊆ - t, begin simp; exact assume x ⟨_, hnt⟩, hnt end,
  have is_closed (- t), from is_open_compl_iff.mp $ by simp; exact hc₁ t ht₁,
  have a ∈ - t, from is_closed_iff_nhds.mp this _ $ neq_bot_of_le_neq_bot h $
    le_inf inf_le_right (inf_le_left_of_le ‹f ≤ principal (- t)›),
  this ‹a ∈ t›

lemma compact_elim_finite_subcover_image {s : set α} {b : set β} {c : β → set α}
  (hs : compact s) (hc₁ : ∀i∈b, is_open (c i)) (hc₂ : s ⊆ ⋃i∈b, c i) :
  ∃b'⊆b, finite b' ∧ s ⊆ ⋃i∈b', c i :=
if h : b = ∅ then ⟨∅, by simp, by simp, h ▸ hc₂⟩ else
let ⟨i, hi⟩ := exists_mem_of_ne_empty h in
have hc'₁ : ∀i∈c '' b, is_open i, from assume i ⟨j, hj, h⟩, h ▸ hc₁ _ hj,
have hc'₂ : s ⊆ ⋃₀ (c '' b), by simpa,
let ⟨d, hd₁, hd₂, hd₃⟩ := compact_elim_finite_subcover hs hc'₁ hc'₂ in
have ∀x : d, ∃i, i ∈ b ∧ c i = x, from assume ⟨x, hx⟩, hd₁ hx,
let ⟨f', hf⟩ := axiom_of_choice this,
    f := λx:set α, (if h : x ∈ d then f' ⟨x, h⟩ else i : β) in
have ∀(x : α) (i : set α), i ∈ d → x ∈ i → (∃ (i : β), i ∈ f '' d ∧ x ∈ c i),
  from assume x i hid hxi, ⟨f i, mem_image_of_mem f hid,
    by simpa [f, hid, (hf ⟨_, hid⟩).2] using hxi⟩,
⟨f '' d,
  assume i ⟨j, hj, h⟩,
  h ▸ by simpa [f, hj] using (hf ⟨_, hj⟩).1,
  finite_image f hd₂,
  subset.trans hd₃ $ by simpa [subset_def]⟩

lemma compact_of_finite_subcover {s : set α}
  (h : ∀c, (∀t∈c, is_open t) → s ⊆ ⋃₀ c → ∃c'⊆c, finite c' ∧ s ⊆ ⋃₀ c') : compact s :=
assume f hfn hfs, classical.by_contradiction $ assume : ¬ (∃x∈s, f ⊓ nhds x ≠ ⊥),
  have hf : ∀x∈s, nhds x ⊓ f = ⊥,
    by simpa [not_and, inf_comm],
  have ¬ ∃x∈s, ∀t∈f.sets, x ∈ closure t,
    from assume ⟨x, hxs, hx⟩,
    have ∅ ∈ (nhds x ⊓ f).sets, by rw [empty_in_sets_eq_bot, hf x hxs],
    let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := by rw [mem_inf_sets] at this; exact this in
    have ∅ ∈ (nhds x ⊓ principal t₂).sets,
      from (nhds x ⊓ principal t₂).sets_of_superset (inter_mem_inf_sets ht₁ (subset.refl t₂)) ht,
    have nhds x ⊓ principal t₂ = ⊥,
      by rwa [empty_in_sets_eq_bot] at this,
    by simp [closure_eq_nhds] at hx; exact hx t₂ ht₂ this,
  have ∀x∈s, ∃t∈f.sets, x ∉ closure t, by simpa [_root_.not_forall],
  let c := (λt, - closure t) '' f.sets, ⟨c', hcc', hcf, hsc'⟩ := h c
    (assume t ⟨s, hs, h⟩, h ▸ is_closed_closure) (by simpa [subset_def]) in
  let ⟨b, hb⟩ := axiom_of_choice $
    show ∀s:c', ∃t, t ∈ f.sets ∧ - closure t = s,
      from assume ⟨x, hx⟩, hcc' hx in
  have (⋂s∈c', if h : s ∈ c' then b ⟨s, h⟩ else univ) ∈ f.sets,
    from Inter_mem_sets hcf $ assume t ht, by rw [dif_pos ht]; exact (hb ⟨t, ht⟩).left,
  have s ∩ (⋂s∈c', if h : s ∈ c' then b ⟨s, h⟩ else univ) ∈ f.sets,
    from inter_mem_sets (by simp at hfs; assumption) this,
  have ∅ ∈ f.sets,
    from mem_sets_of_superset this $ assume x ⟨hxs, hxi⟩,
    let ⟨t, htc', hxt⟩ := (show ∃t ∈ c', x ∈ t, by simpa using hsc' hxs) in
    have -closure (b ⟨t, htc'⟩) = t, from (hb _).right,
    have x ∈ - t,
      from this ▸ (calc x ∈ b ⟨t, htc'⟩ : by simp at hxi; have h := hxi t htc'; rwa [dif_pos htc'] at h
        ... ⊆ closure (b ⟨t, htc'⟩) : subset_closure
        ... ⊆ - - closure (b ⟨t, htc'⟩) : by simp; exact subset.refl _),
    show false, from this hxt,
  hfn $ by rwa [empty_in_sets_eq_bot] at this

lemma compact_iff_finite_subcover {s : set α} :
  compact s ↔ (∀c, (∀t∈c, is_open t) → s ⊆ ⋃₀ c → ∃c'⊆c, finite c' ∧ s ⊆ ⋃₀ c') :=
⟨assume hc c, compact_elim_finite_subcover hc, compact_of_finite_subcover⟩

lemma compact_empty : compact (∅ : set α) :=
assume f hnf hsf, not.elim hnf $
by simpa [empty_in_sets_eq_bot] using hsf

lemma compact_singleton {a : α} : compact ({a} : set α) :=
compact_of_finite_subcover $ assume c hc₁ hc₂,
  let ⟨i, hic, hai⟩ := (show ∃i ∈ c, a ∈ i, by simpa using hc₂) in
  ⟨{i}, by simp [hic], finite_singleton _, by simp [hai]⟩

lemma compact_bUnion_of_compact {s : set β} {f : β → set α} (hs : finite s) :
  (∀i ∈ s, compact (f i)) → compact (⋃i ∈ s, f i) :=
assume hf, compact_of_finite_subcover $ assume c c_open c_cover,
  have ∀i : subtype s, ∃c' ⊆ c, finite c' ∧ f i ⊆ ⋃₀ c', from
    assume ⟨i, hi⟩, compact_elim_finite_subcover (hf i hi) c_open
      (calc f i ⊆ ⋃i ∈ s, f i : subset_bUnion_of_mem hi
            ... ⊆ ⋃₀ c        : c_cover),
  let ⟨finite_subcovers, h⟩ := axiom_of_choice this in
  let c' := ⋃i, finite_subcovers i in
  have c' ⊆ c, from Union_subset (λi, (h i).fst),
  have finite c', from @finite_Union _ _ hs.fintype _ (λi, (h i).snd.1),
  have (⋃i ∈ s, f i) ⊆ ⋃₀ c', from bUnion_subset $ λi hi, calc
    f i ⊆ ⋃₀ finite_subcovers ⟨i,hi⟩ : (h ⟨i,hi⟩).snd.2
    ... ⊆ ⋃₀ c'                      : sUnion_mono (subset_Union _ _),
  ⟨c', ‹c' ⊆ c›, ‹finite c'›, this⟩

lemma compact_of_finite {s : set α} (hs : finite s) : compact s :=
let s' : set α := ⋃i ∈ s, {i} in
have e : s' = s, from ext $ λi, by simp,
have compact s', from compact_bUnion_of_compact hs (λ_ _, compact_singleton),
e ▸ this

end compact

/- separation axioms -/

section separation

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where for every pair `x ≠ y`, there is an open set containing `x` and not `y`.
  Equivalently, every singleton set is closed. -/
class t1_space (α : Type u) [topological_space α] :=
(t1 : ∀x, is_closed ({x} : set α))

lemma is_closed_singleton [t1_space α] {x : α} : is_closed ({x} : set α) :=
t1_space.t1 x

lemma compl_singleton_mem_nhds [t1_space α] {x y : α} (h : y ≠ x) : - {x} ∈ (nhds y).sets :=
mem_nhds_sets is_closed_singleton $ by simp; exact h

@[simp] lemma closure_singleton [topological_space α] [t1_space α] {a : α} :
  closure ({a} : set α) = {a} :=
closure_eq_of_is_closed is_closed_singleton

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
class t2_space (α : Type u) [topological_space α] :=
(t2 : ∀x y, x ≠ y → ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅)

lemma t2_separation [t2_space α] {x y : α} (h : x ≠ y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
t2_space.t2 x y h

instance t2_space.t1_space [topological_space α] [t2_space α] : t1_space α :=
⟨assume x,
  have ∀y, y ≠ x ↔ ∃ (i : set α), (x ∉ i ∧ is_open i) ∧ y ∈ i,
    from assume y, ⟨assume h',
      let ⟨u, v, hu, hv, hy, hx, h⟩ := t2_separation h' in
      have x ∉ u,
        from assume : x ∈ u,
        have x ∈ u ∩ v, from ⟨this, hx⟩,
        by rwa [h] at this,
      ⟨u, ⟨this, hu⟩, hy⟩,
      assume ⟨s, ⟨hx, hs⟩, hy⟩ h, hx $ h ▸ hy⟩,
  have (-{x} : set α) = (⋃s∈{s : set α | x ∉ s ∧ is_open s}, s),
    by apply set.ext; simpa,
  show is_open (- {x}),
    by rw [this]; exact (is_open_Union $ assume s, is_open_Union $ assume ⟨_, hs⟩, hs)⟩

lemma eq_of_nhds_neq_bot [ht : t2_space α] {x y : α} (h : nhds x ⊓ nhds y ≠ ⊥) : x = y :=
classical.by_contradiction $ assume : x ≠ y,
let ⟨u, v, hu, hv, hx, hy, huv⟩ := t2_space.t2 x y this in
have u ∩ v ∈ (nhds x ⊓ nhds y).sets,
  from inter_mem_inf_sets (mem_nhds_sets hu hx) (mem_nhds_sets hv hy),
h $ empty_in_sets_eq_bot.mp $ huv ▸ this

@[simp] lemma nhds_eq_nhds_iff {a b : α} [t2_space α] : nhds a = nhds b ↔ a = b :=
⟨assume h, eq_of_nhds_neq_bot $ by simp [h], assume h, h ▸ rfl⟩

@[simp] lemma nhds_le_nhds_iff {a b : α} [t2_space α] : nhds a ≤ nhds b ↔ a = b :=
⟨assume h, eq_of_nhds_neq_bot $ by simp [inf_of_le_left h], assume h, h ▸ le_refl _⟩

lemma tendsto_nhds_unique [t2_space α] {f : β → α} {l : filter β} {a b : α}
  (hl : l ≠ ⊥) (ha : tendsto f l (nhds a)) (hb : tendsto f l (nhds b)) : a = b :=
eq_of_nhds_neq_bot $ neq_bot_of_le_neq_bot (map_ne_bot hl) $ le_inf ha hb

end separation

section regularity

/-- A T₃ space, also known as a regular space (although this condition sometimes
  omits T₂), is one in which for every closed `C` and `x ∉ C`, there exist
  disjoint open sets containing `x` and `C` respectively. -/
class regular_space (α : Type u) [topological_space α] extends t2_space α :=
(regular : ∀{s:set α} {a}, is_closed s → a ∉ s → ∃t, is_open t ∧ s ⊆ t ∧ nhds a ⊓ principal t = ⊥)

lemma nhds_is_closed [regular_space α] {a : α} {s : set α} (h : s ∈ (nhds a).sets) :
  ∃t∈(nhds a).sets, t ⊆ s ∧ is_closed t :=
let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_sets_iff.mp h in
have ∃t, is_open t ∧ -s' ⊆ t ∧ nhds a ⊓ principal t = ⊥,
  from regular_space.regular (is_closed_compl_iff.mpr h₂) (not_not_intro h₃),
let ⟨t, ht₁, ht₂, ht₃⟩ := this in
⟨-t,
  mem_sets_of_neq_bot $ by simp; exact ht₃,
  subset.trans (compl_subset_comm.1 ht₂) h₁,
  is_closed_compl_iff.mpr ht₁⟩

end regularity

/- generating sets -/

end topological_space

namespace topological_space
variables {α : Type u}

/-- The least topology containing a collection of basic sets. -/
inductive generate_open (g : set (set α)) : set α → Prop
| basic  : ∀s∈g, generate_open s
| univ   : generate_open univ
| inter  : ∀s t, generate_open s → generate_open t → generate_open (s ∩ t)
| sUnion : ∀k, (∀s∈k, generate_open s) → generate_open (⋃₀ k)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from (g : set (set α)) : topological_space α :=
{ is_open        := generate_open g,
  is_open_univ   := generate_open.univ g,
  is_open_inter  := generate_open.inter,
  is_open_sUnion := generate_open.sUnion  }

lemma nhds_generate_from {g : set (set α)} {a : α} :
  @nhds α (generate_from g) a = (⨅s∈{s | a ∈ s ∧ s ∈ g}, principal s) :=
le_antisymm
  (infi_le_infi $ assume s, infi_le_infi_const $ assume ⟨as, sg⟩, ⟨as, generate_open.basic _ sg⟩)
  (le_infi $ assume s, le_infi $ assume ⟨as, hs⟩,
    have ∀s, generate_open g s → a ∈ s → (⨅s∈{s | a ∈ s ∧ s ∈ g}, principal s) ≤ principal s,
    begin
      intros s hs,
      induction hs,
      case generate_open.basic : s hs
      { exact assume as, infi_le_of_le s $ infi_le _ ⟨as, hs⟩ },
      case generate_open.univ
      { rw [principal_univ],
        exact assume _, le_top },
      case generate_open.inter : s t hs' ht' hs ht
      { exact assume ⟨has, hat⟩, calc _ ≤ principal s ⊓ principal t : le_inf (hs has) (ht hat)
          ... = _ : by simp },
      case generate_open.sUnion : k hk' hk
      { exact λ ⟨t, htk, hat⟩, calc _ ≤ principal t : hk t htk hat
          ... ≤ _ : begin simp; exact subset_sUnion_of_mem htk end }
    end,
    this s hs as)

lemma tendsto_nhds_generate_from {β : Type*} {m : α → β} {f : filter α} {g : set (set β)} {b : β}
  (h : ∀s∈g, b ∈ s → m ⁻¹' s ∈ f.sets) : tendsto m f (@nhds β (generate_from g) b) :=
by rw [nhds_generate_from]; exact
  (tendsto_infi.2 $ assume s, tendsto_infi.2 $ assume ⟨hbs, hsg⟩, tendsto_principal.2 $ h s hsg hbs)

protected def mk_of_nhds (n : α → filter α) : topological_space α :=
{ is_open        := λs, ∀a∈s, s ∈ (n a).sets,
  is_open_univ   := assume x h, univ_mem_sets,
  is_open_inter  := assume s t hs ht x ⟨hxs, hxt⟩, inter_mem_sets (hs x hxs) (ht x hxt),
  is_open_sUnion := assume s hs a ⟨x, hx, hxa⟩, mem_sets_of_superset (hs x hx _ hxa) (set.subset_sUnion_of_mem hx) }

lemma nhds_mk_of_nhds (n : α → filter α) (a : α)
  (h₀ : pure ≤ n) (h₁ : ∀{a s}, s ∈ (n a).sets → ∃t∈(n a).sets, t ⊆ s ∧ ∀a'∈t, s ∈ (n a').sets) :
  @nhds α (topological_space.mk_of_nhds n) a = n a :=
begin
  letI := topological_space.mk_of_nhds n,
  refine le_antisymm (assume s hs, _) (assume s hs, _),
  { have h₀ : {b | s ∈ (n b).sets} ⊆ s := assume b hb, mem_pure_sets.1 $ h₀ b hb,
    have h₁ : {b | s ∈ (n b).sets} ∈ (nhds a).sets,
    { refine mem_nhds_sets (assume b (hb : s ∈ (n b).sets), _) hs,
      rcases h₁ hb with ⟨t, ht, hts, h⟩,
      exact mem_sets_of_superset ht h },
    exact mem_sets_of_superset h₁ h₀ },
  { rcases (@mem_nhds_sets_iff α (topological_space.mk_of_nhds n) _ _).1 hs with ⟨t, hts, ht, hat⟩,
    exact (n a).sets_of_superset (ht _ hat) hts },
end

end topological_space

section lattice

variables {α : Type u} {β : Type v}

instance : partial_order (topological_space α) :=
{ le          := λt s, t.is_open ≤ s.is_open,
  le_antisymm := assume t s h₁ h₂, topological_space_eq $ le_antisymm h₁ h₂,
  le_refl     := assume t, le_refl t.is_open,
  le_trans    := assume a b c h₁ h₂, @le_trans _ _ a.is_open b.is_open c.is_open h₁ h₂ }

lemma generate_from_le_iff_subset_is_open {g : set (set α)} {t : topological_space α} :
  topological_space.generate_from g ≤ t ↔ g ⊆ {s | t.is_open s} :=
iff.intro
  (assume ht s hs, ht _ $ topological_space.generate_open.basic s hs)
  (assume hg s hs, hs.rec_on (assume v hv, hg hv)
    t.is_open_univ (assume u v _ _, t.is_open_inter u v) (assume k _, t.is_open_sUnion k))

protected def mk_of_closure (s : set (set α))
  (hs : {u | (topological_space.generate_from s).is_open u} = s) : topological_space α :=
{ is_open        := λu, u ∈ s,
  is_open_univ   := hs ▸ topological_space.generate_open.univ _,
  is_open_inter  := hs ▸ topological_space.generate_open.inter,
  is_open_sUnion := hs ▸ topological_space.generate_open.sUnion }

lemma mk_of_closure_sets {s : set (set α)}
  {hs : {u | (topological_space.generate_from s).is_open u} = s} :
  mk_of_closure s hs = topological_space.generate_from s :=
topological_space_eq hs.symm

def gi_generate_from (α : Type*) :
  galois_insertion topological_space.generate_from (λt:topological_space α, {s | t.is_open s}) :=
{ gc        := assume g t, generate_from_le_iff_subset_is_open,
  le_l_u    := assume ts s hs, topological_space.generate_open.basic s hs,
  choice    := λg hg, mk_of_closure g
    (subset.antisymm hg $ generate_from_le_iff_subset_is_open.1 $ le_refl _),
  choice_eq := assume s hs, mk_of_closure_sets }

lemma generate_from_mono {α} {g₁ g₂ : set (set α)} (h : g₁ ⊆ g₂) :
  topological_space.generate_from g₁ ≤ topological_space.generate_from g₂ :=
(gi_generate_from _).gc.monotone_l h

instance {α : Type u} : complete_lattice (topological_space α) :=
(gi_generate_from α).lift_complete_lattice

@[simp] lemma is_open_top {s : set α} : @is_open α ⊤ s := trivial

lemma le_of_nhds_le_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₂ x ≤ @nhds α t₁ x) :
  t₁ ≤ t₂ :=
assume s, show @is_open α t₁ s → @is_open α t₂ s,
  begin simp [is_open_iff_nhds]; exact assume hs a ha, h _ $ hs _ ha end

lemma eq_of_nhds_eq_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₂ x = @nhds α t₁ x) :
  t₁ = t₂ :=
le_antisymm
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ h x)
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ (h x).symm)

end lattice

section galois_connection
variables {α : Type*} {β : Type*} {γ : Type*}

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def topological_space.induced {α : Type u} {β : Type v} (f : α → β) (t : topological_space β) :
  topological_space α :=
{ is_open        := λs, ∃s', t.is_open s' ∧ s = f ⁻¹' s',
  is_open_univ   := ⟨univ, by simp; exact t.is_open_univ⟩,
  is_open_inter  := assume s₁ s₂ ⟨s'₁, hs₁, eq₁⟩ ⟨s'₂, hs₂, eq₂⟩,
    ⟨s'₁ ∩ s'₂, by simp [eq₁, eq₂]; exact t.is_open_inter _ _ hs₁ hs₂⟩,
  is_open_sUnion := assume s h,
  begin
    simp [classical.skolem] at h,
    cases h with f hf,
    apply exists.intro (⋃(x : set α) (h : x ∈ s), f x h),
    simp [sUnion_eq_bUnion, (λx h, (hf x h).right.symm)],
    exact (@is_open_Union β _ t _ $ assume i,
      show is_open (⋃h, f i h), from @is_open_Union β _ t _ $ assume h, (hf i h).left)
  end }

lemma is_closed_induced_iff [t : topological_space β] {s : set α} {f : α → β} :
  @is_closed α (t.induced f) s ↔ (∃t, is_closed t ∧ s = f ⁻¹' t) :=
⟨assume ⟨t, ht, heq⟩, ⟨-t, by simp; assumption, by simp [preimage_compl, heq.symm]⟩,
  assume ⟨t, ht, heq⟩, ⟨-t, ht, by simp [preimage_compl, heq.symm]⟩⟩

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def topological_space.coinduced {α : Type u} {β : Type v} (f : α → β) (t : topological_space α) :
  topological_space β :=
{ is_open        := λs, t.is_open (f ⁻¹' s),
  is_open_univ   := by simp; exact t.is_open_univ,
  is_open_inter  := assume s₁ s₂ h₁ h₂, by simp; exact t.is_open_inter _ _ h₁ h₂,
  is_open_sUnion := assume s h, by rw [preimage_sUnion]; exact (@is_open_Union _ _ t _ $ assume i,
    show is_open (⋃ (H : i ∈ s), f ⁻¹' i), from
      @is_open_Union _ _ t _ $ assume hi, h i hi) }

variables {t t₁ t₂ : topological_space α} {t' : topological_space β} {f : α → β} {g : β → α}

lemma induced_le_iff_le_coinduced {f : α → β } {tα : topological_space α} {tβ : topological_space β} :
  tβ.induced f ≤ tα ↔ tβ ≤ tα.coinduced f :=
iff.intro
  (assume h s hs, show tα.is_open (f ⁻¹' s), from h _ ⟨s, hs, rfl⟩)
  (assume h s ⟨t, ht, hst⟩, hst.symm ▸ h _ ht)

lemma gc_induced_coinduced (f : α → β) :
  galois_connection (topological_space.induced f) (topological_space.coinduced f) :=
assume f g, induced_le_iff_le_coinduced

lemma induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
(gc_induced_coinduced g).monotone_l h

lemma coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
(gc_induced_coinduced f).monotone_u h

@[simp] lemma induced_bot : (⊥ : topological_space α).induced g = ⊥ :=
(gc_induced_coinduced g).l_bot

@[simp] lemma induced_sup : (t₁ ⊔ t₂).induced g = t₁.induced g ⊔ t₂.induced g :=
(gc_induced_coinduced g).l_sup

@[simp] lemma induced_supr {ι : Sort w} {t : ι → topological_space α} :
  (⨆i, t i).induced g = (⨆i, (t i).induced g) :=
(gc_induced_coinduced g).l_supr

@[simp] lemma coinduced_top : (⊤ : topological_space α).coinduced f = ⊤ :=
(gc_induced_coinduced f).u_top

@[simp] lemma coinduced_inf : (t₁ ⊓ t₂).coinduced f = t₁.coinduced f ⊓ t₂.coinduced f :=
(gc_induced_coinduced f).u_inf

@[simp] lemma coinduced_infi {ι : Sort w} {t : ι → topological_space α} :
  (⨅i, t i).coinduced f = (⨅i, (t i).coinduced f) :=
(gc_induced_coinduced f).u_infi

lemma induced_id [t : topological_space α] : t.induced id = t :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', hs, h⟩, h.symm ▸ hs, assume hs, ⟨s, hs, rfl⟩⟩

lemma induced_compose [tβ : topological_space β] [tγ : topological_space γ]
  {f : α → β} {g : β → γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', ⟨s, hs, h₂⟩, h₁⟩, h₁.symm ▸ h₂.symm ▸ ⟨s, hs, rfl⟩,
    assume ⟨s, hs, h⟩, ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

lemma coinduced_id [t : topological_space α] : t.coinduced id = t :=
topological_space_eq rfl

lemma coinduced_compose [tα : topological_space α]
  {f : α → β} {g : β → γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
topological_space_eq rfl

end galois_connection

/- constructions using the complete lattice structure -/
section constructions
open topological_space

variables {α : Type u} {β : Type v}

instance inhabited_topological_space {α : Type u} : inhabited (topological_space α) :=
⟨⊤⟩

lemma t2_space_top : @t2_space α ⊤ :=
{ t2 := assume x y hxy, ⟨{x}, {y}, trivial, trivial, mem_insert _ _, mem_insert _ _,
  eq_empty_iff_forall_not_mem.2 $ by intros z hz; simp at hz; cc⟩ }

instance : topological_space empty := ⊤
instance : topological_space unit := ⊤
instance : topological_space bool := ⊤
instance : topological_space ℕ := ⊤
instance : topological_space ℤ := ⊤

instance sierpinski_space : topological_space Prop :=
generate_from {{true}}

instance {p : α → Prop} [t : topological_space α] : topological_space (subtype p) :=
induced subtype.val t

instance {r : α → α → Prop} [t : topological_space α] : topological_space (quot r) :=
coinduced (quot.mk r) t

instance {s : setoid α} [t : topological_space α] : topological_space (quotient s) :=
coinduced quotient.mk t

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α × β) :=
induced prod.fst t₁ ⊔ induced prod.snd t₂

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α ⊕ β) :=
coinduced sum.inl t₁ ⊓ coinduced sum.inr t₂

instance {β : α → Type v} [t₂ : Πa, topological_space (β a)] : topological_space (sigma β) :=
⨅a, coinduced (sigma.mk a) (t₂ a)

instance Pi.topological_space {β : α → Type v} [t₂ : Πa, topological_space (β a)] : topological_space (Πa, β a) :=
⨆a, induced (λf, f a) (t₂ a)

instance [topological_space α] : topological_space (list α) :=
topological_space.mk_of_nhds (traverse nhds)

lemma nhds_list [topological_space α] (as : list α) : nhds as = traverse nhds as :=
begin
  refine nhds_mk_of_nhds _ _ _ _,
  { assume l, induction l,
    case list.nil { exact le_refl _ },
    case list.cons : a l ih {
      suffices : list.cons <$> pure a <*> pure l ≤ list.cons <$> nhds a <*> traverse nhds l,
      { simpa [-filter.pure_def] with functor_norm using this },
      exact filter.seq_mono (filter.map_mono $ pure_le_nhds a) ih } },
  { assume l s hs,
    rcases (mem_traverse_sets_iff _ _).1 hs with ⟨u, hu, hus⟩, clear as hs,
    have : ∃v:list (set α), l.forall₂ (λa s, is_open s ∧ a ∈ s) v ∧ sequence v ⊆ s,
    { induction hu generalizing s,
      case list.forall₂.nil : hs this { existsi [], simpa },
      case list.forall₂.cons : a s as ss ht h ih t hts {
        rcases mem_nhds_sets_iff.1 ht with ⟨u, hut, hu⟩,
        rcases ih (subset.refl _) with ⟨v, hv, hvss⟩,
        exact ⟨u::v, list.forall₂.cons hu hv,
          subset.trans (set.seq_mono (set.image_subset _ hut) hvss) hts⟩ } },
    rcases this with ⟨v, hv, hvs⟩,
    refine ⟨sequence v, mem_traverse_sets _ _ _, hvs, _⟩,
    { exact hv.imp (assume a s ⟨hs, ha⟩, mem_nhds_sets hs ha) },
    { assume u hu,
      have hu := (list.mem_traverse _ _).1 hu,
      have : list.forall₂ (λa s, is_open s ∧ a ∈ s) u v,
      { refine list.forall₂.flip _,
        replace hv := hv.flip,
        simp [list.forall₂_and_left, flip] at ⊢ hv,
        exact ⟨hv.1, hu.flip⟩ },
      refine mem_sets_of_superset _ hvs,
      exact mem_traverse_sets _ _ (this.imp $ assume a s ⟨hs, ha⟩, mem_nhds_sets hs ha) } }
end

lemma quotient_dense_of_dense [setoid α] [topological_space α] {s : set α} (H : ∀ x, x ∈ closure s) :
  closure (quotient.mk '' s) = univ :=
begin
  ext x,
  suffices : x ∈ closure (quotient.mk '' s), by simp [this],
  rw mem_closure_iff,
  intros U U_op x_in_U,
  let V := quotient.mk ⁻¹' U,
  cases quotient.exists_rep x with y y_x,
  have y_in_V : y ∈ V, by simp [mem_preimage_eq, y_x, x_in_U],
  have V_op : is_open V := U_op,
  have : V ∩ s ≠ ∅ := mem_closure_iff.1 (H y) V V_op y_in_V,
  rcases exists_mem_of_ne_empty this with ⟨w, w_in_V, w_in_range⟩,
  exact ne_empty_of_mem ⟨by tauto, mem_image_of_mem quotient.mk w_in_range⟩
end

lemma generate_from_le {t : topological_space α} { g : set (set α) } (h : ∀s∈g, is_open s) :
  generate_from g ≤ t :=
generate_from_le_iff_subset_is_open.2 h

protected def topological_space.nhds_adjoint (a : α) (f : filter α) : topological_space α :=
{ is_open        := λs, a ∈ s → s ∈ f.sets,
  is_open_univ   := assume s, univ_mem_sets,
  is_open_inter  := assume s t hs ht ⟨has, hat⟩, inter_mem_sets (hs has) (ht hat),
  is_open_sUnion := assume k hk ⟨u, hu, hau⟩, mem_sets_of_superset (hk u hu hau) (subset_sUnion_of_mem hu) }

lemma gc_nhds (a : α) :
  @galois_connection _ (order_dual (filter α)) _ _ (λt, @nhds α t a) (topological_space.nhds_adjoint a) :=
assume t (f : filter α), show f ≤ @nhds α t a ↔ _, from iff.intro
  (assume h s hs has, h $ @mem_nhds_sets α t a s hs has)
  (assume h, le_infi $ assume u, le_infi $ assume ⟨hau, hu⟩, le_principal_iff.2 $ h _ hu hau)

lemma nhds_mono {t₁ t₂ : topological_space α} {a : α} (h : t₁ ≤ t₂) :
  @nhds α t₂ a ≤ @nhds α t₁ a := (gc_nhds a).monotone_l h

lemma nhds_supr {ι : Sort*} {t : ι → topological_space α} {a : α} :
  @nhds α (supr t) a = (⨅i, @nhds α (t i) a) := (gc_nhds a).l_supr

lemma nhds_Sup {s : set (topological_space α)} {a : α} :
  @nhds α (Sup s) a = (⨅t∈s, @nhds α t a) := (gc_nhds a).l_Sup

lemma nhds_sup {t₁ t₂ : topological_space α} {a : α} :
  @nhds α (t₁ ⊔ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a := (gc_nhds a).l_sup

lemma nhds_bot {a : α} : @nhds α ⊥ a = ⊤ := (gc_nhds a).l_bot

private lemma separated_by_f
  [tα : topological_space α] [tβ : topological_space β] [t2_space β]
  (f : α → β) (hf : induced f tβ ≤ tα) {x y : α} (h : f x ≠ f y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h in
⟨f ⁻¹' u, f ⁻¹' v, hf _ ⟨u, uo, rfl⟩, hf _ ⟨v, vo, rfl⟩, xu, yv,
  by rw [←preimage_inter, uv, preimage_empty]⟩

instance {p : α → Prop} [t : topological_space α] [t2_space α] : t2_space (subtype p) :=
⟨assume x y h,
  separated_by_f subtype.val (le_refl _) (mt subtype.eq h)⟩

instance [t₁ : topological_space α] [t2_space α] [t₂ : topological_space β] [t2_space β] :
  t2_space (α × β) :=
⟨assume ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ h,
  or.elim (not_and_distrib.mp (mt prod.ext_iff.mpr h))
    (λ h₁, separated_by_f prod.fst le_sup_left h₁)
    (λ h₂, separated_by_f prod.snd le_sup_right h₂)⟩

instance Pi.t2_space {β : α → Type v} [t₂ : Πa, topological_space (β a)] [Πa, t2_space (β a)] :
  t2_space (Πa, β a) :=
⟨assume x y h,
  let ⟨i, hi⟩ := not_forall.mp (mt funext h) in
  separated_by_f (λz, z i) (le_supr _ i) hi⟩

end constructions

namespace topological_space
/- countability axioms

For our applications we are interested that there exists a countable basis, but we do not need the
concrete basis itself. This allows us to declare these type classes as `Prop` to use them as mixins.
-/
variables {α : Type u} [t : topological_space α]
include t

/-- A topological basis is one that satisfies the necessary conditions so that
  it suffices to take unions of the basis sets to get a topology (without taking
  finite intersections as well). -/
def is_topological_basis (s : set (set α)) : Prop :=
(∀t₁∈s, ∀t₂∈s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃∈s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂) ∧
(⋃₀ s) = univ ∧
t = generate_from s

lemma is_topological_basis_of_subbasis {s : set (set α)} (hs : t = generate_from s) :
  is_topological_basis ((λf, ⋂₀ f) '' {f:set (set α) | finite f ∧ f ⊆ s ∧ ⋂₀ f ≠ ∅}) :=
let b' := (λf, ⋂₀ f) '' {f:set (set α) | finite f ∧ f ⊆ s ∧ ⋂₀ f ≠ ∅} in
⟨assume s₁ ⟨t₁, ⟨hft₁, ht₁b, ht₁⟩, eq₁⟩ s₂ ⟨t₂, ⟨hft₂, ht₂b, ht₂⟩, eq₂⟩,
    have ie : ⋂₀(t₁ ∪ t₂) = ⋂₀ t₁ ∩ ⋂₀ t₂, from Inf_union,
    eq₁ ▸ eq₂ ▸ assume x h,
      ⟨_, ⟨t₁ ∪ t₂, ⟨finite_union hft₁ hft₂, union_subset ht₁b ht₂b,
        by simpa [ie] using ne_empty_of_mem h⟩, ie⟩, h, subset.refl _⟩,
  eq_univ_iff_forall.2 $ assume a, ⟨univ, ⟨∅, by simp; exact (@empty_ne_univ _ ⟨a⟩).symm⟩, mem_univ _⟩,
 have generate_from s = generate_from b',
    from le_antisymm
      (generate_from_le $ assume s hs,
        by_cases
          (assume : s = ∅, by rw [this]; apply @is_open_empty _ _)
          (assume : s ≠ ∅, generate_open.basic _ ⟨{s}, by simp [this, hs]⟩))
      (generate_from_le $ assume u ⟨t, ⟨hft, htb, ne⟩, eq⟩,
        eq ▸ @is_open_sInter _ (generate_from s) _ hft (assume s hs, generate_open.basic _ $ htb hs)),
  this ▸ hs⟩

lemma is_topological_basis_of_open_of_nhds {s : set (set α)}
  (h_open : ∀ u ∈ s, _root_.is_open u)
  (h_nhds : ∀(a:α) (u : set α), a ∈ u → _root_.is_open u → ∃v ∈ s, a ∈ v ∧ v ⊆ u) :
  is_topological_basis s :=
⟨assume t₁ ht₁ t₂ ht₂ x ⟨xt₁, xt₂⟩,
    h_nhds x (t₁ ∩ t₂) ⟨xt₁, xt₂⟩
      (is_open_inter _ _ _ (h_open _ ht₁) (h_open _ ht₂)),
  eq_univ_iff_forall.2 $ assume a,
    let ⟨u, h₁, h₂, _⟩ := h_nhds a univ trivial (is_open_univ _) in
    ⟨u, h₁, h₂⟩,
  le_antisymm
    (assume u hu,
      (@is_open_iff_nhds α (generate_from _) _).mpr $ assume a hau,
        let ⟨v, hvs, hav, hvu⟩ := h_nhds a u hau hu in
        by rw nhds_generate_from; exact infi_le_of_le v (infi_le_of_le ⟨hav, hvs⟩ $ by simp [hvu]))
    (generate_from_le h_open)⟩

lemma mem_nhds_of_is_topological_basis {a : α} {s : set α} {b : set (set α)}
  (hb : is_topological_basis b) : s ∈ (nhds a).sets ↔ ∃t∈b, a ∈ t ∧ t ⊆ s :=
begin
  rw [hb.2.2, nhds_generate_from, infi_sets_eq'],
  { simp [and_comm, and.left_comm] },
  { exact assume s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩,
      have a ∈ s ∩ t, from ⟨hs₁, ht₁⟩,
      let ⟨u, hu₁, hu₂, hu₃⟩ := hb.1 _ hs₂ _ ht₂ _ this in
      ⟨u, ⟨hu₂, hu₁⟩, by simpa [(≥)] using hu₃⟩ },
  { suffices : a ∈ (⋃₀ b), { simpa [and_comm] },
    { rw [hb.2.1], trivial } }
end

lemma is_open_of_is_topological_basis {s : set α} {b : set (set α)}
  (hb : is_topological_basis b) (hs : s ∈ b) : _root_.is_open s :=
is_open_iff_mem_nhds.2 $ λ a as,
(mem_nhds_of_is_topological_basis hb).2 ⟨s, hs, as, subset.refl _⟩

lemma mem_basis_subset_of_mem_open {b : set (set α)}
  (hb : is_topological_basis b) {a:α} {u : set α} (au : a ∈ u)
  (ou : _root_.is_open u) : ∃v ∈ b, a ∈ v ∧ v ⊆ u :=
(mem_nhds_of_is_topological_basis hb).1 $ mem_nhds_sets ou au

lemma sUnion_basis_of_is_open {B : set (set α)}
  (hB : is_topological_basis B) {u : set α} (ou : _root_.is_open u) :
  ∃ S ⊆ B, u = ⋃₀ S :=
⟨{s ∈ B | s ⊆ u}, λ s h, h.1, set.ext $ λ a,
  ⟨λ ha, let ⟨b, hb, ab, bu⟩ := mem_basis_subset_of_mem_open hB ha ou in
         ⟨b, ⟨hb, bu⟩, ab⟩,
   λ ⟨b, ⟨hb, bu⟩, ab⟩, bu ab⟩⟩

lemma Union_basis_of_is_open {B : set (set α)}
  (hB : is_topological_basis B) {u : set α} (ou : _root_.is_open u) :
  ∃ (β : Type u) (f : β → set α), u = (⋃ i, f i) ∧ ∀ i, f i ∈ B :=
let ⟨S, sb, su⟩ := sUnion_basis_of_is_open hB ou in
⟨S, subtype.val, su.trans set.sUnion_eq_Union, λ ⟨b, h⟩, sb h⟩

variables (α)

/-- A separable space is one with a countable dense subset. -/
class separable_space : Prop :=
(exists_countable_closure_eq_univ : ∃s:set α, countable s ∧ closure s = univ)

/-- A first-countable space is one in which every point has a
  countable neighborhood basis. -/
class first_countable_topology : Prop :=
(nhds_generated_countable : ∀a:α, ∃s:set (set α), countable s ∧ nhds a = (⨅t∈s, principal t))

/-- A second-countable space is one with a countable basis. -/
class second_countable_topology : Prop :=
(is_open_generated_countable : ∃b:set (set α), countable b ∧ t = topological_space.generate_from b)

instance second_countable_topology.to_first_countable_topology
  [second_countable_topology α] : first_countable_topology α :=
let ⟨b, hb, eq⟩ := second_countable_topology.is_open_generated_countable α in
⟨assume a, ⟨{s | a ∈ s ∧ s ∈ b},
  countable_subset (assume x ⟨_, hx⟩, hx) hb, by rw [eq, nhds_generate_from]⟩⟩

lemma is_open_generated_countable_inter [second_countable_topology α] :
  ∃b:set (set α), countable b ∧ ∅ ∉ b ∧ is_topological_basis b :=
let ⟨b, hb₁, hb₂⟩ := second_countable_topology.is_open_generated_countable α in
let b' := (λs, ⋂₀ s) '' {s:set (set α) | finite s ∧ s ⊆ b ∧ ⋂₀ s ≠ ∅} in
⟨b',
  countable_image _ $ countable_subset (by simp {contextual:=tt}) (countable_set_of_finite_subset hb₁),
  assume ⟨s, ⟨_, _, hn⟩, hp⟩, hn hp,
  is_topological_basis_of_subbasis hb₂⟩

instance second_countable_topology.to_separable_space
  [second_countable_topology α] : separable_space α :=
let ⟨b, hb₁, hb₂, hb₃, hb₄, eq⟩ := is_open_generated_countable_inter α in
have nhds_eq : ∀a, nhds a = (⨅ s : {s : set α // a ∈ s ∧ s ∈ b}, principal s.val),
  by intro a; rw [eq, nhds_generate_from]; simp [infi_subtype],
have ∀s∈b, ∃a, a ∈ s, from assume s hs, exists_mem_of_ne_empty $ assume eq, hb₂ $ eq ▸ hs,
have ∃f:∀s∈b, α, ∀s h, f s h ∈ s, by simp only [skolem] at this; exact this,
let ⟨f, hf⟩ := this in
⟨⟨(⋃s∈b, ⋃h:s∈b, {f s h}),
  countable_bUnion hb₁ (by simp [countable_Union_Prop]),
  set.ext $ assume a,
  have a ∈ (⋃₀ b), by rw [hb₄]; exact trivial,
  let ⟨t, ht₁, ht₂⟩ := this in
  have w : {s : set α // a ∈ s ∧ s ∈ b}, from ⟨t, ht₂, ht₁⟩,
  suffices (⨅ (x : {s // a ∈ s ∧ s ∈ b}), principal (x.val ∩ ⋃s (h₁ h₂ : s ∈ b), {f s h₂})) ≠ ⊥,
    by simpa [closure_eq_nhds, nhds_eq, infi_inf w],
  infi_neq_bot_of_directed ⟨a⟩
    (assume ⟨s₁, has₁, hs₁⟩ ⟨s₂, has₂, hs₂⟩,
      have a ∈ s₁ ∩ s₂, from ⟨has₁, has₂⟩,
      let ⟨s₃, hs₃, has₃, hs⟩ := hb₃ _ hs₁ _ hs₂ _ this in
      ⟨⟨s₃, has₃, hs₃⟩, begin
        simp only [le_principal_iff, mem_principal_sets, (≥)],
        simp at hs, split; apply inter_subset_inter_left; simp [hs]
      end⟩)
    (assume ⟨s, has, hs⟩,
      have s ∩ (⋃ (s : set α) (H h : s ∈ b), {f s h}) ≠ ∅,
        from ne_empty_of_mem ⟨hf _ hs, mem_bUnion hs $ mem_Union.mpr ⟨hs, by simp⟩⟩,
      by simp [this]) ⟩⟩

lemma is_open_sUnion_countable [second_countable_topology α]
  (S : set (set α)) (H : ∀ s ∈ S, _root_.is_open s) :
  ∃ T : set (set α), countable T ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S :=
let ⟨B, cB, _, bB⟩ := is_open_generated_countable_inter α in
begin
  let B' := {b ∈ B | ∃ s ∈ S, b ⊆ s},
  rcases axiom_of_choice (λ b:B', b.2.2) with ⟨f, hf⟩,
  change B' → set α at f,
  haveI : encodable B' := (countable_subset (sep_subset _ _) cB).to_encodable,
  have : range f ⊆ S := range_subset_iff.2 (λ x, (hf x).fst),
  exact ⟨_, countable_range f, this,
    subset.antisymm (sUnion_subset_sUnion this) $
    sUnion_subset $ λ s hs x xs,
      let ⟨b, hb, xb, bs⟩ := mem_basis_subset_of_mem_open bB xs (H _ hs) in
      ⟨_, ⟨⟨_, hb, _, hs, bs⟩, rfl⟩, (hf _).snd xb⟩⟩
end

end topological_space

section limit
variables {α : Type u} [inhabited α] [topological_space α]
open classical

/-- If `f` is a filter, then `lim f` is a limit of the filter, if it exists. -/
noncomputable def lim (f : filter α) : α := epsilon $ λa, f ≤ nhds a

lemma lim_spec {f : filter α} (h : ∃a, f ≤ nhds a) : f ≤ nhds (lim f) := epsilon_spec h

variables [t2_space α] {f : filter α}

lemma lim_eq {a : α} (hf : f ≠ ⊥) (h : f ≤ nhds a) : lim f = a :=
eq_of_nhds_neq_bot $ neq_bot_of_le_neq_bot hf $ le_inf (lim_spec ⟨_, h⟩) h

@[simp] lemma lim_nhds_eq {a : α} : lim (nhds a) = a :=
lim_eq nhds_neq_bot (le_refl _)

@[simp] lemma lim_nhds_eq_of_closure {a : α} {s : set α} (h : a ∈ closure s) :
  lim (nhds a ⊓ principal s) = a :=
lim_eq begin rw [closure_eq_nhds] at h, exact h end inf_le_left

end limit
