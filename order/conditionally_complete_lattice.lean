/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
Adapted from the corresponding theory for complete lattices.

Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset s
has a least upper bound and a greatest lower bound, denoted below by Sup s and Inf s.
Typical examples are real, nat, int with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and non-emptyness assumptions have to be added to most statements.
We introduce two predicates bdd_above and bdd_below to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of Sup and Inf
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix Inf and Sup in the statements by c, giving cInf and cSup. For instance,
Inf_le is a statement in complete lattices ensuring Inf s ≤ x, while cInf_le is the same
statement in conditionally complete lattices with an additional assumption that s is
bounded below.
-/
import
  order.lattice order.complete_lattice order.bounds
  tactic.finish data.set.countable

set_option old_structure_cmd true

open preorder set lattice

universes u v
variables {α : Type u} {β : Type v}

section preorder
variables [preorder α] {s t : set α} {a b : α}

/-Sets bounded above and bounded below.-/
def bdd_above (s : set α) := ∃x, ∀y∈s, y ≤ x
def bdd_below (s : set α) := ∃x, ∀y∈s, x ≤ y

/-Introduction rules for boundedness above and below.
Most of the time, it is more efficient to use ⟨w, P⟩ where P is a proof
that all elements of the set are bounded by w. However, they are sometimes handy.-/
lemma bdd_above.mk (a : α) (H : ∀y∈s, y≤a) : bdd_above s := ⟨a, H⟩
lemma bdd_below.mk (a : α) (H : ∀y∈s, a≤y) : bdd_below s := ⟨a, H⟩

/-Empty sets and singletons are trivially bounded. For finite sets, we need
a notion of maximum and minimum, i.e., a lattice structure, see later on.-/
@[simp] lemma bdd_above_empty [inhabited α] : bdd_above (∅ : set α) :=
⟨default α, by simp only [set.mem_empty_eq, forall_const, forall_prop_of_false, not_false_iff]⟩

@[simp] lemma bdd_below_empty [inhabited α] : bdd_below (∅ : set α) :=
⟨default α, by simp only [set.mem_empty_eq, forall_const, forall_prop_of_false, not_false_iff]⟩

@[simp] lemma bdd_above_singleton : bdd_above ({a} : set α) :=
⟨a, by simp only [set.mem_singleton_iff, forall_eq]⟩

@[simp] lemma bdd_below_singleton : bdd_below ({a} : set α) :=
⟨a, by simp only [set.mem_singleton_iff, forall_eq]⟩

/-If a set is included in another one, boundedness of the second implies boundedness
of the first-/
lemma bdd_above_subset (_ : s ⊆ t) (_ : bdd_above t) : bdd_above s :=
let ⟨w, hw⟩ := ‹bdd_above t› in  /-hw : ∀ (y : α), y ∈ t → y ≤ w-/
⟨w, assume (y : α) (_ : y ∈ s), hw _ (‹s ⊆ t› ‹y ∈ s›)⟩

lemma bdd_below_subset (_ : s ⊆ t) (_ : bdd_below t) : bdd_below s :=
let ⟨w, hw⟩ := ‹bdd_below t› in  /-hw : ∀ (y : α), y ∈ t → w ≤ y-/
⟨w, assume (y : α) (_ : y ∈ s), hw _ (‹s ⊆ t› ‹y ∈ s›)⟩

/- Boundedness of intersections of sets, in different guises, deduced from the
monotonicity of boundedness.-/
lemma bdd_above_Int1 (_ : bdd_above s) : bdd_above (s ∩ t) :=
by apply bdd_above_subset _ ‹bdd_above s›; simp only [set.inter_subset_left]

lemma bdd_above_Int2 (_ : bdd_above t) : bdd_above (s ∩ t) :=
by apply bdd_above_subset _ ‹bdd_above t›; simp only [set.inter_subset_right]

lemma bdd_below_Int1 (_ : bdd_below s) : bdd_below (s ∩ t) :=
by apply bdd_below_subset _ ‹bdd_below s›; simp only [set.inter_subset_left]

lemma bdd_below_Int2 (_ : bdd_below t) : bdd_below (s ∩ t) :=
by apply bdd_below_subset _ ‹bdd_below t›; simp only [set.inter_subset_right]

end preorder

/--When there is a global maximum, every set is bounded above.-/
@[simp] lemma bdd_above_top [order_top α] (s : set α) : bdd_above s :=
⟨⊤, by intros; apply order_top.le_top⟩

/--When there is a global minimum, every set is bounded below.-/
@[simp] lemma bdd_below_bot [order_bot α] (s : set α): bdd_below s :=
⟨⊥, by intros; apply order_bot.bot_le⟩

/-When there is a max (i.e., in the class semilattice_sup), then the union of
two bounded sets is bounded, by the maximum of the bounds for the two sets.
With this, we deduce that finite sets are bounded by induction, and that a finite
union of bounded sets is bounded.-/
section semilattice_sup
variables [semilattice_sup α] {s t : set α} {a b : α}

/--The union of two sets is bounded above if and only if each of the sets is.-/
@[simp] lemma bdd_above_union : bdd_above (s ∪ t) ↔ bdd_above s ∧ bdd_above t :=
⟨show bdd_above (s ∪ t) → (bdd_above s ∧ bdd_above t), from
  assume : bdd_above (s ∪ t),
  have S : bdd_above s, by apply bdd_above_subset _ ‹bdd_above (s ∪ t)›; simp only [set.subset_union_left],
  have T : bdd_above t, by apply bdd_above_subset _ ‹bdd_above (s ∪ t)›; simp only [set.subset_union_right],
  and.intro S T,
show (bdd_above s ∧ bdd_above t) → bdd_above (s ∪ t), from
  assume H : bdd_above s ∧ bdd_above t,
  let ⟨⟨ws, hs⟩, ⟨wt, ht⟩⟩ := H in
    /-hs : ∀ (y : α), y ∈ s → y ≤ ws      ht : ∀ (y : α), y ∈ s → y ≤ wt-/
  have Bs : ∀b∈s, b ≤ ws ⊔ wt,
    by intros; apply le_trans (hs b ‹b ∈ s›) _; simp only [lattice.le_sup_left],
  have Bt : ∀b∈t, b ≤ ws ⊔ wt,
    by intros; apply le_trans (ht b ‹b ∈ t›) _; simp only [lattice.le_sup_right],
  show bdd_above (s ∪ t),
    begin
    apply bdd_above.mk (ws ⊔ wt),
    intros b H_1,
    cases H_1,
    apply Bs _ ‹b ∈ s›,
    apply Bt _ ‹b ∈ t›,
    end⟩

/--Adding a point to a set preserves its boundedness above.-/
@[simp] lemma bdd_above_insert : bdd_above (insert a s) ↔ bdd_above s :=
⟨show bdd_above (insert a s) → bdd_above s, from bdd_above_subset (by simp only [set.subset_insert]),
 show bdd_above s → bdd_above (insert a s), by rw [insert_eq]; simp only [bdd_above_singleton, and_self, bdd_above_union, forall_true_iff] {contextual := tt}⟩

/--A finite set is bounded above.-/
lemma bdd_above_finite [inhabited α] (_ : finite s) : bdd_above s :=
by apply finite.induction_on ‹finite s›; simp only [bdd_above_insert, imp_self, forall_const, forall_true_iff,bdd_above_empty]

/--A finite union of sets which are all bounded above is still bounded above.-/
lemma bdd_above_finite_union [inhabited α] {β : Type v} {I : set β} {S : β → set α} (H : finite I) :
(bdd_above (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_above (S i)) :=
⟨show (bdd_above (⋃i∈I, S i)) → (∀i ∈ I, bdd_above (S i)), by
  intros;
  apply bdd_above_subset _ ‹bdd_above (⋃i∈I, S i)›;
  apply subset_bUnion_of_mem ‹i ∈ I›,
show (∀i ∈ I, bdd_above (S i)) → (bdd_above (⋃i∈I, S i)),
  by apply finite.induction_on ‹finite I›;
       simp only [set.mem_insert_iff, set.bUnion_insert, bdd_above_union,forall_prop_of_true,
           set.mem_empty_eq,set.Union_empty,forall_prop_of_false,bdd_above_empty,
           set.Union_neg,not_false_iff,forall_true_iff];
       finish⟩

end semilattice_sup


/-When there is a min (i.e., in the class semilattice_inf), then the union of
two sets which are bounded from below is bounded from below, by the minimum of
the bounds for the two sets. With this, we deduce that finite sets are
bounded below by induction, and that a finite union of sets which are bounded below
is still bounded below.-/

section semilattice_inf
variables [semilattice_inf α] {s t : set α} {a b : α}

/--The union of two sets is bounded below if and only if each of the sets is.-/
@[simp] lemma bdd_below_union : bdd_below (s ∪ t) ↔ bdd_below s ∧ bdd_below t :=
⟨show bdd_below (s ∪ t) → (bdd_below s ∧ bdd_below t), from
  assume : bdd_below (s ∪ t),
  have S : bdd_below s, by apply bdd_below_subset _ ‹bdd_below (s ∪ t)›; simp only [set.subset_union_left],
  have T : bdd_below t, by apply bdd_below_subset _ ‹bdd_below (s ∪ t)›; simp only [set.subset_union_right],
  and.intro S T,
show (bdd_below s ∧ bdd_below t) → bdd_below (s ∪ t), from
  assume H : bdd_below s ∧ bdd_below t,
  let ⟨⟨ws, hs⟩, ⟨wt, ht⟩⟩ := H in
    /-hs : ∀ (y : α), y ∈ s → ws ≤ y      ht : ∀ (y : α), y ∈ s → wt ≤ y-/
  have Bs : ∀b∈s, ws ⊓ wt ≤ b,
    by intros; apply le_trans _ (hs b ‹b ∈ s›); simp only [lattice.inf_le_left],
  have Bt : ∀b∈t, ws ⊓ wt ≤ b,
    by intros; apply le_trans _ (ht b ‹b ∈ t›); simp only [lattice.inf_le_right],
  show bdd_below (s ∪ t),
    begin
    apply bdd_below.mk (ws ⊓ wt),
    intros b H_1,
    cases H_1,
    apply Bs _ ‹b ∈ s›,
    apply Bt _ ‹b ∈ t›,
    end⟩

/--Adding a point to a set preserves its boundedness below.-/
@[simp] lemma bdd_below_insert : bdd_below (insert a s) ↔ bdd_below s :=
⟨show bdd_below (insert a s) → bdd_below s, from bdd_below_subset (by simp only [set.subset_insert]),
 show bdd_below s → bdd_below (insert a s),
   by rw[insert_eq]; simp only [bdd_below_singleton, bdd_below_union, and_self, forall_true_iff] {contextual := tt}⟩

/--A finite set is bounded below.-/
lemma bdd_below_finite [inhabited α] (_ : finite s) : bdd_below s :=
by apply finite.induction_on ‹finite s›; simp only [imp_self, forall_const, bdd_below_insert, forall_true_iff,bdd_below_empty]

/--A finite union of sets which are all bounded below is still bounded below.-/
lemma bdd_below_finite_union [inhabited α] {β : Type v} {I : set β} {S : β → set α} (H : finite I) :
(bdd_below (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_below (S i)) :=
⟨show (bdd_below (⋃i∈I, S i)) → (∀i ∈ I, bdd_below (S i)), by
  intros;
  apply bdd_below_subset _ ‹bdd_below (⋃i∈I, S i)›;
  apply subset_bUnion_of_mem ‹i ∈ I›,
show (∀i ∈ I, bdd_below (S i)) → (bdd_below (⋃i∈I, S i)),
  by apply finite.induction_on ‹finite I›;
       simp only [set.mem_insert_iff, set.bUnion_insert, bdd_below_union,
           forall_prop_of_true,set.mem_empty_eq,set.Union_empty,
           forall_prop_of_false,bdd_below_empty,set.Union_neg,
           not_false_iff,forall_true_iff];
       finish⟩

end semilattice_inf


namespace lattice
/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of non-emptyness or
boundedness.-/
class conditionally_complete_lattice (α : Type u) extends lattice α, has_Sup α, has_Inf α :=
(le_cSup : ∀s a, bdd_above s → a ∈ s → a ≤ Sup s)
(cSup_le : ∀s a, s ≠ ∅ → (∀b∈s, b ≤ a) → Sup s ≤ a)
(cInf_le : ∀s a, bdd_below s → a ∈ s → Inf s ≤ a)
(le_cInf : ∀s a, s ≠ ∅ → (∀b∈s, a ≤ b) → a ≤ Inf s)

class conditionally_complete_linear_order (α : Type u)
  extends conditionally_complete_lattice α, linear_order α

class conditionally_complete_linear_order_bot (α : Type u)
  extends conditionally_complete_lattice α, linear_order α, order_bot α :=
(cSup_empty : Sup ∅ = ⊥)

/- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/

instance conditionally_complete_lattice_of_complete_lattice [complete_lattice α]:
  conditionally_complete_lattice α :=
{ le_cSup := by intros; apply le_Sup; assumption,
  cSup_le := by intros; apply Sup_le; assumption,
  cInf_le := by intros; apply Inf_le; assumption,
  le_cInf := by intros; apply le_Inf; assumption,
  ..‹complete_lattice α›}

instance conditionally_complete_linear_order_of_complete_linear_order [complete_linear_order α]:
  conditionally_complete_linear_order α :=
{ ..lattice.conditionally_complete_lattice_of_complete_lattice, .. ‹complete_linear_order α› }

section conditionally_complete_lattice
variables [conditionally_complete_lattice α] {s t : set α} {a b : α}

theorem le_cSup (h₁ : bdd_above s) (h₂ : a ∈ s) : a ≤ Sup s :=
conditionally_complete_lattice.le_cSup s a h₁ h₂

theorem cSup_le (h₁ : s ≠ ∅) (h₂ : ∀b∈s, b ≤ a) : Sup s ≤ a :=
conditionally_complete_lattice.cSup_le s a h₁ h₂

theorem cInf_le (h₁ : bdd_below s) (h₂ : a ∈ s) : Inf s ≤ a :=
conditionally_complete_lattice.cInf_le s a h₁ h₂

theorem le_cInf (h₁ : s ≠ ∅) (h₂ : ∀b∈s, a ≤ b) : a ≤ Inf s :=
conditionally_complete_lattice.le_cInf s a h₁ h₂

theorem le_cSup_of_le (_ : bdd_above s) (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_cSup ‹bdd_above s› hb)

theorem cInf_le_of_le (_ : bdd_below s) (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (cInf_le ‹bdd_below s› hb) h

theorem cSup_le_cSup (_ : bdd_above t) (_ : s ≠ ∅) (h : s ⊆ t) : Sup s ≤ Sup t :=
cSup_le ‹s ≠ ∅› (assume (a) (ha : a ∈ s), le_cSup ‹bdd_above t› (h ha))

theorem cInf_le_cInf (_ : bdd_below t) (_ :s ≠ ∅) (h : s ⊆ t) : Inf t ≤ Inf s :=
le_cInf ‹s ≠ ∅› (assume (a) (ha : a ∈ s), cInf_le ‹bdd_below t› (h ha))

theorem cSup_le_iff (_ : bdd_above s) (_ : s ≠ ∅) : Sup s ≤ a ↔ (∀b ∈ s, b ≤ a) :=
⟨assume (_ : Sup s ≤ a) (b) (_ : b ∈ s),
  le_trans (le_cSup ‹bdd_above s› ‹b ∈ s›) ‹Sup s ≤ a›,
  cSup_le ‹s ≠ ∅›⟩

theorem le_cInf_iff (_ : bdd_below s) (_ : s ≠ ∅) : a ≤ Inf s ↔ (∀b ∈ s, a ≤ b) :=
⟨assume (_ : a ≤ Inf s) (b) (_ : b ∈ s),
  le_trans ‹a ≤ Inf s› (cInf_le ‹bdd_below s› ‹b ∈ s›),
  le_cInf ‹s ≠ ∅›⟩

lemma cSup_upper_bounds_eq_cInf {s : set α} (h : bdd_below s) (hs : s ≠ ∅) :
  Sup {a | ∀x∈s, a ≤ x} = Inf s :=
let ⟨b, hb⟩ := h, ⟨a, ha⟩ := ne_empty_iff_exists_mem.1 hs in
le_antisymm
  (cSup_le (ne_empty_iff_exists_mem.2 ⟨b, hb⟩) $ assume a ha, le_cInf hs ha)
  (le_cSup ⟨a, assume y hy, hy a ha⟩ $ assume x hx, cInf_le h hx)

lemma cInf_lower_bounds_eq_cSup {s : set α} (h : bdd_above s) (hs : s ≠ ∅) :
  Inf {a | ∀x∈s, x ≤ a} = Sup s :=
let ⟨b, hb⟩ := h, ⟨a, ha⟩ := ne_empty_iff_exists_mem.1 hs in
le_antisymm
  (cInf_le ⟨a, assume y hy, hy a ha⟩ $ assume x hx, le_cSup h hx)
  (le_cInf (ne_empty_iff_exists_mem.2 ⟨b, hb⟩) $ assume a ha, cSup_le hs ha)

/--Introduction rule to prove that b is the supremum of s: it suffices to check that b
is larger than all elements of s, and that this is not the case of any w<b.-/
theorem cSup_intro (_ : s ≠ ∅) (_ : ∀a∈s, a ≤ b) (H : ∀w, w < b → (∃a∈s, w < a)) : Sup s = b :=
have bdd_above s := ⟨b, by assumption⟩,
have (Sup s < b) ∨ (Sup s = b) := lt_or_eq_of_le (cSup_le ‹s ≠ ∅› ‹∀a∈s, a ≤ b›),
have ¬(Sup s < b) :=
  assume: Sup s < b,
  let ⟨a, _, _⟩ := (H (Sup s) ‹Sup s < b›) in  /- a ∈ s, Sup s < a-/
  have Sup s < Sup s := lt_of_lt_of_le ‹Sup s < a› (le_cSup ‹bdd_above s› ‹a ∈ s›),
  show false, by finish [lt_irrefl (Sup s)],
show Sup s = b, by finish

/--Introduction rule to prove that b is the infimum of s: it suffices to check that b
is smaller than all elements of s, and that this is not the case of any w>b.-/
theorem cInf_intro (_ : s ≠ ∅) (_ : ∀a∈s, b ≤ a) (H : ∀w, b < w → (∃a∈s, a < w)) : Inf s = b :=
have bdd_below s := ⟨b, by assumption⟩,
have (b < Inf s) ∨ (b = Inf s) := lt_or_eq_of_le (le_cInf ‹s ≠ ∅› ‹∀a∈s, b ≤ a›),
have ¬(b < Inf s) :=
  assume: b < Inf s,
  let ⟨a, _, _⟩ := (H (Inf s) ‹b < Inf s›) in  /- a ∈ s, a < Inf s-/
  have Inf s < Inf s := lt_of_le_of_lt (cInf_le ‹bdd_below s› ‹a ∈ s›) ‹a < Inf s› ,
  show false, by finish [lt_irrefl (Inf s)],
show Inf s = b, by finish

/--When an element a of a set s is larger than all elements of the set, it is Sup s-/
theorem cSup_of_in_of_le (_ : a ∈ s) (_ : ∀w∈s, w ≤ a) : Sup s = a :=
have bdd_above s := ⟨a, by assumption⟩,
have s ≠ ∅ := ne_empty_of_mem ‹a ∈ s›,
have A : a ≤ Sup s := le_cSup ‹bdd_above s› ‹a ∈ s›,
have B : Sup s ≤ a := cSup_le ‹s ≠ ∅› ‹∀w∈s, w ≤ a›,
le_antisymm B A

/--When an element a of a set s is smaller than all elements of the set, it is Inf s-/
theorem cInf_of_in_of_le (_ : a ∈ s) (_ : ∀w∈s, a ≤ w) : Inf s = a :=
have bdd_below s := ⟨a, by assumption⟩,
have s ≠ ∅ := ne_empty_of_mem ‹a ∈ s›,
have A : Inf s ≤ a := cInf_le ‹bdd_below s› ‹a ∈ s›,
have B : a ≤ Inf s := le_cInf ‹s ≠ ∅› ‹∀w∈s, a ≤ w›,
le_antisymm A B

/--b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptyness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
lemma lt_cSup_of_lt (_ : bdd_above s) (_ : a ∈ s) (_ : b < a) : b < Sup s :=
lt_of_lt_of_le ‹b < a› (le_cSup ‹bdd_above s› ‹a ∈ s›)

/--Inf s < b s when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptyness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/

lemma cInf_lt_of_lt (_ : bdd_below s) (_ : a ∈ s) (_ : a < b) : Inf s < b :=
lt_of_le_of_lt (cInf_le ‹bdd_below s› ‹a ∈ s›) ‹a < b›

/--The supremum of a singleton is the element of the singleton-/
@[simp] theorem cSup_singleton (a : α) : Sup {a} = a :=
have A : a ≤ Sup {a} :=
  by apply le_cSup _ _; simp only [set.mem_singleton,bdd_above_singleton],
have B : Sup {a} ≤ a :=
  by apply cSup_le _ _; simp only [set.mem_singleton_iff, forall_eq,ne.def, not_false_iff, set.singleton_ne_empty],
le_antisymm B A

/--The infimum of a singleton is the element of the singleton-/
@[simp] theorem cInf_singleton (a : α) : Inf {a} = a :=
have A : Inf {a} ≤ a :=
  by apply cInf_le _ _; simp only [set.mem_singleton,bdd_below_singleton],
have B : a ≤ Inf {a} :=
  by apply le_cInf _ _; simp only [set.mem_singleton_iff, forall_eq,ne.def, not_false_iff, set.singleton_ne_empty],
le_antisymm A B

/--If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cInf_le_cSup (_ : bdd_below s) (_ : bdd_above s) (_ : s ≠ ∅) : Inf s ≤ Sup s :=
let ⟨w, hw⟩ := exists_mem_of_ne_empty ‹s ≠ ∅› in   /-hw : w ∈ s-/
have Inf s ≤ w := cInf_le ‹bdd_below s› ‹w ∈ s›,
have w ≤ Sup s := le_cSup ‹bdd_above s› ‹w ∈ s›,
le_trans ‹Inf s ≤ w› ‹w ≤ Sup s›

/--The sup of a union of sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem cSup_union (_ : bdd_above s) (_ : s ≠ ∅) (_ : bdd_above t) (_ : t ≠ ∅) :
Sup (s ∪ t) = Sup s ⊔ Sup t :=
have A : Sup (s ∪ t) ≤ Sup s ⊔ Sup t :=
  have s ∪ t ≠ ∅ := by simp only [not_and, set.union_empty_iff, ne.def] at *; finish,
  have F : ∀b∈ s∪t, b ≤ Sup s ⊔ Sup t :=
    begin
      intros,
      cases H,
      apply le_trans (le_cSup ‹bdd_above s› ‹b ∈ s›) _, simp only [lattice.le_sup_left],
      apply le_trans (le_cSup ‹bdd_above t› ‹b ∈ t›) _, simp only [lattice.le_sup_right]
    end,
  cSup_le this F,
have B : Sup s ⊔ Sup t ≤ Sup (s ∪ t) :=
  have Sup s ≤ Sup (s ∪ t) := by apply cSup_le_cSup _ ‹s ≠ ∅›; simp only [bdd_above_union,set.subset_union_left]; finish,
  have Sup t ≤ Sup (s ∪ t) := by apply cSup_le_cSup _ ‹t ≠ ∅›; simp only [bdd_above_union,set.subset_union_right]; finish,
  by simp only [lattice.sup_le_iff]; split; assumption; assumption,
le_antisymm A B

/--The inf of a union of sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cInf_union (_ : bdd_below s) (_ : s ≠ ∅) (_ : bdd_below t) (_ : t ≠ ∅) :
Inf (s ∪ t) = Inf s ⊓ Inf t :=
have A : Inf s ⊓ Inf t ≤ Inf (s ∪ t) :=
  have s ∪ t ≠ ∅ := by simp only [not_and, set.union_empty_iff, ne.def] at *; finish,
  have F : ∀b∈ s∪t, Inf s ⊓ Inf t ≤ b :=
    begin
      intros,
      cases H,
      apply le_trans _ (cInf_le ‹bdd_below s› ‹b ∈ s›), simp only [lattice.inf_le_left],
      apply le_trans _ (cInf_le ‹bdd_below t› ‹b ∈ t›), simp only [lattice.inf_le_right]
    end,
  le_cInf this F,
have B : Inf (s ∪ t) ≤ Inf s ⊓ Inf t  :=
  have Inf (s ∪ t) ≤ Inf s := by apply cInf_le_cInf _ ‹s ≠ ∅›; simp only [bdd_below_union,set.subset_union_left]; finish,
  have Inf (s ∪ t) ≤ Inf t := by apply cInf_le_cInf _ ‹t ≠ ∅›; simp only [bdd_below_union,set.subset_union_right]; finish,
  by simp only [lattice.le_inf_iff]; split; assumption; assumption,
le_antisymm B A

/--The supremum of an intersection of sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le (_ : bdd_above s) (_ : bdd_above t) (_ : s ∩ t ≠ ∅) :
Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
begin
  apply cSup_le ‹s ∩ t ≠ ∅› _, simp only [lattice.le_inf_iff, and_imp, set.mem_inter_eq], intros b _ _, split,
  apply le_cSup ‹bdd_above s› ‹b ∈ s›,
  apply le_cSup ‹bdd_above t› ‹b ∈ t›
end

/--The infimum of an intersection of sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter (_ : bdd_below s) (_ : bdd_below t) (_ : s ∩ t ≠ ∅) :
Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
begin
  apply le_cInf ‹s ∩ t ≠ ∅› _, simp only [and_imp, set.mem_inter_eq, lattice.sup_le_iff], intros b _ _, split,
  apply cInf_le ‹bdd_below s› ‹b ∈ s›,
  apply cInf_le ‹bdd_below t› ‹b ∈ t›
end

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert (_ : bdd_above s) (_ : s ≠ ∅) : Sup (insert a s) = a ⊔ Sup s :=
calc Sup (insert a s)
        = Sup ({a} ∪ s)   : by rw [insert_eq]
    ... = Sup {a} ⊔ Sup s : by apply cSup_union _ _ ‹bdd_above s› ‹s ≠ ∅›; simp only [ne.def, not_false_iff, set.singleton_ne_empty,bdd_above_singleton]
    ... = a ⊔ Sup s       : by simp only [eq_self_iff_true, lattice.cSup_singleton]

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert (_ : bdd_below s) (_ : s ≠ ∅) : Inf (insert a s) = a ⊓ Inf s :=
calc Inf (insert a s)
        = Inf ({a} ∪ s)   : by rw [insert_eq]
    ... = Inf {a} ⊓ Inf s : by apply cInf_union _ _ ‹bdd_below s› ‹s ≠ ∅›; simp only [ne.def, not_false_iff, set.singleton_ne_empty,bdd_below_singleton]
    ... = a ⊓ Inf s       : by simp only [eq_self_iff_true, lattice.cInf_singleton]

@[simp] lemma cInf_interval [conditionally_complete_lattice α] : Inf {b | a ≤ b} = a :=
cInf_of_in_of_le (by simp only [set.mem_set_of_eq]) (λw Hw, by simp only [set.mem_set_of_eq] at Hw; apply Hw)

@[simp] lemma cSup_interval [conditionally_complete_lattice α] : Sup {b | b ≤ a} = a :=
cSup_of_in_of_le (by simp only [set.mem_set_of_eq]) (λw Hw, by simp only [set.mem_set_of_eq] at Hw; apply Hw)

end conditionally_complete_lattice


section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α] {s t : set α} {a b : α}

/--When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order.-/
lemma exists_lt_of_lt_cSup (_ : s ≠ ∅) (_ : b < Sup s) : ∃a∈s, b < a :=
begin
  apply classical.by_contradiction,
  assume : ¬ (∃a∈s, b < a),
  have : Sup s ≤ b :=
    by apply cSup_le ‹s ≠ ∅› _; finish,
  apply lt_irrefl b (lt_of_lt_of_le ‹b < Sup s› ‹Sup s ≤ b›)
end

/--When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
lemma exists_lt_of_cInf_lt (_ : s ≠ ∅) (_ : Inf s < b) : ∃a∈s, a < b :=
begin
  apply classical.by_contradiction,
  assume : ¬ (∃a∈s, a < b),
  have : b ≤ Inf s :=
    by apply le_cInf ‹s ≠ ∅› _; finish,
  apply lt_irrefl b (lt_of_le_of_lt ‹b ≤ Inf s› ‹Inf s < b›)
end

end conditionally_complete_linear_order

section conditionally_complete_linear_order_bot
variables [conditionally_complete_linear_order_bot α]

lemma cSup_empty [conditionally_complete_linear_order_bot α] : (Sup ∅ : α) = ⊥ :=
conditionally_complete_linear_order_bot.cSup_empty α

end conditionally_complete_linear_order_bot

section

local attribute [instance] classical.prop_decidable

noncomputable instance : has_Inf ℕ :=
⟨λs, if h : ∃n, n ∈ s then @nat.find (λn, n ∈ s) _ h else 0⟩

noncomputable instance : has_Sup ℕ :=
⟨λs, if h : ∃n, ∀a∈s, a ≤ n then @nat.find (λn, ∀a∈s, a ≤ n) _ h else 0⟩

lemma Inf_nat_def {s : set ℕ} (h : ∃n, n ∈ s) : Inf s = @nat.find (λn, n ∈ s) _ h :=
dif_pos _

lemma Sup_nat_def {s : set ℕ} (h : ∃n, ∀a∈s, a ≤ n) :
  Sup s = @nat.find (λn, ∀a∈s, a ≤ n) _ h :=
dif_pos _

/-- This instanec is necessary, otherwise the lattice operations would be derive via
conditionally_complete_linear_order_bot and marked as noncomputable. -/
instance : lattice ℕ := infer_instance

noncomputable instance : conditionally_complete_linear_order_bot ℕ :=
{ Sup := Sup, Inf := Inf,
  le_cSup    := assume s a hb ha, by rw [Sup_nat_def hb]; revert a ha; exact @nat.find_spec _ _ hb,
  cSup_le    := assume s a hs ha, by rw [Sup_nat_def ⟨a, ha⟩]; exact nat.find_min' _ ha,
  le_cInf    := assume s a hs hb,
    by rw [Inf_nat_def (ne_empty_iff_exists_mem.1 hs)]; exact hb _ (@nat.find_spec (λn, n ∈ s) _ _),
  cInf_le    := assume s a hb ha, by rw [Inf_nat_def ⟨a, ha⟩]; exact nat.find_min' _ ha,
  cSup_empty :=
  begin
    simp only [Sup_nat_def, set.mem_empty_eq, forall_const, forall_prop_of_false, not_false_iff, exists_const],
    apply bot_unique (nat.find_min' _ _),
    trivial
  end,
  .. (infer_instance : order_bot ℕ), .. (infer_instance : lattice ℕ),
  .. (infer_instance : linear_order ℕ) }

end

end lattice /-end of namespace lattice-/

namespace with_top
open lattice
local attribute [instance] classical.prop_decidable

variables [conditionally_complete_linear_order_bot α]

lemma has_lub (s : set (with_top α)) : ∃a, is_lub s a :=
begin
  by_cases hs : s = ∅, { subst hs, exact ⟨⊥, is_lub_empty⟩, },
  rcases ne_empty_iff_exists_mem.1 hs with ⟨x, hxs⟩,
  by_cases bnd : ∃b:α, ↑b ∈ upper_bounds s,
  { rcases bnd with ⟨b, hb⟩,
    have bdd : bdd_above {a : α | ↑a ∈ s}, from ⟨b, assume y hy, coe_le_coe.1 $ hb _ hy⟩,
    refine ⟨(Sup {a : α | ↑a ∈ s} : α), _, _⟩,
    { assume a has,
      rcases (le_coe_iff _ _).1 (hb _ has) with ⟨a, rfl, h⟩,
      exact (coe_le_coe.2 $ le_cSup bdd has) },
    { assume a hs,
      rcases (le_coe_iff _ _).1 (hb _ hxs) with ⟨x, rfl, h⟩,
      refine (coe_le_iff _ _).2 (assume c hc, _), subst hc,
      exact (cSup_le (ne_empty_of_mem hxs) $ assume b (hbs : ↑b ∈ s), coe_le_coe.1 $ hs _ hbs), } },
  exact ⟨⊤, assume a _, le_top, assume a,
    match a with
    | some a, ha := (bnd ⟨a, ha⟩).elim
    | none,   ha := _root_.le_refl ⊤
    end⟩
end

lemma has_glb (s : set (with_top α)) : ∃a, is_glb s a :=
begin
  by_cases hs : ∃x:α, ↑x ∈ s,
  { rcases hs with ⟨x, hxs⟩,
    refine ⟨(Inf {a : α | ↑a ∈ s} : α), _, _⟩,
    exact (assume a has, (coe_le_iff _ _).2 $ assume x hx, cInf_le (bdd_below_bot _) $
      show ↑x ∈ s, from hx ▸ has),
    { assume a has,
      rcases (le_coe_iff _ _).1 (has _ hxs) with ⟨x, rfl, h⟩,
      exact (coe_le_coe.2 $ le_cInf (ne_empty_of_mem hxs) $
        assume b hbs, coe_le_coe.1 $ has _ hbs) } },
  exact ⟨⊤, assume a, match a with
    | some a, ha := (hs ⟨a, ha⟩).elim
    | none,   ha := _root_.le_refl _
    end,
    assume a _, le_top⟩
end

noncomputable instance : has_Sup (with_top α) := ⟨λs, classical.some $ has_lub s⟩
noncomputable instance : has_Inf (with_top α) := ⟨λs, classical.some $ has_glb s⟩

lemma is_lub_Sup (s : set (with_top α)) : is_lub s (Sup s) := classical.some_spec _
lemma is_glb_Inf (s : set (with_top α)) : is_glb s (Inf s) := classical.some_spec _

noncomputable instance : complete_linear_order (with_top α) :=
{ Sup := Sup, le_Sup := assume s, (is_lub_Sup s).1, Sup_le := assume s, (is_lub_Sup s).2,
  Inf := Inf, le_Inf := assume s, (is_glb_Inf s).2, Inf_le := assume s, (is_glb_Inf s).1,
  .. with_top.linear_order, ..with_top.lattice, ..with_top.order_top, ..with_top.order_bot }

lemma coe_Sup {s : set α} (hb : bdd_above s) : (↑(Sup s) : with_top α) = (⨆a∈s, ↑a) :=
begin
  by_cases hs : s = ∅,
  { rw [hs, cSup_empty], simp only [set.mem_empty_eq, lattice.supr_bot, lattice.supr_false], refl },
  apply le_antisymm,
  { refine ((coe_le_iff _ _).2 $ assume b hb, cSup_le hs $ assume a has, coe_le_coe.1 $ hb ▸ _),
    exact (le_supr_of_le a $ le_supr_of_le has $ _root_.le_refl _) },
  { exact (supr_le $ assume a, supr_le $ assume ha, coe_le_coe.2 $ le_cSup hb ha) }
end

lemma coe_Inf {s : set α} (hs : s ≠ ∅) : (↑(Inf s) : with_top α) = (⨅a∈s, ↑a) :=
let ⟨x, hx⟩ := ne_empty_iff_exists_mem.1 hs in
have (⨅a∈s, ↑a : with_top α) ≤ x, from infi_le_of_le x $ infi_le_of_le hx $ _root_.le_refl _,
let ⟨r, r_eq, hr⟩ := (le_coe_iff _ _).1 this in
le_antisymm
  (le_infi $ assume a, le_infi $ assume ha, coe_le_coe.2 $ cInf_le (bdd_below_bot s) ha)
  begin
    refine (r_eq.symm ▸ coe_le_coe.2 $ le_cInf hs $ assume a has, coe_le_coe.1 $ _),
    refine (r_eq ▸ infi_le_of_le a _),
    exact (infi_le_of_le has $ _root_.le_refl _),
  end

end with_top
