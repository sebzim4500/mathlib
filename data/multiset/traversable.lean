
import data.finset data.multiset
       category.basic
universes u_1
namespace finset

local attribute [instance, priority 0] classical.prop_decidable

noncomputable instance : functor finset :=
{ map := λ α β, @finset.image α β _ }

instance : is_lawful_functor finset :=
by refine { .. }; intros; simp [finset.image_id,image_image]

variables {F : Type u_1 → Type u_1} [applicative F] [is_comm_applicative F]
variables {α' β' γ' : Type u_1} [decidable_eq β']
          (f : α' → F β')
#check multiset.traverse
def traverse :
  finset α' → F (finset β')
| ⟨ m, _ ⟩ := multiset.to_finset <$> m.traverse f

@[simp]
lemma lift_beta {α β : Type*} (x : list α) (f : list α → β)
  (h : ∀ a b : list α, a ≈ b → f a = f b) :
  quotient.lift f h (x : multiset α) = f x :=
quotient.lift_beta _ _ _

@[simp]
lemma map_comp_coe {α β} (h : α → β) :
  functor.map h ∘ coe = (coe ∘ functor.map h : list α → multiset β) :=
by funext; simp [functor.map]

lemma id_traverse {α : Type*} (x : finset α) :
  traverse id.mk x = x :=
by cases x; simp! [multiset.id_traverse]; rw multiset.to_finset_eq; refl

open functor

-- section comp_traversable

-- lemma to_finset_map_traverse
--   {H : Type* → Type*}
--   [applicative H]
--   [is_comm_applicative H]
--   (h : α' → H β') (x : multiset α') :
-- multiset.to_finset <$> multiset.traverse h x =
-- traverse h (multiset.to_finset x) :=
-- quotient.induction_on x
-- (by { intro x, induction x with x xs, refl,
--       simp [multiset.traverse,traversable.traverse], -- multiset.to_finset,multiset.erase_dup_map_erase_dup_eq],
--       congr })

-- lemma comp_traverse {G H : Type* → Type*}
--                [applicative G] [applicative H]
--                [is_comm_applicative G] [is_comm_applicative H]
--                {α β γ : Type*}
--                (g : α → G β) (h : β → H γ) (x : finset α) :
--   traverse (comp.mk ∘ functor.map h ∘ g) x =
--   comp.mk (functor.map (traverse h) (traverse g x)) :=
-- by cases x; simp! [comp.map,traverse,multiset.comp_traverse,functor.map_map,function.comp,functor.map];
--    congr; ext;  simp [to_finset_map_traverse,multiset.to_finset,multiset.erase_dup_erase_dup]

-- end comp_traversable

@[simp]
lemma to_finset_map (h : α' → β') (x : multiset α') :
  multiset.to_finset (h <$> x) = h <$> multiset.to_finset x :=
by simp [functor.map,image,multiset.to_finset,multiset.erase_dup_map_erase_dup_eq]; congr

lemma traverse_eq_map_id {α β} (f : α → β) (x : finset α) :
  traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
by { cases x, simp [traverse],
   rw [multiset.traverse_eq_map_id],
   simp! [functor.map_map,multiset.to_finset_eq] }

lemma map_traverse {G : Type* → Type*}
               [applicative G] [is_comm_applicative G]
               {α β γ : Type*}
               (g : α → G β) (h : β → γ)
               (x : finset α) :
  functor.map (functor.map h) (traverse g x) =
  traverse (functor.map h ∘ g) x :=
by cases x; simp [traverse];
   rw [← multiset.map_traverse];
   simp [functor.map_map,function.comp,to_finset_map]

-- lemma traverse_map {G : Type* → Type*}
--                [applicative G] [is_comm_applicative G]
--                {α β γ : Type*}
--                (g : α → β) (h : β → G γ)
--                (x : finset α) :
--   traverse h (functor.map g x) =
--   traverse (h ∘ g) x :=
-- by cases x; simp! [traverse,to_finset_map];
--    rw [← multiset.traverse_map g h];
--    simp [to_finset_map_traverse,multiset.to_finset,multiset.erase_dup_erase_dup]

lemma naturality {G H : Type* → Type*}
                [applicative G] [applicative H]
                [is_comm_applicative G] [is_comm_applicative H]
                (eta : applicative_transformation G H)
                {α β : Type*} (f : α → G β) (x : finset α) :
  eta (traverse f x) = traverse (@eta _ ∘ f) x :=
by cases x; simp [traverse,multiset.naturality] with functor_norm

end finset
