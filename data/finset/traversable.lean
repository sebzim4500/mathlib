
import data.finset data.multiset
       category.basic category.functor
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

def traverse (s : finset α') : F (finset β') :=
multiset.to_finset <$> s.val.traverse f

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
by cases x; simp [traverse,multiset.id_traverse]; rw multiset.to_finset_eq; refl

open functor

section comp_traversable
open is_idempotent_applicative is_comm_applicative

open multiset (erase_dup erase_dup_cons erase_dup_ndinsert)
lemma traverse_ndinsert {H : Type* → Type*}
    [applicative H]
    [is_comm_applicative H]
    [is_idempotent_applicative H]
    (f : α' → H β') (x : α') (xs : multiset α') :
  erase_dup <$> multiset.traverse f (multiset.ndinsert x xs) =
  erase_dup <$> (multiset.ndinsert <$> f x <*> multiset.traverse f xs) :=
-- multiset.induction_on xs _ $ λ x xs ih, _
begin
  by_cases x ∈ xs; simp *,
  { cases multiset.exists_cons_of_mem h with ys h',
    simp [h',idempotent_map,(∘),dup,multiset.ndinsert_cons] with functor_norm },
  { simp [(∘)] with functor_norm, congr, ext : 2,
    simp [erase_dup_cons,erase_dup_ndinsert] }
end

lemma traverse_insert {H : Type* → Type*}
    [applicative H]
    [is_idempotent_applicative H]
    (f : α' → H β') (x : α') (xs : finset α') :
  finset.traverse f (insert x xs) =
  insert <$> f x <*> finset.traverse f xs :=
begin
  simp [insert_def,traverse,traverse_ndinsert,(∘),multiset.to_finset] with functor_norm,
  refine functor.eq_of_injective_of_eq finset.val _ _,
  { rintro ⟨ ⟩ ⟨ ⟩ , simp },
  have : (val ∘ multiset.to_finset : multiset β' → multiset β') = multiset.erase_dup,
  { ext : 1, simp [(∘)] },
  simp [this,traverse_ndinsert] with functor_norm,
  congr' 2, ext : 2, simp [(∘),erase_dup_ndinsert],
end

lemma to_finset_map_traverse {H : Type* → Type*}
    [applicative H]
    [is_comm_applicative H]
    [is_idempotent_applicative H]
    (h : α' → H β') (x : multiset α') :
       multiset.to_finset <$> multiset.traverse h x =
       traverse h (multiset.to_finset x) :=
multiset.induction_on x rfl $ λ x xs ih,
(by { simp with functor_norm, rw [traverse_insert,← ih],
      simp [(∘)] with functor_norm, })

lemma comp_traverse {G H : Type* → Type*}
               [applicative G] [applicative H]
               [is_comm_applicative G]
               [is_comm_applicative H]
               [is_idempotent_applicative G]
               [is_idempotent_applicative H]
               {α β γ : Type*}
               (g : α → G β) (h : β → H γ) (x : finset α) :
  traverse (comp.mk ∘ functor.map h ∘ g) x =
  comp.mk (functor.map (traverse h) (traverse g x)) :=
begin
  cases x, simp! [comp.map,traverse,multiset.comp_traverse] with functor_norm,
  congr' 2, ext, simp [(∘),to_finset_map_traverse],
end

--                [applicative G] [applicative H]
--                {α β γ : Type*}
--                (g : α → G β) (h : β → H γ) (x : finset α) :

end comp_traversable

@[simp]
lemma to_finset_map (h : α' → β') (x : multiset α') :
  multiset.to_finset (h <$> x) = h <$> multiset.to_finset x :=
by simp [functor.map,image,multiset.to_finset,multiset.erase_dup_map_erase_dup_eq]; congr

lemma map_eq_traverse_id {α β} (f : α → β) (x : finset α) :
  traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
by { cases x, simp [traverse],
     rw [multiset.traverse_eq_map_id],
     simp! [functor.map_map,multiset.to_finset_eq] }

lemma map_eq_traverse_id' {α β} (f : α → β) (x : finset α) :
  (f <$> x) = id.run (traverse (id.mk ∘ f) x) :=
by rw map_eq_traverse_id; refl

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
--                [applicative G] [is_idempotent_applicative G]
--                {α β γ : Type*}
--                (g : α → β) (h : β → G γ)
--                (x : finset α) :
--   traverse h (functor.map g x) =
--   traverse (h ∘ g) x :=
-- begin
--   simp [map_eq_traverse_id',map_id_run (traverse h)],
--   transitivity,
--   refine (comp_traverse (id.mk ∘ g) h x).symm,
--   -- unfreezeI, -- cases _inst_5, cases _to_is_comm_applicative,
--   have : @comp.applicative id G _ _ = _inst_4,
--   { apply applicative.ext; intros; refl },
--   congr, apply comp.applicative_id_comp,
--   apply proof_irrel_heq, congr, assumption,
-- end

lemma naturality {G H : Type* → Type*}
                [applicative G] [applicative H]
                [is_comm_applicative G] [is_comm_applicative H]
                (eta : applicative_transformation G H)
                {α β : Type*} (f : α → G β) (x : finset α) :
  eta (traverse f x) = traverse (@eta _ ∘ f) x :=
by cases x; simp [traverse,multiset.naturality] with functor_norm

end finset
