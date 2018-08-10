/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances of `traversable` for types from the core library
-/

import category.traversable.basic
import category.basic
import category.functor
import category.applicative

universes u v

open function

instance : traversable id := ⟨λ _ _ _ _, id⟩
instance : is_lawful_traversable id := by refine {..}; intros; refl

section option

open function functor

section inst

variables {F : Type u → Type v}
variables [applicative F]

protected def option.traverse {α β} (f : α → F β) : option α → F (option β)
| none := pure none
| (some x) := some <$> f x

instance : traversable option := ⟨@option.traverse⟩

end inst

variables {F G : Type u → Type u}
variables [applicative F] [applicative G]
variables [is_lawful_applicative F] [is_lawful_applicative G]

lemma option.id_traverse {α} (x : option α) : option.traverse id.mk x = x :=
by cases x; refl

lemma option.comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : option α) :
  option.traverse (comp.mk ∘ (<$>) f ∘ g) x =
  comp.mk (option.traverse f <$> option.traverse g x) :=
by cases x; simp! with functor_norm; refl

lemma option.traverse_eq_map_id {α β} (f : α → β) (x : option α) :
  traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
by cases x; refl

variable (η : applicative_transformation F G)

lemma option.naturality {α β} (f : α → F β) (x : option α) :
  η (option.traverse f x) = option.traverse (@η _ ∘ f) x :=
by cases x with x; simp! [*] with functor_norm

end option

instance : is_lawful_traversable option :=
{ id_traverse := @option.id_traverse,
  comp_traverse := @option.comp_traverse,
  traverse_eq_map_id := @option.traverse_eq_map_id,
  naturality := @option.naturality }

section list

variables {F : Type u → Type v}
variables [applicative F]

open applicative functor
open list (cons)

protected def list.traverse {α β} (f : α → F β) : list α → F (list β)
| [] := pure []
| (x :: xs) := cons <$> f x <*> list.traverse xs

end list

section list

variables {F G : Type u → Type u}
variables [applicative F] [applicative G]
variables [is_lawful_applicative F] [is_lawful_applicative G]

open applicative functor
open list (cons)

lemma list.id_traverse {α} (xs : list α) :
  list.traverse id.mk xs = xs :=
by induction xs; simp! * with functor_norm; refl

lemma list.comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : list α) :
  list.traverse (comp.mk ∘ (<$>) f ∘ g) x =
  comp.mk (list.traverse f <$> list.traverse g x) :=
by induction x; simp! * with functor_norm; refl

lemma list.traverse_eq_map_id {α β} (f : α → β) (x : list α) :
  list.traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
by induction x; simp! * with functor_norm; refl

variable (η : applicative_transformation F G)

lemma list.naturality {α β} (f : α → F β) (x : list α) :
  η (list.traverse f x) = list.traverse (@η _ ∘ f) x :=
by induction x; simp! * with functor_norm
open nat

end list

instance : traversable list := ⟨@list.traverse⟩

instance : is_lawful_traversable list :=
{ id_traverse := @list.id_traverse,
  comp_traverse := @list.comp_traverse,
  traverse_eq_map_id := @list.traverse_eq_map_id,
  naturality := @list.naturality }

namespace sum

section traverse
variables {σ : Type u}
variables {F G : Type u → Type u}
variables [applicative F] [applicative G]

open applicative functor
open list (cons)

protected def traverse {α β} (f : α → F β) : σ ⊕ α → F (σ ⊕ β)
| (sum.inl x) := pure (sum.inl x)
| (sum.inr x) := sum.inr <$> f x

variables [is_lawful_applicative F] [is_lawful_applicative G]

protected lemma id_traverse {σ α} (x : σ ⊕ α) : sum.traverse id.mk x = x :=
by cases x; refl

protected lemma comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : σ ⊕ α) :
  sum.traverse (comp.mk ∘ (<$>) f ∘ g) x =
  comp.mk (sum.traverse f <$> sum.traverse g x) :=
by cases x; simp! [sum.traverse,map_id] with functor_norm; refl

protected lemma traverse_eq_map_id {α β} (f : α → β) (x : σ ⊕ α) :
  sum.traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
by induction x; simp! * with functor_norm; refl

protected lemma map_traverse {α β γ} (g : α → G β) (f : β → γ) (x : σ ⊕ α) :
  (<$>) f <$> sum.traverse g x = sum.traverse ((<$>) f ∘ g) x :=
by cases x; simp [(<$>), sum.mapr, sum.traverse, id_map] with functor_norm; congr

protected lemma traverse_map {α β γ : Type u} (g : α → β) (f : β → G γ) (x : σ ⊕ α) :
  sum.traverse f (g <$> x) = sum.traverse (f ∘ g) x :=
by cases x; simp [(<$>), sum.mapr, sum.traverse, id_map] with functor_norm

variable (η : applicative_transformation F G)

protected lemma naturality {α β} (f : α → F β) (x : σ ⊕ α) :
  η (sum.traverse f x) = sum.traverse (@η _ ∘ f) x :=
by cases x; simp! [sum.traverse] with functor_norm

end traverse

instance {σ : Type u} : traversable.{u} (sum σ) := ⟨@sum.traverse _⟩

instance {σ : Type u} : is_lawful_traversable.{u} (sum σ) :=
{ id_traverse := @sum.id_traverse σ,
  comp_traverse := @sum.comp_traverse σ,
  traverse_eq_map_id := @sum.traverse_eq_map_id σ,
  naturality := @sum.naturality σ }

end sum
