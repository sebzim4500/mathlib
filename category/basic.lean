/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends the theory on functors, applicatives and monads.
-/

universes u v
variables {α β γ : Type u}

notation a ` $< `:1 f:1 := f a

section functor
variables {f : Type u → Type v} [functor f] [is_lawful_functor f]

run_cmd mk_simp_attr `functor_norm

@[functor_norm] protected theorem map_map (m : α → β) (g : β → γ) (x : f α) :
  g <$> (m <$> x) = (g ∘ m) <$> x :=
(comp_map _ _ _).symm

@[simp] theorem id_map' (x : f α) : (λa, a) <$> x = x := id_map _

end functor

section applicative
variables {F : Type u → Type v} [applicative F]

def mzip_with
  {α₁ α₂ φ : Type u}
  (f : α₁ → α₂ → F φ) :
  Π (ma₁ : list α₁) (ma₂: list α₂), F (list φ)
| (x :: xs) (y :: ys) := (::) <$> f x y <*> mzip_with xs ys
| _ _ := pure []

def mzip_with'  (f : α → β → F γ) : list α → list β → F punit
| (x :: xs) (y :: ys) := f x y *> mzip_with' xs ys
| [] _ := pure punit.star
| _ [] := pure punit.star

protected def option.traverse {α β : Type*} (f : α → F β) : option α → F (option β)
| none := pure none
| (some x) := some <$> f x

protected def list.traverse {α β : Type*} (f : α → F β) : list α → F (list β)
| [] := pure []
| (x :: xs) := list.cons <$> f x <*> list.traverse xs

variables [is_lawful_applicative F]

attribute [functor_norm] seq_assoc pure_seq_eq_map

@[simp] theorem pure_id'_seq (x : F α) : pure (λx, x) <*> x = x :=
pure_id_seq x

variables  [is_lawful_applicative F]

attribute [functor_norm] seq_assoc pure_seq_eq_map

@[functor_norm] theorem seq_map_assoc (x : F (α → β)) (f : γ → α) (y : F γ) :
  (x <*> (f <$> y)) = (λ(m:α→β), m ∘ f) <$> x <*> y :=
begin
  simp [(pure_seq_eq_map _ _).symm],
  simp [seq_assoc, (comp_map _ _ _).symm, (∘)],
  simp [pure_seq_eq_map]
end

@[functor_norm] theorem map_seq (f : β → γ) (x : F (α → β)) (y : F α) :
  (f <$> (x <*> y)) = ((∘) f) <$> x <*> y :=
by simp [(pure_seq_eq_map _ _).symm]; simp [seq_assoc]

end applicative

-- TODO: setup `functor_norm` for `monad` laws
section monad
variables {m : Type u → Type v} [monad m] [is_lawful_monad m]

open list

def list.mpartition {f : Type → Type} [monad f] {α : Type} (p : α → f bool) :
  list α → f (list α × list α)
| [] := pure ([],[])
| (x :: xs) :=
mcond (p x) (prod.map (cons x) id <$> list.mpartition xs)
            (prod.map id (cons x) <$> list.mpartition xs)

lemma map_bind (x : m α) {g : α → m β} {f : β → γ} : f <$> (x >>= g) = (x >>= λa, f <$> g a) :=
by rw [← bind_pure_comp_eq_map,bind_assoc]; simp [bind_pure_comp_eq_map]

lemma seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} : (f <$> x) >>= g = (x >>= g ∘ f) :=
show bind (f <$> x) g = bind x (g ∘ f),
by rw [← bind_pure_comp_eq_map, bind_assoc]; simp [pure_bind]

lemma seq_eq_bind_map {x : m α} {f : m (α → β)} : f <*> x = (f >>= (<$> x)) :=
(bind_map_eq_seq m f x).symm

end monad

section alternative
variables {F : Type → Type v} [alternative F]

def succeeds {α} (x : F α) : F bool := (x $> tt) <|> pure ff

def mtry {α} (x : F α) : F unit := (x $> ()) <|> pure ()

@[simp] theorem guard_true {h : decidable true} :
  @guard F _ true h = pure () := by simp [guard]

@[simp] theorem guard_false {h : decidable false} :
  @guard F _ false h = failure := by simp [guard]

end alternative

namespace sum

variables {e : Type v}

protected def bind {α β} : e ⊕ α → (α → e ⊕ β) → e ⊕ β
| (inl x) _ := inl x
| (inr x) f := f x

instance : monad (sum.{v u} e) :=
{ pure := @sum.inr e,
  bind := @sum.bind e }

instance : is_lawful_functor (sum.{v u} e) :=
by refine { .. }; intros; cases x; refl

instance : is_lawful_monad (sum.{v u} e) :=
{ bind_assoc := by { intros, cases x; refl },
  pure_bind  := by { intros, refl },
  bind_pure_comp_eq_map := by { intros, cases x; refl },
  bind_map_eq_seq := by { intros, cases f; refl } }

end sum

class is_comm_applicative (m : Type* → Type*) [applicative m] extends is_lawful_applicative m : Prop :=
(commutative_prod : ∀{α β} (a : m α) (b : m β), prod.mk <$> a <*> b = (λb a, (a, b)) <$> b <*> a)

lemma is_comm_applicative.commutative_map
  {m : Type* → Type*} [applicative m] [is_comm_applicative m]
  {α β γ} (a : m α) (b : m β) {f : α → β → γ} :
  f <$> a <*> b = flip f <$> b <*> a :=
calc f <$> a <*> b = (λp:α×β, f p.1 p.2) <$> (prod.mk <$> a <*> b) :
    by simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map]
  ... = (λb a, f a b) <$> b <*> a :
    by rw [is_comm_applicative.commutative_prod];
        simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map]
