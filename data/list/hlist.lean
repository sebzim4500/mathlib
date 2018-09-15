import data.list.basic data.erased

universes u v

def type_list := erased (list (Type u))

inductive hlist_cell (α β : Type*)
| nil {} : hlist_cell
| cons : α → β → hlist_cell

namespace type_list

def nil : type_list := erased.mk []

def cons (α : Type u) (U : type_list) : type_list :=
erased.mk (α :: U.out)

@[simp] theorem nil_out : nil.out = [] := erased.out_mk _

@[simp] theorem cons_out {α U} : (cons α U).out = α :: U.out := erased.out_mk _

def len_lt (U V : type_list) := U.out.length < V.out.length

theorem len_lt_wf : well_founded len_lt := measure_wf _

instance : has_well_founded type_list := ⟨_, len_lt_wf⟩

instance : has_coe (list (Type u)) type_list := ⟨erased.mk⟩

end type_list

def hlist_aux : list (Type u) → Σ α β : Type u, (hlist_cell α β → Prop)
| [] := ⟨punit, punit, λ a, a = hlist_cell.nil⟩
| (α :: U) := let T := hlist_aux U in
  ⟨α, subtype T.2.2, λ x, ∃ a b, x = hlist_cell.cons a b⟩

def hlist_aux' (U : type_list) : Σ α β : Type u, (hlist_cell α β → Prop) :=
⟨(hlist_aux U.out).1, (hlist_aux U.out).2.1, (hlist_aux U.out).2.2⟩

/--
The type of heterogeneous lists. The type is morally given by the definition:
```
inductive hlist : list (Type u) → Type u
| nil : hlist []
| cons {α U} : α → hlist U → hlist (α :: U)
```
but this both puts `hlist` in a higher universe than desired and also
adds a data field `list (Type u)` which is stored in memory as a linked
list of units (the types). To avoid this problem we use `type_list`
instead, which is the same as `list (Type u)` but it is completely erased.
-/
def hlist (l : type_list.{u}) : Type u :=
let T := hlist_aux' l in subtype T.2.2

theorem hlist_eq (l : type_list.{u}) :
  ∀ {l'}, l.out = l' → hlist l = subtype (hlist_aux l').2.2
| _ rfl := rfl

theorem hlist_eq_mpr_fst (l : type_list.{u}) :
  ∀ {l'} (h : l.out = l') (a b),
    (eq.mpr (hlist_eq _ h) ⟨a, b⟩).1 = (by rw [hlist_aux', h]; exact a)
| _ rfl a b := rfl

def hlist.nil : hlist type_list.nil.{u} :=
eq.mpr (hlist_eq _ type_list.nil_out) ⟨_, rfl⟩

def hlist.cons {α U} (a : α) (l : hlist U) : hlist (type_list.cons α U) :=
eq.mpr (hlist_eq _ type_list.cons_out) ⟨_, a, l, rfl⟩

theorem hlist.nil_eq (l : list (Type u)) (h : (hlist_aux l).2.2 hlist_cell.nil) :
  type_list.nil.out = l ∧ hlist.nil.{u} == subtype.mk hlist_cell.nil h :=
begin
  cases l with a l,
  { exact ⟨type_list.nil_out, eq_rec_heq _ _⟩ },
  { rcases h with ⟨a, b, e⟩, injection e }
end

def hlist.head_ty : ∀ (l : list (Type u)) {a b},
  (hlist_aux l).2.2 (hlist_cell.cons a b) → Type u
| (α::U) a b h := α

def hlist.head_ty' (U : type_list) : ∀ {a b},
  (hlist_aux' U).2.2 (hlist_cell.cons a b) → Type u :=
@hlist.head_ty U.out

def hlist.tail_ty : ∀ (l : list (Type u)) {a b},
  (hlist_aux l).2.2 (hlist_cell.cons a b) → list (Type u)
| (α::U) a b h := U

def hlist.tail_ty' (U : type_list) {a b}
  (h : (hlist_aux' U).2.2 (hlist_cell.cons a b)) : type_list :=
erased.mk (hlist.tail_ty U.out h)

theorem hlist.cons_eq (l : list (Type u)) {a b}
  (h : (hlist_aux l).2.2 (hlist_cell.cons a b)) :
  ∃ (h₁ : (hlist_aux l).fst = hlist.head_ty l h),
  ∃ (h₂ : ((hlist_aux l).snd).fst = hlist (hlist.tail_ty l h)),
  (type_list.cons (hlist.head_ty l h) (hlist.tail_ty l h)) = erased.mk l ∧
  (hlist.cons (eq.mp h₁ a) (eq.mp h₂ b)) ==
    @subtype.mk _ (hlist_aux l).2.2 (hlist_cell.cons a b) h :=
begin
  cases l with a l,
  { exact ⟨type_list.nil_out, eq_rec_heq _ _⟩ },
  { rcases h with ⟨a, b, e⟩, injection e }
end


theorem hlist.rec_on_proof_1 (C : Π (U : type_list), hlist U → Sort v)
  {U : type_list} (h : (hlist_aux' U).2.2 hlist_cell.nil) :
  C type_list.nil hlist.nil =
  C U ⟨@hlist_cell.nil _ (((hlist_aux' U).snd).fst), h⟩ :=
begin
  cases hlist.nil_eq _ h with h₁ h₂,
  have := erased.out_bijective.1 h₁,
  clear_, subst U,
  rw eq_of_heq h₂
end

theorem hlist.rec_on_proof_2 (C : Π (U : type_list), hlist U → Sort v)
  {U : type_list} {a b}
  (h : (hlist_aux' U).2.2 (hlist_cell.cons a b)) :
  (hlist_aux' U).fst = hlist.head_ty' U h :=
sorry

theorem hlist.rec_on_proof_3 (C : Π (U : type_list), hlist U → Sort v)
  {U : type_list} {a b}
  (h : (hlist_aux' U).2.2 (hlist_cell.cons a b)) :
  ((hlist_aux' U).snd).fst = hlist (hlist.tail_ty' U h) :=
sorry

theorem hlist.rec_on_proof_4 (C : Π (U : type_list), hlist U → Sort v)
  {U : type_list} {a b}
  (h : (hlist_aux' U).2.2 (hlist_cell.cons a b)) :
    let a' := eq.mp (hlist.rec_on_proof_2 C h) a,
        l' := eq.mp (hlist.rec_on_proof_3 C h) b in
    C (type_list.cons (hlist.head_ty' U h)
    (hlist.tail_ty' U h)) (hlist.cons a' l') =
    C U ⟨hlist_cell.cons a b, h⟩ :=
  /-
      cases H.snd.snd with h₁ h₂,
      rw erased.mk_out at h₁,
      congr, {exact h₁},
      exact h₂
    end
  -/
_

theorem hlist.rec_on_proof_5 (C : Π (U : type_list), hlist U → Sort v)
  {U : type_list} {a b}
  (h : (hlist_aux' U).2.2 (hlist_cell.cons a b)) :
    type_list.len_lt (hlist.tail_ty' U h) U :=
  /-
      cases H.snd.snd with h₁ h₂,
      rw erased.mk_out at h₁,
      congr, {exact h₁},
      exact h₂
    end
  -/
_

def hlist.rec_on {C : ∀ U, hlist U → Sort v} : ∀ {U} (l : hlist U)
  (H1 : C _ hlist.nil)
  (H2 : ∀ α U a l, C _ l → C _ (@hlist.cons α U a l)), C U l
| U := λ l H1 H2, match l with
  | ⟨hlist_cell.nil, h⟩ := eq.mp (hlist.rec_on_proof_1 C h) H1
  | ⟨hlist_cell.cons a l, h⟩ :=
    let a' := eq.mp (hlist.rec_on_proof_2 C h) a,
        l' := eq.mp (hlist.rec_on_proof_3 C h) l in
    have _, from hlist.rec_on_proof_5 C h,
    eq.mp (hlist.rec_on_proof_4 C h)
      (H2 _ _ a' l' (hlist.rec_on l' H1 H2))
  end
using_well_founded {dec_tac := `[assumption]}

namespace hlist
variable {α : Type u}
open list

def map_to_list : ∀ {U : erased (list (Type v))}, (∀ β ∈ U, β → α) → hlist U → list α
| []       f l := []
| (α :: U) f l := f α (or.inl rfl) l.1 :: map_to_list (λ β h, f β (or.inr h)) l.2

def to_list (n) : hlist (repeat α n) → list α :=
map_to_list (λ β h, cast (eq_of_mem_repeat h))

def map (F : Type u → Type v) (f : ∀ {α}, α → F α) :
  ∀ {U : list (Type u)}, hlist U → hlist (map F U)
| []       _ := punit.star
| (α :: U) (a, l) := (f a, map l)

def sigma {U : list (Type u)} : hlist U → list (Σ α, α) :=
map_to_list $ λ α _ a, ⟨α, a⟩

def map_of_list : ∀ {U : list (Type v)}, (∀ β ∈ U, α → β) →
  ∀ l : list α, length l = length U → hlist U
| []       f l        h := punit.star
| (α :: U) f (a :: l) h :=
  (f α (or.inl rfl) a,
   map_of_list (λ β h, f β (or.inr h)) l (nat.succ_inj h))

end hlist