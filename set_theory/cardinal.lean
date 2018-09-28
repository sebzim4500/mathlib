/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Mario Carneiro

Cardinal arithmetic.

Cardinals are represented as quotient over equinumerous types.
-/

import data.set.finite data.quot logic.schroeder_bernstein logic.function

open function lattice set
local attribute [instance] classical.prop_decidable

universes u v w x

instance cardinal.is_equivalent : setoid (Type u) :=
{ r := λα β, nonempty (α ≃ β),
  iseqv := ⟨λα,
    ⟨equiv.refl α⟩,
    λα β ⟨e⟩, ⟨e.symm⟩,
    λα β γ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

/-- `cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
def cardinal : Type (u + 1) := quotient cardinal.is_equivalent

namespace cardinal

/-- The cardinal of a type -/
def mk : Type u → cardinal := quotient.mk

@[simp] theorem mk_def (α : Type u) : @eq cardinal ⟦α⟧ (mk α) := rfl

@[simp] theorem mk_out (c : cardinal) : mk (c.out) = c := quotient.out_eq _

instance : has_le cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, nonempty $ α ↪ β) $
  assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
    propext ⟨assume ⟨e⟩, ⟨e.congr e₁ e₂⟩, assume ⟨e⟩, ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

theorem le_mk_iff_exists_set {c : cardinal} {α : Type u} :
  c ≤ mk α ↔ ∃ p : set α, mk p = c :=
⟨quotient.induction_on c $ λ β ⟨⟨f, hf⟩⟩,
  ⟨set.range f, eq.symm $ quot.sound ⟨equiv.set.range f hf⟩⟩,
λ ⟨p, e⟩, e ▸ ⟨⟨subtype.val, λ a b, subtype.eq⟩⟩⟩

instance : linear_order cardinal.{u} :=
{ le          := (≤),
  le_refl     := by rintros ⟨α⟩; exact ⟨embedding.refl _⟩,
  le_trans    := by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.trans e₂⟩,
  le_antisymm := by rintros ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩; exact quotient.sound (e₁.antisymm e₂),
  le_total    := by rintros ⟨α⟩ ⟨β⟩; exact embedding.total }

noncomputable instance : decidable_linear_order cardinal.{u} := classical.DLO _

noncomputable instance : distrib_lattice cardinal.{u} := by apply_instance

instance : has_zero cardinal.{u} := ⟨⟦pempty⟧⟩

instance : inhabited cardinal.{u} := ⟨0⟩

theorem ne_zero_iff_nonempty {α : Type u} : mk α ≠ 0 ↔ nonempty α :=
not_iff_comm.1
  ⟨λ h, quotient.sound ⟨(equiv.empty_of_not_nonempty h).trans equiv.empty_equiv_pempty⟩,
   λ e, let ⟨h⟩ := quotient.exact e in λ ⟨a⟩, (h a).elim⟩

instance : has_one cardinal.{u} := ⟨⟦punit⟧⟩

instance : zero_ne_one_class cardinal.{u} :=
{ zero := 0, one := 1, zero_ne_one :=
  ne.symm $ ne_zero_iff_nonempty.2 ⟨punit.star⟩ }

theorem le_one_iff_subsingleton {α : Type u} : mk α ≤ 1 ↔ subsingleton α :=
⟨λ ⟨f⟩, ⟨λ a b, f.inj (subsingleton.elim _ _)⟩,
 λ ⟨h⟩, ⟨⟨λ a, punit.star, λ a b _, h _ _⟩⟩⟩

instance : has_add cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, mk (α ⊕ β)) $ assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.sum_congr e₁ e₂⟩⟩

@[simp] theorem add_def (α β) : mk α + mk β = mk (α ⊕ β) := rfl

instance : has_mul cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, mk (α × β)) $ assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.prod_congr e₁ e₂⟩⟩

@[simp] theorem mul_def (α β) : mk α * mk β = mk (α × β) := rfl

private theorem add_comm (a b : cardinal.{u}) : a + b = b + a :=
quotient.induction_on₂ a b $ assume α β, quotient.sound ⟨equiv.sum_comm α β⟩

private theorem mul_comm (a b : cardinal.{u}) : a * b = b * a :=
quotient.induction_on₂ a b $ assume α β, quotient.sound ⟨equiv.prod_comm α β⟩

private theorem zero_add (a : cardinal.{u}) : 0 + a = a :=
quotient.induction_on a $ assume α, quotient.sound ⟨equiv.pempty_sum α⟩

private theorem zero_mul (a : cardinal.{u}) : 0 * a = 0 :=
quotient.induction_on a $ assume α, quotient.sound ⟨equiv.pempty_prod α⟩

private theorem one_mul (a : cardinal.{u}) : 1 * a = a :=
quotient.induction_on a $ assume α, quotient.sound ⟨equiv.punit_prod α⟩

private theorem left_distrib (a b c : cardinal.{u}) : a * (b + c) = a * b + a * c :=
quotient.induction_on₃ a b c $ assume α β γ, quotient.sound ⟨equiv.prod_sum_distrib α β γ⟩

instance : comm_semiring cardinal.{u} :=
{ zero          := 0,
  one           := 1,
  add           := (+),
  mul           := (*),
  zero_add      := zero_add,
  add_zero      := assume a, by rw [add_comm a 0, zero_add a],
  add_assoc     := λa b c, quotient.induction_on₃ a b c $ assume α β γ,
    quotient.sound ⟨equiv.sum_assoc α β γ⟩,
  add_comm      := add_comm,
  zero_mul      := zero_mul,
  mul_zero      := assume a, by rw [mul_comm a 0, zero_mul a],
  one_mul       := one_mul,
  mul_one       := assume a, by rw [mul_comm a 1, one_mul a],
  mul_assoc     := λa b c, quotient.induction_on₃ a b c $ assume α β γ,
    quotient.sound ⟨equiv.prod_assoc α β γ⟩,
  mul_comm      := mul_comm,
  left_distrib  := left_distrib,
  right_distrib := assume a b c,
    by rw [mul_comm (a + b) c, left_distrib c a b, mul_comm c a, mul_comm c b] }

/-- The cardinal exponential. `mk α ^ mk β` is the cardinal of `β → α`. -/
protected def power (a b : cardinal.{u}) : cardinal.{u} :=
quotient.lift_on₂ a b (λα β, mk (β → α)) $ assume α₁ α₂ β₁ β₂ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.arrow_congr e₂ e₁⟩

instance : has_pow cardinal cardinal := ⟨cardinal.power⟩
local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow

@[simp] theorem power_def (α β) : mk α ^ mk β = mk (β → α) := rfl

@[simp] theorem power_zero {a : cardinal} : a ^ 0 = 1 :=
quotient.induction_on a $ assume α, quotient.sound
⟨equiv.pempty_arrow_equiv_punit α⟩

@[simp] theorem power_one {a : cardinal} : a ^ 1 = a :=
quotient.induction_on a $ assume α, quotient.sound
⟨equiv.punit_arrow_equiv α⟩

@[simp] theorem one_power {a : cardinal} : 1 ^ a = 1 :=
quotient.induction_on a $ assume α, quotient.sound
⟨equiv.arrow_punit_equiv_punit α⟩

@[simp] theorem prop_eq_two : mk (ulift Prop) = 2 :=
quot.sound ⟨equiv.ulift.trans $ equiv.Prop_equiv_bool.trans equiv.bool_equiv_punit_sum_punit⟩

@[simp] theorem zero_power {a : cardinal} : a ≠ 0 → 0 ^ a = 0 :=
quotient.induction_on a $ assume α heq,
nonempty.rec_on (ne_zero_iff_nonempty.1 heq) $ assume a,
quotient.sound ⟨equiv.equiv_pempty $ assume f, pempty.rec (λ _, false) (f a)⟩

theorem power_ne_zero {a : cardinal} (b) : a ≠ 0 → a ^ b ≠ 0 :=
quotient.induction_on₂ a b $ λ α β h,
let ⟨a⟩ := ne_zero_iff_nonempty.1 h in
ne_zero_iff_nonempty.2 ⟨λ _, a⟩

theorem mul_power {a b c : cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_prod_equiv_prod_arrow α β γ⟩

theorem power_add {a b c : cardinal} : a ^ (b + c) = a ^ b * a ^ c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.sum_arrow_equiv_prod_arrow β γ α⟩

theorem power_mul {a b c : cardinal} : (a ^ b) ^ c = a ^ (b * c) :=
by rw [_root_.mul_comm b c];
from (quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_arrow_equiv_prod_arrow γ β α⟩)

section order_properties
open sum

theorem zero_le : ∀(a : cardinal), 0 ≤ a :=
by rintro ⟨α⟩; exact ⟨embedding.of_not_nonempty $ λ ⟨a⟩, a.elim⟩

theorem le_zero (a : cardinal) : a ≤ 0 ↔ a = 0 :=
by simp [le_antisymm_iff, zero_le]

theorem pos_iff_ne_zero {o : cardinal} : 0 < o ↔ o ≠ 0 :=
by simp [lt_iff_le_and_ne, eq_comm, zero_le]

theorem zero_lt_one : (0 : cardinal) < 1 :=
lt_of_le_of_ne (zero_le _) zero_ne_one

theorem add_le_add : ∀{a b c d : cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨embedding.sum_congr e₁ e₂⟩

theorem add_le_add_left (a) {b c : cardinal} : b ≤ c → a + b ≤ a + c :=
add_le_add (le_refl _)

theorem add_le_add_right {a b : cardinal} (c) (h : a ≤ b) : a + c ≤ b + c :=
add_le_add h (le_refl _)

theorem le_add_right (a b : cardinal) : a ≤ a + b :=
by simpa using add_le_add_left a (zero_le b)

theorem le_add_left (a b : cardinal) : a ≤ b + a :=
by simpa using add_le_add_right a (zero_le b)

theorem mul_le_mul : ∀{a b c d : cardinal}, a ≤ b → c ≤ d → a * c ≤ b * d :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨embedding.prod_congr e₁ e₂⟩

theorem mul_le_mul_left (a) {b c : cardinal} : b ≤ c → a * b ≤ a * c :=
mul_le_mul (le_refl _)

theorem mul_le_mul_right {a b : cardinal} (c) (h : a ≤ b) : a * c ≤ b * c :=
mul_le_mul h (le_refl _)

theorem power_le_power_left : ∀{a b c : cardinal}, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩; exact
  let ⟨a⟩ := ne_zero_iff_nonempty.1 hα in
  ⟨@embedding.arrow_congr_right _ _ _ ⟨a⟩ e⟩

theorem power_le_power_right {a b c : cardinal} : a ≤ b → a ^ c ≤ b ^ c :=
quotient.induction_on₃ a b c $ assume α β γ ⟨e⟩, ⟨embedding.arrow_congr_left e⟩

theorem le_iff_exists_add {a b : cardinal} : a ≤ b ↔ ∃ c, b = a + c :=
⟨quotient.induction_on₂ a b $ λ α β ⟨⟨f, hf⟩⟩,
  have (α ⊕ ↥-range f) ≃ β, from
    (equiv.sum_congr (equiv.set.range f hf) (equiv.refl _)).trans $
    (equiv.set.sum_compl (range f)),
  ⟨⟦(-range f : set β)⟧, quotient.sound ⟨this.symm⟩⟩,
 λ ⟨c, e⟩, add_zero a ▸ e.symm ▸ add_le_add_left _ (zero_le _)⟩

end order_properties

instance : canonically_ordered_monoid cardinal.{u} :=
{ add_le_add_left       := λ a b h c, add_le_add_left _ h,
  lt_of_add_lt_add_left := λ a b c, le_imp_le_iff_lt_imp_lt.1 (add_le_add_left _),
  le_iff_exists_add     := @le_iff_exists_add,
  ..cardinal.comm_semiring, ..cardinal.linear_order }

instance : order_bot cardinal.{u} :=
{ bot := 0, bot_le := zero_le, ..cardinal.linear_order }

theorem cantor : ∀(a : cardinal.{u}), a < 2 ^ a :=
by rw ← prop_eq_two; rintros ⟨a⟩; exact ⟨
  ⟨⟨λ a b, ⟨a = b⟩, λ a b h, cast (ulift.up.inj (@congr_fun _ _ _ _ h b)).symm rfl⟩⟩,
  λ ⟨⟨f, hf⟩⟩, cantor_injective (λ s, f (λ a, ⟨s a⟩)) $
    λ s t h, by funext a; injection congr_fun (hf h) a⟩

instance : no_top_order cardinal.{u} :=
{ no_top := λ a, ⟨_, cantor a⟩, ..cardinal.linear_order }

/-- The minimum cardinal in a family of cardinals (the existence
  of which is provided by `injective_min`). -/
noncomputable def min {ι} (I : nonempty ι) (f : ι → cardinal) : cardinal :=
f $ classical.some $
@embedding.injective_min _ (λ i, (f i).out) I

theorem min_eq {ι} (I) (f : ι → cardinal) : ∃ i, min I f = f i :=
⟨_, rfl⟩

theorem min_le {ι I} (f : ι → cardinal) (i) : min I f ≤ f i :=
by rw [← mk_out (min I f), ← mk_out (f i)]; exact
let ⟨g⟩ := classical.some_spec
  (@embedding.injective_min _ (λ i, (f i).out) I) in
⟨g i⟩

theorem le_min {ι I} {f : ι → cardinal} {a} : a ≤ min I f ↔ ∀ i, a ≤ f i :=
⟨λ h i, le_trans h (min_le _ _),
 λ h, let ⟨i, e⟩ := min_eq I f in e.symm ▸ h i⟩

protected theorem wf : @well_founded cardinal.{u} (<) :=
⟨λ a, classical.by_contradiction $ λ h,
  let ι := {c :cardinal // ¬ acc (<) c},
      f : ι → cardinal := subtype.val,
      ⟨⟨c, hc⟩, hi⟩ := @min_eq ι ⟨⟨_, h⟩⟩ f in
    hc (acc.intro _ (λ j ⟨_, h'⟩,
      classical.by_contradiction $ λ hj, h' $
      by have := min_le f ⟨j, hj⟩; rwa hi at this))⟩

instance has_wf : @has_well_founded cardinal.{u} := ⟨(<), cardinal.wf⟩

instance wo : @is_well_order cardinal.{u} (<) := ⟨cardinal.wf⟩

/-- The successor cardinal - the smallest cardinal greater than
  `c`. This is not the same as `c + 1` except in the case of finite `c`. -/
noncomputable def succ (c : cardinal) : cardinal :=
@min {c' // c < c'} ⟨⟨_, cantor _⟩⟩ subtype.val

theorem lt_succ_self (c : cardinal) : c < succ c :=
by cases min_eq _ _ with s e; rw [succ, e]; exact s.2

theorem succ_le {a b : cardinal} : succ a ≤ b ↔ a < b :=
⟨lt_of_lt_of_le (lt_succ_self _), λ h,
  by exact min_le _ (subtype.mk b h)⟩

theorem lt_succ {a b : cardinal} : a < succ b ↔ a ≤ b :=
by rw [← not_le, succ_le, not_lt]

theorem add_one_le_succ (c : cardinal) : c + 1 ≤ succ c :=
begin
  refine quot.induction_on c (λ α, _) (lt_succ_self c),
  refine quot.induction_on (succ (quot.mk setoid.r α)) (λ β h, _),
  cases h.left with f,
  have : ¬ surjective f := λ hn,
    ne_of_lt h (quotient.sound ⟨equiv.of_bijective ⟨f.inj, hn⟩⟩),
  cases classical.not_forall.1 this with b nex,
  refine ⟨⟨sum.rec (by exact f) _, _⟩⟩,
  { exact λ _, b },
  { intros a b h, rcases a with a|⟨⟨⟨⟩⟩⟩; rcases b with b|⟨⟨⟨⟩⟩⟩,
    { rw f.inj h },
    { exact nex.elim ⟨_, h⟩ },
    { exact nex.elim ⟨_, h.symm⟩ },
    { refl } }
end

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → cardinal) : cardinal := mk Σ i, (f i).out

theorem le_sum {ι} (f : ι → cardinal) (i) : f i ≤ sum f :=
by rw ← quotient.out_eq (f i); exact
⟨⟨λ a, ⟨i, a⟩, λ a b h, eq_of_heq $ by injection h⟩⟩

@[simp] theorem sum_mk {ι} (f : ι → Type*) : sum (λ i, mk (f i)) = mk (Σ i, f i) :=
quot.sound ⟨equiv.sigma_congr_right $ λ i,
  classical.choice $ quotient.exact $ quot.out_eq $ mk (f i)⟩

theorem sum_const (ι : Type u) (a : cardinal.{u}) : sum (λ _:ι, a) = mk ι * a :=
quotient.induction_on a $ λ α, by simp; exact
  quotient.sound ⟨equiv.sigma_equiv_prod _ _⟩

theorem sum_le_sum {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
⟨embedding.sigma_congr_right $ λ i, classical.choice $
  by have := H i; rwa [← quot.out_eq (f i), ← quot.out_eq (g i)] at this⟩

/-- The indexed supremum of cardinals is the smallest cardinal above
  everything in the family. -/
noncomputable def sup {ι} (f : ι → cardinal) : cardinal :=
@min {c // ∀ i, f i ≤ c} ⟨⟨sum f, le_sum f⟩⟩ (λ a, a.1)

theorem le_sup {ι} (f : ι → cardinal) (i) : f i ≤ sup f :=
by dsimp [sup]; cases min_eq _ _ with c hc; rw hc; exact c.2 i

theorem sup_le {ι} {f : ι → cardinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
⟨λ h i, le_trans (le_sup _ _) h,
 λ h, by dsimp [sup]; change a with (⟨a, h⟩:subtype _).1; apply min_le⟩

theorem sup_le_sup {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : sup f ≤ sup g :=
sup_le.2 $ λ i, le_trans (H i) (le_sup _ _)

theorem sup_le_sum {ι} (f : ι → cardinal) : sup f ≤ sum f :=
sup_le.2 $ le_sum _

theorem sum_le_sup {ι : Type u} (f : ι → cardinal.{u}) : sum f ≤ mk ι * sup.{u u} f :=
by rw ← sum_const; exact sum_le_sum _ _ (le_sup _)

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → cardinal) : cardinal := mk (Π i, (f i).out)

@[simp] theorem prod_mk {ι} (f : ι → Type*) : prod (λ i, mk (f i)) = mk (Π i, f i) :=
quot.sound ⟨equiv.Pi_congr_right $ λ i,
  classical.choice $ quotient.exact $ mk_out $ mk (f i)⟩

theorem prod_const (ι : Type u) (a : cardinal.{u}) : prod (λ _:ι, a) = a ^ mk ι :=
quotient.induction_on a $ by simp

theorem prod_le_prod {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
⟨embedding.Pi_congr_right $ λ i, classical.choice $
  by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

theorem prod_ne_zero {ι} (f : ι → cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 :=
begin
  conv in (f _) {rw ← mk_out (f i)},
  simp [prod, ne_zero_iff_nonempty, -mk_out, -ne.def],
  exact ⟨λ ⟨F⟩ i, ⟨F i⟩, λ h, ⟨λ i, classical.choice (h i)⟩⟩,
end

theorem prod_eq_zero {ι} (f : ι → cardinal) : prod f = 0 ↔ ∃ i, f i = 0 :=
not_iff_not.1 $ by simpa using prod_ne_zero f

/-- The universe lift operation on cardinals -/
def lift (c : cardinal.{u}) : cardinal.{max u v} :=
quotient.lift_on c (λ α, ⟦ulift α⟧) $ λ α β ⟨e⟩,
quotient.sound ⟨equiv.ulift.trans $ e.trans equiv.ulift.symm⟩

theorem lift_mk (α) : lift.{u v} (mk α) = mk (ulift.{v u} α) := rfl

theorem lift_umax : lift.{u (max u v)} = lift.{u v} :=
funext $ λ a, quot.induction_on a $ λ α,
quotient.sound ⟨equiv.ulift.trans equiv.ulift.symm⟩

theorem lift_id' (a : cardinal) : lift a = a :=
quot.induction_on a $ λ α, quot.sound ⟨equiv.ulift⟩

@[simp] theorem lift_id : ∀ a, lift.{u u} a = a := lift_id'.{u u}

@[simp] theorem lift_lift (a : cardinal) : lift.{(max u v) w} (lift.{u v} a) = lift.{u (max v w)} a :=
quot.induction_on a $ λ α,
quotient.sound ⟨equiv.ulift.trans $ equiv.ulift.trans equiv.ulift.symm⟩

theorem lift_mk_le {α : Type u} {β : Type v} :
  lift.{u (max v w)} (mk α) ≤ lift.{v (max u w)} (mk β) ↔ nonempty (α ↪ β) :=
⟨λ ⟨f⟩, ⟨embedding.congr equiv.ulift equiv.ulift f⟩,
 λ ⟨f⟩, ⟨embedding.congr equiv.ulift.symm equiv.ulift.symm f⟩⟩

theorem lift_mk_eq {α : Type u} {β : Type v} :
  lift.{u (max v w)} (mk α) = lift.{v (max u w)} (mk β) ↔ nonempty (α ≃ β) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨equiv.ulift.symm.trans $ f.trans equiv.ulift⟩,
 λ ⟨f⟩, ⟨equiv.ulift.trans $ f.trans equiv.ulift.symm⟩⟩

@[simp] theorem lift_le {a b : cardinal} : lift a ≤ lift b ↔ a ≤ b :=
quotient.induction_on₂ a b $ λ α β,
by rw ← lift_umax; exact lift_mk_le

@[simp] theorem lift_inj {a b : cardinal} : lift a = lift b ↔ a = b :=
by simp [le_antisymm_iff]

@[simp] theorem lift_lt {a b : cardinal} : lift a < lift b ↔ a < b :=
by simp [lt_iff_le_not_le, -not_le]

@[simp] theorem lift_zero : lift 0 = 0 :=
quotient.sound ⟨equiv.ulift.trans equiv.pempty_equiv_pempty⟩

@[simp] theorem lift_one : lift 1 = 1 :=
quotient.sound ⟨equiv.ulift.trans equiv.punit_equiv_punit⟩

@[simp] theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
quotient.induction_on₂ a b $ λ α β,
quotient.sound ⟨equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
quotient.induction_on₂ a b $ λ α β,
quotient.sound ⟨equiv.ulift.trans (equiv.prod_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_power (a b) : lift (a ^ b) = lift a ^ lift b :=
quotient.induction_on₂ a b $ λ α β,
quotient.sound ⟨equiv.ulift.trans (equiv.arrow_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_two_power (a) : lift (2 ^ a) = 2 ^ lift a :=
by simp [bit0]

@[simp] theorem lift_min {ι I} (f : ι → cardinal) : lift (min I f) = min I (lift ∘ f) :=
le_antisymm (le_min.2 $ λ a, lift_le.2 $ min_le _ a) $
let ⟨i, e⟩ := min_eq I (lift ∘ f) in
by rw e; exact lift_le.2 (le_min.2 $ λ j, lift_le.1 $
by have := min_le (lift ∘ f) j; rwa e at this)

theorem lift_down {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a → ∃ a', lift a' = b :=
quotient.induction_on₂ a b $ λ α β,
by dsimp; rw [← lift_id (mk β), ← lift_umax, ← lift_umax.{u v}, lift_mk_le]; exact
λ ⟨f⟩, ⟨mk (set.range f), eq.symm $ lift_mk_eq.2
  ⟨embedding.equiv_of_surjective
    (embedding.cod_restrict _ f set.mem_range_self)
    $ λ ⟨a, ⟨b, e⟩⟩, ⟨b, subtype.eq e⟩⟩⟩

theorem le_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
⟨λ h, let ⟨a', e⟩ := lift_down h in ⟨a', e, lift_le.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
⟨λ h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
      ⟨a', e, lift_lt.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_lt.2 h⟩

@[simp] theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
le_antisymm
  (le_of_not_gt $ λ h, begin
    rcases lt_lift_iff.1 h with ⟨b, e, h⟩,
    rw [lt_succ, ← lift_le, e] at h,
    exact not_lt_of_le h (lt_succ_self _)
  end)
  (succ_le.2 $ lift_lt.2 $ lt_succ_self _)

/-- `ω` is the smallest infinite cardinal, also known as ℵ₀. -/
def omega : cardinal.{u} := lift (mk ℕ)

theorem omega_ne_zero : omega ≠ 0 :=
ne_zero_iff_nonempty.2 ⟨⟨0⟩⟩

theorem omega_pos : 0 < omega :=
pos_iff_ne_zero.2 omega_ne_zero

@[simp] theorem lift_omega : lift omega = omega := lift_lift _

@[simp] theorem mk_fin : ∀ (n : ℕ), mk (fin n) = n
| 0     := quotient.sound ⟨(equiv.pempty_of_not_nonempty $ λ ⟨h⟩, h.elim0)⟩
| (n+1) := by rw [nat.cast_succ, ← mk_fin]; exact
  quotient.sound (fintype.card_eq.1 $ by simp)

@[simp] theorem lift_nat_cast (n : ℕ) : lift n = n :=
by induction n; simp *

theorem lift_mk_fin (n : ℕ) : lift (mk (fin n)) = n := by simp

theorem fintype_card (α : Type u) [fintype α] : mk α = fintype.card α :=
by rw [← lift_mk_fin.{u}, ← lift_id (mk α), lift_mk_eq.{u 0 u}];
   exact fintype.card_eq.1 (by simp)

theorem card_le_of_finset {α} (s : finset α) :
  (s.card : cardinal) ≤ cardinal.mk α :=
begin
  rw (_ : (s.card : cardinal) = cardinal.mk (↑s : set α)),
  { exact ⟨function.embedding.subtype _⟩ },
  rw [cardinal.fintype_card, fintype.card_coe]
end

@[simp] theorem nat_cast_pow {m n : ℕ} : (↑(pow m n) : cardinal) = m ^ n :=
by induction n; simp [nat.pow_succ, -_root_.add_comm, power_add, *]

@[simp] theorem nat_cast_le {m n : ℕ} : (m : cardinal) ≤ n ↔ m ≤ n :=
by rw [← lift_mk_fin, ← lift_mk_fin, lift_le]; exact
⟨λ ⟨⟨f, hf⟩⟩, begin
  have : _ = fintype.card _ := finset.card_image_of_injective finset.univ hf,
  simp at this,
  rw [← fintype.card_fin n, ← this],
  exact finset.card_le_of_subset (finset.subset_univ _)
end,
λ h, ⟨⟨λ i, ⟨i.1, lt_of_lt_of_le i.2 h⟩, λ a b h,
  have _, from fin.veq_of_eq h, fin.eq_of_veq this⟩⟩⟩

@[simp] theorem nat_cast_lt {m n : ℕ} : (m : cardinal) < n ↔ m < n :=
by simp [lt_iff_le_not_le, -not_le]

@[simp] theorem nat_cast_inj {m n : ℕ} : (m : cardinal) = n ↔ m = n :=
by simp [le_antisymm_iff]

@[simp] theorem nat_succ (n : ℕ) : succ n = n.succ :=
le_antisymm (succ_le.2 $ nat_cast_lt.2 $ nat.lt_succ_self _) (add_one_le_succ _)

@[simp] theorem succ_zero : succ 0 = 1 :=
by simpa using nat_succ 0

theorem cantor' (a) {b : cardinal} (hb : 1 < b) : a < b ^ a :=
by rw [← succ_le, (by simpa using nat_succ 1 : succ 1 = 2)] at hb;
   exact lt_of_lt_of_le (cantor _) (power_le_power_right hb)

theorem one_le_iff_pos {c : cardinal} : 1 ≤ c ↔ 0 < c :=
by rw [← succ_zero, succ_le]

theorem one_le_iff_ne_zero {c : cardinal} : 1 ≤ c ↔ c ≠ 0 :=
by rw [one_le_iff_pos, pos_iff_ne_zero]

theorem nat_lt_omega (n : ℕ) : (n : cardinal.{u}) < omega :=
succ_le.1 $ by rw [nat_succ, ← lift_mk_fin, omega, lift_mk_le.{0 0 u}]; exact
⟨⟨fin.val, λ a b, fin.eq_of_veq⟩⟩

theorem one_lt_omega : 1 < omega :=
by simpa using nat_lt_omega 1

theorem lt_omega {c : cardinal.{u}} : c < omega ↔ ∃ n : ℕ, c = n :=
⟨λ h, begin
  rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩,
  rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩,
  suffices : finite S,
  { cases this, resetI,
    existsi fintype.card S,
    rw [← lift_nat_cast.{0 u}, lift_inj, fintype_card S] },
  by_contra nf,
  have P : ∀ (n : ℕ) (IH : ∀ i<n, S), ∃ a : S, ¬ ∃ y h, IH y h = a :=
    λ n IH,
    let g : {i | i < n} → S := λ ⟨i, h⟩, IH i h in
    classical.not_forall.1 (λ h, nf
      ⟨fintype.of_surjective g (λ a, subtype.exists.2 (h a))⟩),
  let F : ℕ → S := nat.lt_wf.fix (λ n IH, classical.some (P n IH)),
  refine not_le_of_lt h' ⟨⟨F, _⟩⟩,
  suffices : ∀ (n : ℕ) (m < n), F m ≠ F n,
  { refine λ m n, not_imp_not.1 (λ ne, _),
    rcases lt_trichotomy m n with h|h|h,
    { exact this n m h },
    { contradiction },
    { exact (this m n h).symm } },
  intros n m h,
  have := classical.some_spec (P n (λ y _, F y)),
  rw [← show F n = classical.some (P n (λ y _, F y)),
      from nat.lt_wf.fix_eq (λ n IH, classical.some (P n IH)) n] at this,
  exact λ e, this ⟨m, h, e⟩,
end, λ ⟨n, e⟩, e.symm ▸ nat_lt_omega _⟩

theorem omega_le {c : cardinal.{u}} : omega ≤ c ↔ ∀ n : ℕ, (n:cardinal) ≤ c :=
⟨λ h n, le_trans (le_of_lt (nat_lt_omega _)) h,
 λ h, le_of_not_lt $ λ hn, begin
  rcases lt_omega.1 hn with ⟨n, rfl⟩,
  exact not_le_of_lt (nat.lt_succ_self _) (nat_cast_le.1 (h (n+1)))
end⟩

theorem lt_omega_iff_fintype {α : Type u} : mk α < omega ↔ nonempty (fintype α) :=
lt_omega.trans ⟨λ ⟨n, e⟩, begin
  rw [← lift_mk_fin n] at e,
  cases quotient.exact e with f,
  exact ⟨fintype.of_equiv _ f.symm⟩
end, λ ⟨_⟩, by exactI ⟨_, fintype_card _⟩⟩

theorem lt_omega_iff_finite {α} {S : set α} : mk S < omega ↔ finite S :=
lt_omega_iff_fintype

theorem add_lt_omega {a b : cardinal} (ha : a < omega) (hb : b < omega) : a + b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_add]; apply nat_lt_omega
end

theorem mul_lt_omega {a b : cardinal} (ha : a < omega) (hb : b < omega) : a * b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_mul]; apply nat_lt_omega
end

theorem power_lt_omega {a b : cardinal} (ha : a < omega) (hb : b < omega) : a ^ b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat_cast_pow]; apply nat_lt_omega
end

/-- König's theorem -/
theorem sum_lt_prod {ι} (f g : ι → cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
lt_of_not_ge $ λ ⟨F⟩, begin
  have : inhabited (Π (i : ι), (g i).out),
  { refine ⟨λ i, classical.choice $ ne_zero_iff_nonempty.1 _⟩,
    rw mk_out,
    exact ne_of_gt (lt_of_le_of_lt (zero_le _) (H i)) }, resetI,
  let G := inv_fun F,
  have sG : surjective G := inv_fun_surjective F.2,
  have : ∀ i, ¬ ∀ b, ∃ a, G ⟨i, a⟩ i = b,
  { refine λ i h, not_le_of_lt (H i) _,
    rw [← mk_out (f i), ← mk_out (g i)],
    exact ⟨embedding.of_surjective h⟩ },
  simp [classical.not_forall] at this,
  exact let ⟨C, hc⟩ := classical.axiom_of_choice this, ⟨⟨i, a⟩, h⟩ := sG C in
  hc i a (congr_fun h _),
end

@[simp] theorem mk_empty : mk empty = 0 :=
fintype_card empty

@[simp] theorem mk_pempty : mk pempty = 0 :=
fintype_card pempty

@[simp] theorem mk_emptyc (α : Type u) : mk (∅ : set α) = 0 :=
quotient.sound ⟨equiv.set.pempty α⟩

@[simp] theorem mk_plift_of_false {p : Prop} (h : ¬ p) : mk (plift p) = 0 :=
quotient.sound ⟨equiv.plift.trans $ equiv.equiv_pempty h⟩

@[simp] theorem mk_unit : mk unit = 1 :=
(fintype_card unit).trans nat.cast_one

@[simp] theorem mk_punit : mk punit = 1 :=
(fintype_card punit).trans nat.cast_one

@[simp] theorem mk_singleton {α : Type u} (x : α) : mk ({x} : set α) = 1 :=
quotient.sound ⟨equiv.set.singleton x⟩

@[simp] theorem mk_plift_of_true {p : Prop} (h : p) : mk (plift p) = 1 :=
quotient.sound ⟨equiv.plift.trans $ equiv.prop_equiv_punit h⟩

@[simp] theorem mk_bool : mk bool = 2 :=
quotient.sound ⟨equiv.bool_equiv_punit_sum_punit⟩

@[simp] theorem mk_Prop : mk Prop = 2 :=
(quotient.sound ⟨equiv.Prop_equiv_bool⟩ : mk Prop = mk bool).trans mk_bool

@[simp] theorem mk_option {α : Type u} : mk (option α) = mk α + 1 :=
quotient.sound ⟨equiv.option_equiv_sum_punit α⟩

theorem mk_eq_of_injective {α β : Type u} {f : α → β} {s : set α} (hf : injective f) : mk (f '' s) = mk s :=
quotient.sound ⟨(equiv.set.image f s hf).symm⟩

theorem mk_list_eq_sum_pow (α : Type u) : mk (list α) = sum (λ n : ℕ, (mk α)^(n:cardinal.{u})) :=
calc  mk (list α)
    = mk (Σ n, vector α n) : quotient.sound ⟨equiv.equiv_sigma_subtype list.length⟩
... = mk (Σ n, fin n → α) : quotient.sound ⟨equiv.sigma_congr_right $ λ n,
  ⟨vector.nth, vector.of_fn, vector.of_fn_nth, λ f, funext $ vector.nth_of_fn f⟩⟩
... = mk (Σ n : ℕ, ulift.{u} (fin n) → α) : quotient.sound ⟨equiv.sigma_congr_right $ λ n,
  equiv.arrow_congr equiv.ulift.symm (equiv.refl α)⟩
... = sum (λ n : ℕ, (mk α)^(n:cardinal.{u})) : by simp only [(lift_mk_fin _).symm, lift_mk, power_def, sum_mk]

theorem mk_Union_le_sum_mk {α ι : Type u} {f : ι → set α} : mk (⋃ i, f i) ≤ sum (λ i, mk (f i)) :=
calc  mk (⋃ i, f i)
    ≤ mk (Σ i, f i) : show nonempty ((⋃ i, f i) ↪ (Σ i, f i)),
  from ⟨⟨λ x, ⟨classical.some (mem_Union.1 x.2), x.1, classical.some_spec (mem_Union.1 x.2)⟩,
  λ x y H, subtype.eq $ begin
    cases sigma.mk.inj H with H1 H2, clear H,
    generalize_hyp : classical.some_spec _ = H4 at H1 H2,
    generalize_hyp : classical.some _ = i₀ at H1 H2 H4,
    subst H1,
    exact subtype.mk.inj (eq_of_heq H2)
  end⟩⟩
... = sum (λ i, mk (f i)) : (sum_mk _).symm

@[simp] lemma finset_card {α : Type u} {s : finset α} : ↑(finset.card s) = mk (↑s : set α) :=
by rw [fintype_card, nat_cast_inj, fintype.card_coe]

theorem mk_union_add_mk_inter {α : Type u} {S T : set α} : mk (S ∪ T : set α) + mk (S ∩ T : set α) = mk S + mk T :=
quot.sound ⟨equiv.set.union_sum_inter S T⟩

theorem mk_union_of_disjoint {α : Type u} {S T : set α} (H : disjoint S T) : mk (S ∪ T : set α) = mk S + mk T :=
quot.sound ⟨equiv.set.union (disjoint_iff.1 H)⟩

end cardinal
