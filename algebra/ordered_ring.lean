/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import order.basic algebra.order algebra.ordered_group algebra.ring
       tactic.monotonicity.basic

universe u
variable {α : Type u}

-- TODO: this is necessary additionally to mul_nonneg otherwise the simplifier can not match
lemma zero_le_mul [ordered_semiring α] {a b : α} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
mul_nonneg

section linear_ordered_semiring
variable [linear_ordered_semiring α]

@[simp] lemma mul_le_mul_left {a b c : α} (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
⟨λ h', le_of_mul_le_mul_left h' h, λ h', mul_le_mul_of_nonneg_left h' (le_of_lt h)⟩

@[simp] lemma mul_le_mul_right {a b c : α} (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
⟨λ h', le_of_mul_le_mul_right h' h, λ h', mul_le_mul_of_nonneg_right h' (le_of_lt h)⟩

@[simp] lemma mul_lt_mul_left {a b c : α} (h : 0 < c) : c * a < c * b ↔ a < b :=
⟨λ h', lt_of_mul_lt_mul_left h' (le_of_lt h), λ h', mul_lt_mul_of_pos_left h' h⟩

@[simp] lemma mul_lt_mul_right {a b c : α} (h : 0 < c) : a * c < b * c ↔ a < b :=
⟨λ h', lt_of_mul_lt_mul_right h' (le_of_lt h), λ h', mul_lt_mul_of_pos_right h' h⟩

lemma mul_lt_mul'' {a b c d : α} (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) :
       a * b < c * d :=
(lt_or_eq_of_le h4).elim
  (λ b0, mul_lt_mul h1 (le_of_lt h2) b0 (le_trans h3 (le_of_lt h1)))
  (λ b0, by rw [← b0, mul_zero]; exact
    mul_pos (lt_of_le_of_lt h3 h1) (lt_of_le_of_lt h4 h2))

lemma le_mul_iff_one_le_left {a b : α} (hb : b > 0) : b ≤ a * b ↔ 1 ≤ a :=
suffices 1 * b ≤ a * b ↔ 1 ≤ a, by rwa one_mul at this,
mul_le_mul_right hb

lemma lt_mul_iff_one_lt_left {a b : α} (hb : b > 0) : b < a * b ↔ 1 < a :=
suffices 1 * b < a * b ↔ 1 < a, by rwa one_mul at this,
mul_lt_mul_right hb

lemma le_mul_iff_one_le_right {a b : α} (hb : b > 0) : b ≤ b * a ↔ 1 ≤ a :=
suffices b * 1 ≤ b * a ↔ 1 ≤ a, by rwa mul_one at this,
mul_le_mul_left hb

lemma lt_mul_iff_one_lt_right {a b : α} (hb : b > 0) : b < b * a ↔ 1 < a :=
suffices b * 1 < b * a ↔ 1 < a, by rwa mul_one at this,
mul_lt_mul_left hb

lemma lt_mul_of_gt_one_right' {a b : α} (hb : b > 0) : a > 1 → b < b * a :=
(lt_mul_iff_one_lt_right hb).2

lemma le_mul_of_ge_one_right' {a b : α} (hb : b ≥ 0) (h : a ≥ 1) : b ≤ b * a :=
suffices b * 1 ≤ b * a, by rwa mul_one at this,
mul_le_mul_of_nonneg_left h hb

lemma le_mul_of_ge_one_left' {a b : α} (hb : b ≥ 0) (h : a ≥ 1) : b ≤ a * b :=
suffices 1 * b ≤ a * b, by rwa one_mul at this,
mul_le_mul_of_nonneg_right h hb

theorem mul_nonneg_iff_right_nonneg_of_pos {a b : α} (h : 0 < a) : 0 ≤ b * a ↔ 0 ≤ b :=
⟨assume : 0 ≤ b * a, nonneg_of_mul_nonneg_right this h, assume : 0 ≤ b, mul_nonneg this $ le_of_lt h⟩

lemma bit1_pos {a : α} (h : 0 ≤ a) : 0 < bit1 a :=
lt_add_of_le_of_pos (add_nonneg h h) zero_lt_one

lemma bit1_pos' {a : α} (h : 0 < a) : 0 < bit1 a :=
bit1_pos (le_of_lt h)

lemma lt_add_one (a : α) : a < a + 1 :=
lt_add_of_le_of_pos (le_refl _) zero_lt_one

lemma one_lt_two : 1 < (2 : α) := lt_add_one _

lemma mul_le_one {a b : α} (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
begin rw ← one_mul (1 : α), apply mul_le_mul; {assumption <|> apply zero_le_one} end

end linear_ordered_semiring

instance linear_ordered_semiring.to_no_top_order {α : Type*} [linear_ordered_semiring α] :
  no_top_order α :=
⟨assume a, ⟨a + 1, lt_add_of_pos_right _ zero_lt_one⟩⟩

instance linear_ordered_semiring.to_no_bot_order {α : Type*} [linear_ordered_ring α] :
  no_bot_order α :=
⟨assume a, ⟨a - 1, sub_lt_iff_lt_add.mpr $ lt_add_of_pos_right _ zero_lt_one⟩⟩

instance to_domain [s : linear_ordered_ring α] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := @linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero α s,
  ..s }

section linear_ordered_ring
variable [linear_ordered_ring α]

@[simp] lemma mul_le_mul_left_of_neg {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
⟨le_imp_le_iff_lt_imp_lt.2 $ λ h', mul_lt_mul_of_neg_left h' h,
  λ h', mul_le_mul_of_nonpos_left h' (le_of_lt h)⟩

@[simp] lemma mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
⟨le_imp_le_iff_lt_imp_lt.2 $ λ h', mul_lt_mul_of_neg_right h' h,
  λ h', mul_le_mul_of_nonpos_right h' (le_of_lt h)⟩

@[simp] lemma mul_lt_mul_left_of_neg {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
le_iff_le_iff_lt_iff_lt.1 (mul_le_mul_left_of_neg h)

@[simp] lemma mul_lt_mul_right_of_neg {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
le_iff_le_iff_lt_iff_lt.1 (mul_le_mul_right_of_neg h)

lemma sub_one_lt (a : α) : a - 1 < a :=
sub_lt_iff_lt_add.2 (lt_add_one a)

lemma mul_self_pos {a : α} (ha : a ≠ 0) : 0 < a * a :=
by rcases lt_trichotomy a 0 with h|h|h;
   [exact mul_pos_of_neg_of_neg h h, exact (ha h).elim, exact mul_pos h h]

end linear_ordered_ring

set_option old_structure_cmd true
/-- Extend `nonneg_comm_group` to support ordered rings
  specified by their nonnegative elements -/
class nonneg_ring (α : Type*)
  extends ring α, zero_ne_one_class α, nonneg_comm_group α :=
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(mul_pos : ∀ {a b}, pos a → pos b → pos (a * b))

/-- Extend `nonneg_comm_group` to support linearly ordered rings
  specified by their nonnegative elements -/
class linear_nonneg_ring (α : Type*) extends domain α, nonneg_comm_group α :=
(mul_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a * b))
(nonneg_total : ∀ a, nonneg a ∨ nonneg (-a))

namespace nonneg_ring
open nonneg_comm_group
variable [s : nonneg_ring α]

instance to_ordered_ring : ordered_ring α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  add_lt_add_left := @add_lt_add_left _ _,
  add_le_add_left := @add_le_add_left _ _,
  mul_nonneg := λ a b, by simp [nonneg_def.symm]; exact mul_nonneg,
  mul_pos := λ a b, by simp [pos_def.symm]; exact mul_pos,
  ..s }

def nonneg_ring.to_linear_nonneg_ring
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : linear_nonneg_ring α :=
{ nonneg_total := nonneg_total,
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    suffices ∀ {a} b : α, nonneg a → a * b = 0 → a = 0 ∨ b = 0,
    from λ a b, (nonneg_total a).elim (this b)
      (λ na, by simpa using this b na),
    suffices ∀ {a b : α}, nonneg a → nonneg b → a * b = 0 → a = 0 ∨ b = 0,
    from λ a b na, (nonneg_total b).elim (this na)
      (λ nb, by simpa using this na nb),
    λ a b na nb z, classical.by_cases
      (λ nna : nonneg (-a), or.inl (nonneg_antisymm na nna))
      (λ pa, classical.by_cases
        (λ nnb : nonneg (-b), or.inr (nonneg_antisymm nb nnb))
        (λ pb, absurd z $ ne_of_gt $ pos_def.1 $ mul_pos
          ((pos_iff _ _).2 ⟨na, pa⟩)
          ((pos_iff _ _).2 ⟨nb, pb⟩))),
  ..s }

end nonneg_ring

namespace linear_nonneg_ring
open nonneg_comm_group
variable [s : linear_nonneg_ring α]

instance to_nonneg_ring : nonneg_ring α :=
{ mul_pos := λ a b pa pb,
  let ⟨a1, a2⟩ := (pos_iff α a).1 pa,
      ⟨b1, b2⟩ := (pos_iff α b).1 pb in
  have ab : nonneg (a * b), from mul_nonneg a1 b1,
  (pos_iff α _).2 ⟨ab, λ hn,
    have a * b = 0, from nonneg_antisymm ab hn,
    (eq_zero_or_eq_zero_of_mul_eq_zero _ _ this).elim
      (ne_of_gt (pos_def.1 pa))
      (ne_of_gt (pos_def.1 pb))⟩,
  ..s }

instance to_linear_order : linear_order α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := nonneg_total_iff.1 nonneg_total,
  ..s }

instance to_linear_ordered_ring : linear_ordered_ring α :=
{ le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := @le_total _ _,
  add_lt_add_left := @add_lt_add_left _ _,
  add_le_add_left := @add_le_add_left _ _,
  mul_nonneg := by simp [nonneg_def.symm]; exact @mul_nonneg _ _,
  mul_pos := by simp [pos_def.symm]; exact @nonneg_ring.mul_pos _ _,
  zero_lt_one := lt_of_not_ge $ λ (h : nonneg (0 - 1)), begin
    rw [zero_sub] at h,
    have := mul_nonneg h h, simp at this,
    exact zero_ne_one _ (nonneg_antisymm this h).symm
  end, ..s }

instance to_decidable_linear_ordered_comm_ring
  [decidable_pred (@nonneg α _)]
  [comm : @is_commutative α (*)]
  : decidable_linear_ordered_comm_ring α :=
{ decidable_le := by apply_instance,
  decidable_eq := by apply_instance,
  decidable_lt := by apply_instance,
  mul_comm := is_commutative.comm (*),
  ..@linear_nonneg_ring.to_linear_ordered_ring _ s }

end linear_nonneg_ring

class canonically_ordered_comm_semiring (α : Type*) extends
  canonically_ordered_monoid α, comm_semiring α, zero_ne_one_class α :=
(mul_eq_zero_iff (a b : α) : a * b = 0 ↔ a = 0 ∨ b = 0)

namespace canonically_ordered_semiring
open canonically_ordered_monoid

lemma mul_le_mul [canonically_ordered_comm_semiring α] {a b c d : α} (hab : a ≤ b) (hcd : c ≤ d) :
  a * c ≤ b * d :=
begin
  rcases (le_iff_exists_add _ _).1 hab with ⟨b, rfl⟩,
  rcases (le_iff_exists_add _ _).1 hcd with ⟨d, rfl⟩,
  suffices : a * c ≤ a * c + (a * d + b * c + b * d), by simpa [mul_add, add_mul],
  exact (le_iff_exists_add _ _).2 ⟨_, rfl⟩
end

end canonically_ordered_semiring

instance : canonically_ordered_comm_semiring ℕ :=
{ le_iff_exists_add := assume a b,
  ⟨assume h, let ⟨c, hc⟩ := nat.le.dest h in ⟨c, hc.symm⟩,
    assume ⟨c, hc⟩, hc.symm ▸ nat.le_add_right _ _⟩,
  zero_ne_one       := ne_of_lt zero_lt_one,
  mul_eq_zero_iff   := assume a b,
    iff.intro nat.eq_zero_of_mul_eq_zero (by simp [or_imp_distrib] {contextual := tt}),
  .. (infer_instance : ordered_comm_monoid ℕ),
  .. (infer_instance : linear_ordered_semiring ℕ),
  .. (infer_instance : comm_semiring ℕ) }

namespace with_top
variables [canonically_ordered_comm_semiring α] [decidable_eq α]

instance : mul_zero_class (with_top α) :=
{ zero := 0,
  mul := λm n, if m = 0 ∨ n = 0 then 0 else m.bind (λa, n.bind $ λb, ↑(a * b)),
  zero_mul := assume a, if_pos $ or.inl rfl,
  mul_zero := assume a, if_pos $ or.inr rfl }

instance : has_one (with_top α) := ⟨↑(1:α)⟩

lemma mul_def {a b : with_top α} :
  a * b = if a = 0 ∨ b = 0 then 0 else a.bind (λa, b.bind $ λb, ↑(a * b)) := rfl

@[simp] theorem top_ne_zero [partial_order α] : ⊤ ≠ (0 : with_top α) .
@[simp] theorem zero_ne_top [partial_order α] : (0 : with_top α) ≠ ⊤ .

@[simp] theorem coe_eq_zero [partial_order α] {a : α} : (a : with_top α) = 0 ↔ a = 0 :=
iff.intro
  (assume h, match a, h with _, rfl := rfl end)
  (assume h, h.symm ▸ rfl)

@[simp] theorem zero_eq_coe [partial_order α] {a : α} : 0 = (a : with_top α) ↔ a = 0 :=
by rw [eq_comm, coe_eq_zero]

@[simp] theorem coe_zero [partial_order α] : ↑(0 : α) = (0 : with_top α) := rfl

@[simp] lemma mul_top {a : with_top α} (h : a ≠ 0) : a * ⊤ = ⊤ :=
by cases a; simp [mul_def, h]; refl

@[simp] lemma top_mul {a : with_top α} (h : a ≠ 0) : ⊤ * a = ⊤ :=
by cases a; simp [mul_def, h]; refl

@[simp] lemma top_mul_top : (⊤ * ⊤ : with_top α) = ⊤ :=
top_mul top_ne_zero

lemma coe_mul {a b : α} : (↑(a * b) : with_top α) = a * b :=
decidable.by_cases (assume : a = 0, by simp [this]) $ assume ha,
decidable.by_cases (assume : b = 0, by simp [this]) $ assume hb,
by simp [*, mul_def]; refl

lemma mul_coe {b : α} (hb : b ≠ 0) : ∀{a : with_top α}, a * b = a.bind (λa:α, ↑(a * b))
| none     := show (if (⊤:with_top α) = 0 ∨ (b:with_top α) = 0 then 0 else ⊤ : with_top α) = ⊤,
    by simp [hb]
| (some a) := show ↑a * ↑b = ↑(a * b), from coe_mul.symm

private lemma comm (a b : with_top α) : a * b = b * a :=
begin
  by_cases ha : a = 0, { simp [ha] },
  by_cases hb : b = 0, { simp [hb] },
  simp [ha, hb, mul_def, option.bind_comm a b, mul_comm]
end

private lemma distrib' (a b c : with_top α) : (a + b) * c = a * c + b * c :=
begin
  cases c,
  { show (a + b) * ⊤ = a * ⊤ + b * ⊤,
    by_cases ha : a = 0; simp [ha] },
  { show (a + b) * c = a * c + b * c,
    by_cases hc : c = 0, { simp [hc] },
    simp [mul_coe hc], cases a; cases b,
    repeat { refl <|> exact congr_arg some (add_mul _ _ _) } }
end

private lemma mul_eq_zero (a b : with_top α) : a * b = 0 ↔ a = 0 ∨ b = 0 :=
by cases a; cases b; dsimp [mul_def]; split_ifs;
  simp [*, none_eq_top, some_eq_coe, canonically_ordered_comm_semiring.mul_eq_zero_iff] at *

private lemma assoc (a b c : with_top α) : (a * b) * c = a * (b * c) :=
begin
  cases a,
  { by_cases hb : b = 0; by_cases hc : c = 0;
      simp [*, none_eq_top, mul_eq_zero b c] },
  cases b,
  { by_cases ha : a = 0; by_cases hc : c = 0;
      simp [*, none_eq_top, some_eq_coe, mul_eq_zero ↑a c] },
  cases c,
  { by_cases ha : a = 0; by_cases hb : b = 0;
      simp [*, none_eq_top, some_eq_coe, mul_eq_zero ↑a ↑b] },
  simp [some_eq_coe, coe_mul.symm, mul_assoc]
end

private lemma one_mul' : ∀a : with_top α, 1 * a = a
| none     := show ((1:α) : with_top α) * ⊤ = ⊤, by simp
| (some a) := show ((1:α) : with_top α) * a = a, by simp [coe_mul.symm]

instance [canonically_ordered_comm_semiring α] [decidable_eq α] :
  canonically_ordered_comm_semiring (with_top α) :=
{ one             := (1 : α),
  right_distrib   := distrib',
  left_distrib    := assume a b c, by rw [comm, distrib', comm b, comm c]; refl,
  mul_assoc       := assoc,
  mul_comm        := comm,
  mul_eq_zero_iff := mul_eq_zero,
  one_mul         := one_mul',
  mul_one         := assume a, by rw [comm, one_mul'],
  zero_ne_one     := assume h, @zero_ne_one α _ $ option.some.inj h,
  .. with_top.add_comm_monoid, .. with_top.mul_zero_class, .. with_top.canonically_ordered_monoid }

end with_top

section monotonicity

@[monotonic]
lemma mul_mono_nonneg {x y z : α} [ordered_semiring α]
  (h' : 0 ≤ z)
  (h : x ≤ y)
: x * z ≤ y * z :=
by apply mul_le_mul_of_nonneg_right; assumption

lemma gt_of_mul_lt_mul_neg_right {a b c : α}  [linear_ordered_ring α]
  (h : a * c < b * c) (hc : c ≤ 0) : a > b :=
have nhc : -c ≥ 0, from neg_nonneg_of_nonpos hc,
have h2 : -(b * c) < -(a * c), from neg_lt_neg h,
have h3 : b * (-c) < a * (-c), from calc
     b * (-c) = - (b * c)    : by rewrite neg_mul_eq_mul_neg
          ... < - (a * c)    : h2
          ... = a * (-c)     : by rewrite neg_mul_eq_mul_neg,
lt_of_mul_lt_mul_right h3 nhc

@[monotonic]
lemma mul_mono_nonpos {x y z : α} [linear_ordered_ring α]
  [decidable_rel ((≤) : α → α → Prop)]
  (h' : 0 ≥ z)
  (h : y ≤ x)
: x * z ≤ y * z :=
begin
  by_contradiction h'',
  revert h,
  apply not_le_of_lt,
  apply gt_of_mul_lt_mul_neg_right _ h',
  apply lt_of_not_ge h''
end

@[monotonic]
lemma nat.sub_mono_left_strict {x y z : ℕ}
  (h' : z ≤ x)
  (h : x < y)
: x - z < y - z :=
begin
  have : z ≤ y,
  { transitivity, assumption, apply le_of_lt h, },
  apply @lt_of_add_lt_add_left _ _ z,
  rw [nat.add_sub_of_le,nat.add_sub_of_le];
    solve_by_elim
end

@[monotonic]
lemma nat.sub_mono_right_strict {x y z : ℕ}
  (h' : x ≤ z)
  (h : y < x)
: z - x < z - y :=
begin
  have h'' : y ≤ z,
  { transitivity, apply le_of_lt h, assumption },
  apply @lt_of_add_lt_add_right _ _ _ x,
  rw [nat.sub_add_cancel h'],
  apply @lt_of_le_of_lt _ _ _ (z - y + y),
  rw [nat.sub_add_cancel h''],
  apply nat.add_lt_add_left h
end

end monotonicity
