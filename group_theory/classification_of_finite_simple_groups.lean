import group_theory.subgroup
import group_theory.perm
import category_theory.examples.groups
import category_theory.isomorphism
import data.nat.prime
import data.zmod
import tactic.tidy

open nat
open equiv
open is_group_hom
open category_theory.examples
open tactic.interactive

universe u
variables (G : Grp.{0})

def cyclic_group (n : ℕ+) : Grp.{0} := { α := multiplicative (zmod n), str := by apply_instance }
def symmetric_group (n : ℕ) : Grp.{0} := { α := perm (fin n) }
def alternating_group (n : ℕ) : Grp.{0} := { α := { x : perm (fin n) // x ∈ ker (@perm.sign (fin n) _ _) } }

def Prime := { p : ℕ //  prime p }
instance : has_coe Prime ℕ := 
{ coe := λ p, p.1 }
instance : has_coe Prime ℕ+ := 
{ coe := λ p, ⟨ p.1, prime.pos p.2 ⟩ }

def is_cyclic_group_of_prime_order := Σ p : Prime, G ≅ cyclic_group p
def is_simple_alternating_group := Σ' n ≥ 5, G ≅ alternating_group n
def is_classical_linear_group (G : Grp.{0}) : Type := sorry -- there is a lot of work here!
def is_exceptional_group_of_Lie_type (G : Grp.{0}) : Type := sorry

instance nodup_decidable_fast {α : Type u} [decidable_eq α] : Π l : list α, decidable (list.nodup l)
| [] := is_true list.nodup_nil
| (h::t) := if h ∈ t then is_false sorry else sorry

def perm.of_cycles (n : ℕ) (cycles : list (list ℕ))
  (b : ∀ c ∈ cycles, ∀ m ∈ c, m < n . obviously) (d : (cycles.join).nodup . admit /- switch to obviously -/) : 
  perm (fin n) := 
sorry

namespace sporadic_simple_groups
-- The Mathieu groups
def M_12_generators : list (perm (fin 12)) := 
[perm.of_cycles 12 [[0,1,2,3,4,5,6,7,8,9,10]],
 perm.of_cycles 12 [[0,11], [1,10], [2,5], [3,7], [4,8], [6,9]],
 perm.of_cycles 12 [[2,6,10,7],[3,9,4,5]]].

def M_12_elements := group.closure { x | x ∈ M_12_generators }

def M_12 : Grp := { α := M_12_elements, str := by unfold M_12_elements; apply_instance }.

/- These should be replaced with more general notions for group actions. -/
def stabiliser {n : ℕ} (s : set (perm (fin n))) (k : fin n) := { x : perm (fin n ) | x ∈ s ∧ equiv.to_fun x k = k }
instance stabiliser_subgroup {n : ℕ} (s : set (perm (fin n))) (k : fin n) : group (stabiliser s k) := sorry

def M_11 : Grp := { α := stabiliser M_12_elements 0 }

def M_24_generators : list (perm (fin 24)) := 
[perm.of_cycles 24 [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]],
 perm.of_cycles 24 [[0,23], [1,12], [2,11], [3,15], [4,17], [5,9], [6,19], [7,13], [8,20], [10,16], [12,21], [14,18]],
 perm.of_cycles 24 [[2,16,9,6,8],[3,12,13,18,4],[7,17,10,11,22],[14,19,21,20,15]]].

def M_24_elements := group.closure { x | x ∈ M_24_generators }

def M_24 : Grp := { α := M_24_elements, str := by unfold M_24_elements; apply_instance }.
def M_23 : Grp := { α := stabiliser M_24_elements 0 }
def M_22 : Grp := { α := stabiliser (stabiliser M_24_elements 0) 1 }

-- The Janko groups
def J_1 : Grp := sorry
def J_2 : Grp := sorry
def J_3 : Grp := sorry
def J_4 : Grp := sorry

-- The Conway groups and babies
def Co_1 : Grp := sorry
def Co_2 : Grp := sorry
def Co_3 : Grp := sorry
def HS : Grp   := sorry
def Mc : Grp   := sorry
def Suz : Grp  := sorry

-- The Fischer groups
def Fi_22  : Grp := sorry
def Fi_23  : Grp := sorry
def Fi_24' : Grp := sorry

-- The monster and its babies
def M : Grp   := sorry
def F_2 : Grp := sorry
def F_3 : Grp := sorry
def F_5 : Grp := sorry
def He : Grp  := sorry

-- The others...
def Ru : Grp := sorry
def Ly : Grp := sorry
def ON : Grp := sorry
end sporadic_simple_groups

open sporadic_simple_groups

def sporadic_simple_groups : list Grp.{0} :=
[M_11,M_12,M_22,M_23,M_24,J_1,J_2,J_3,J_4,Co_1,Co_2,Co_3,HS,Mc,Suz,Fi_22,Fi_23,Fi_24',M,F_2,F_3,F_5,He,Ru,Ly,ON]

def is_sporadic_simple_group := Σ' K ∈ sporadic_simple_groups, G ≅ K

def classification_finite_simple_groups [fintype G.α] (s : simple G.α) :=
  is_cyclic_group_of_prime_order G   ⊕
  is_simple_alternating_group G      ⊕
  is_classical_linear_group G        ⊕
  is_exceptional_group_of_Lie_type G ⊕
  is_sporadic_simple_group G
