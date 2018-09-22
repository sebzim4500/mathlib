/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Introduce Grp -- the category of group.

Currently only the basic setup.
-/

import category_theory.embedding
import algebra.ring

universes u v

open category_theory

namespace category_theory.examples

/-- The category of monoids and monoid morphisms. -/
@[reducible] def Grp : Type (u+1) := bundled group

instance (x : Grp) : group x := x.str

instance concrete_is_group_hom : concrete_category @is_group_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance Grp_hom_is_group_hom {R S : Grp} (f : R ⟶ S) : is_group_hom (f : R → S) := f.2

end category_theory.examples
