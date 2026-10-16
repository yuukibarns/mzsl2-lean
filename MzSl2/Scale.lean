import Mathlib

/-!
# Scale and dynamical Levi subgroups (definitions)

For a topological group `H`:
* `IsCompactOpenSubgroup V`;
* `scale h = min { [hVh⁻¹ : hVh⁻¹ ∩ V] : V compact open subgroup }` (Willis);
* `levi g = { x | {gⁿ x g⁻ⁿ : n ∈ ℤ} is relatively compact }` (Baumgartner–Willis `M_g`).

The theorems of Willis and Baumgartner–Willis about these are axioms, see `MzSl2/Axioms.lean`.
-/

open Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- A compact open subgroup. -/
def IsCompactOpenSubgroup (V : Subgroup H) : Prop := IsCompact (V : Set H) ∧ IsOpen (V : Set H)

/-- Willis' scale of an element: `min [hVh⁻¹ : hVh⁻¹ ∩ V]` over compact open subgroups `V`.
(`V.relIndex K` is the index of `V ⊓ K` in `K`.) -/
noncomputable def scale (h : H) : ℕ :=
  sInf {n | ∃ V : Subgroup H, IsCompactOpenSubgroup V ∧ n = V.relIndex (ConjAct.toConjAct h • V)}

/-- The dynamical Levi subgroup `M_g`: elements whose two-sided conjugation orbit under `g` is
relatively compact. -/
def levi (g : H) : Set H :=
  {x | IsCompact (closure (Set.range fun n : ℤ => g ^ n * x * g ^ (-n)))}

end MzSl2
