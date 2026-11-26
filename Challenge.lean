module

public import Mathlib

@[expose] public section

/-!
# The Vacuus and the Resonus of the permutohedron, machine-checked (DICTO #120)

**Informal statement.** The permutohedron `P n` is the convex hull of the rearrangements of `(n, n-1, …, 1)` in `ℝⁿ`; its
centre is `((n+1)/2, …, (n+1)/2)`. Its *Vacuus* is the set of planes through the centre and a ridge; its *Resonus* is the set
of planes through the centre parallel to a facet. Every statement below is about faces of `P n` itself.

*Faces.* An ordered partition of the coordinates into `m` nonempty blocks is a surjective `key : Fin n → Fin m`. Its face
`flagFace key` is the set of points of `P n` at which, for every `t`, the coordinates in blocks `≤ t` have the largest sum
that occurs on `P n` (`top n k`, the sum of the `k` largest entries). `facet S` is the face of one set `S`.
1. `flagFace_isExposed`, `finrank_vectorSpan_flagFace`: the face of `key` is an exposed face of `P n` of dimension `n - m`
   (facets `m = 2`, ridges `m = 3`).
2. `facet_isExposed`, `vectorSpan_facet`, `finrank_vectorSpan_facet`: for `∅ ≠ S ≠ univ` the facet of `S` is an exposed face,
   its directions are the vectors with sum `0` over `S` and over the complement (`dirs S`), and its dimension is `n - 2`.

*Vacuus.* A ridge is the face of `key : Fin n → Fin 3` surjective, with blocks `B₁, B₂, B₃` of sizes `a, b, c`.
3. `span_centred_ridge` (**#120 Theorem 3 (i)**): the plane through the centre and the ridge is
   `permPlate B₁ B₂ B₃ = {y | ∑ y = 0 ∧ c(a+b) ∑_{B₁} y + a(b+c) ∑_{B₃} y = 0}`.
4. `plate_eq_iff` (**#120 Theorem 3 (ii)**): two ridges have the same plate exactly when `a ≠ c` and the second ridge is the
   first or the first read backwards, or both have outer blocks of equal size and the same or complementary middle blocks.
5. `card_plateSet` (**#120 Theorem 3 (iii)**, OEIS A402191): for `n ≥ 3` the number of distinct plates is
   `∑_{a+b+c=n, a,b,c ≥ 1, a<c} n!/(a! b! c!) + T(n)`, `T(n) = 2^(n-2) - 1` for `n` even and `2^(n-1) - 1` for `n` odd;
   `plates_three … plates_eight`: the values `3, 15, 65, 225, 770, 2443`.

*Resonus.* The Resonus plane of the facet of `S` is its direction space `vectorSpan ℝ (facet S) = dirs S`.
6. `vectorSpan_facet_eq_iff`, `dirs_eq_iff`: two facets have the same Resonus plane exactly when `S' = S` or `S' = Sᶜ`.
7. `card_resonusSet`: there are `2^(n-1) - 1` Resonus planes; `resonus_three … resonus_eight`: `3, 7, 15, 31, 63, 127`.
8. `resonus_parallel`: each Resonus plane is `dirs S` for a facet `S`; the facet is not empty and lies in the translate of
   the plane through any of its points; the plane has dimension `n - 2`.
9. `dirs_eq_plate_iff`: the Resonus plane of `S` is the Vacuus plate of a ridge exactly when the outer blocks of the ridge
   have equal size and `S` is its middle block or the complement.
10. `resonusSet_subset_plateSet_of_odd`, `card_resonus_diff_plate_even`: for odd `n ≥ 3` every Resonus plane is a Vacuus
    plate; for even `n ≥ 4` exactly `2^(n-2)` Resonus planes are not.

**Sources.** DICTO's paper #120 (Theorems 3 and 5). The faces of the permutohedron and Rado's theorem are classical (Rado
1952; Ziegler, *Lectures on Polytopes*). Every definition and statement is copied from the Lean library `PermFaces` (here
namespace `VR`); `prefixSum` (the sum of the first `k` coordinates) is copied from the TauCeti library (Apache-2.0), whose
formalization of Rado's theorem the proofs use.
-/

namespace VR

open Finset
open scoped Pointwise

variable {n m : ℕ}

/-! ### The permutohedron and its faces -/

/-- `w = (n, n-1, …, 1)`. -/
def w (n : ℕ) : Fin n → ℝ := fun i => ((n - (i : ℕ) : ℕ) : ℝ)

/-- The permutohedron: the convex hull of the rearrangements of `w`. -/
def P (n : ℕ) : Set (Fin n → ℝ) := convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) => w n ∘ σ)

/-- The prefix sum `∑_{i < k} x i` of the first `k` coordinates of `x`. For `n ≤ k` it is the
sum of all coordinates. -/
def prefixSum {M : Type*} [AddCommMonoid M] (k : ℕ) (x : Fin n → M) : M :=
  ∑ i : Fin n with i.val < k, x i

/-- The sum of the `k` largest entries of `w`. -/
def top (n k : ℕ) : ℝ := prefixSum k (w n)

/-- The face of `S`: the points of `P n` where the facet inequality of `S` is an equality. -/
def facet (S : Finset (Fin n)) : Set (Fin n → ℝ) := {x | x ∈ P n ∧ ∑ i ∈ S, x i = top n S.card}

/-- `v ↦ ∑_{i ∈ T} vᵢ` as a linear map. -/
def sumL (T : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i ∈ T, v i
  map_add' x y := by simp [sum_add_distrib]
  map_smul' c x := by simp [mul_sum]

/-- The pair of sums over `S` and over its complement. -/
def pairL (S : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] ℝ × ℝ := (sumL S).prod (sumL Sᶜ)

/-- The directions predicted for the facet of `S`. -/
def dirs (S : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) := LinearMap.ker (pairL S)

/-- The coordinates in blocks `≤ t`. -/
def low (key : Fin n → Fin m) (t : ℕ) : Finset (Fin n) := univ.filter fun i => (key i : ℕ) ≤ t

/-- The coordinates in block `b`. -/
def block (key : Fin n → Fin m) (b : Fin m) : Finset (Fin n) := univ.filter fun i => key i = b

/-- The face of the ordered set partition `key`. -/
def flagFace (key : Fin n → Fin m) : Set (Fin n → ℝ) :=
  {x | x ∈ P n ∧ ∀ t : Fin m, ∑ i ∈ low key t, x i = top n (low key t).card}

/-- **The face of an ordered set partition is an exposed face of the permutohedron.** -/
theorem flagFace_isExposed (key : Fin n → Fin m) : IsExposed ℝ (P n) (flagFace key) := by
  sorry

/-- **The face of an ordered set partition into `m` nonempty blocks has dimension `n - m`.** -/
theorem finrank_vectorSpan_flagFace {key : Fin n → Fin m} (hkey : Function.Surjective key) :
    Module.finrank ℝ (vectorSpan ℝ (flagFace key)) = n - m := by
  sorry

/-- **Each face of `S` is an exposed face of the permutohedron.** -/
theorem facet_isExposed (S : Finset (Fin n)) : IsExposed ℝ (P n) (facet S) := by
  sorry

/-- **The directions of a facet.** For `∅ ≠ S ≠ univ`, the vector span of the facet of `S` is `dirs S`. -/
theorem vectorSpan_facet {S : Finset (Fin n)} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    vectorSpan ℝ (facet S) = dirs S := by
  sorry

/-- **Each facet has dimension `n - 2`.** -/
theorem finrank_vectorSpan_facet {S : Finset (Fin n)} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    Module.finrank ℝ (vectorSpan ℝ (facet S)) = n - 2 := by
  sorry

/-! ### The Vacuus: the plate of a ridge -/

/-- The centre of the permutohedron. -/
noncomputable def centre (n : ℕ) : Fin n → ℝ := fun _ => ((n : ℝ) + 1) / 2

/-- The plate predicted by #120 Theorem 3 (i), as a submodule of `Fin n → ℝ`. -/
def permPlate (B₁ B₂ B₃ : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) where
  carrier := {y | ∑ i, y i = 0 ∧
    (B₃.card : ℝ) * ((B₁.card : ℝ) + B₂.card) * ∑ i ∈ B₁, y i +
      (B₁.card : ℝ) * ((B₂.card : ℝ) + B₃.card) * ∑ i ∈ B₃, y i = 0}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · simp [Finset.sum_add_distrib, hx1, hy1]
    · simp only [Pi.add_apply, Finset.sum_add_distrib]; linear_combination hx2 + hy2
  zero_mem' := by simp
  smul_mem' := by
    rintro t y ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show ∑ i, t * y i = 0
      rw [← Finset.mul_sum, h1, mul_zero]
    · show (B₃.card : ℝ) * ((B₁.card : ℝ) + B₂.card) * ∑ i ∈ B₁, t * y i +
          (B₁.card : ℝ) * ((B₂.card : ℝ) + B₃.card) * ∑ i ∈ B₃, t * y i = 0
      rw [← Finset.mul_sum, ← Finset.mul_sum]; linear_combination t * h2

/-- **#120 Theorem 3 (i) on the real ridge.** For an ordered partition into three nonempty blocks, the plane through the
centre and the ridge (the face of `key`) is the Vacuus plate `permPlate B₁ B₂ B₃`. -/
theorem span_centred_ridge {key : Fin n → Fin 3} (hkey : Function.Surjective key) :
    Submodule.span ℝ ((fun x => x - centre n) '' flagFace key) =
      permPlate (block key 0) (block key 1) (block key 2) := by
  sorry

/-- Block sizes. -/
def sz (key : Fin n → Fin 3) (b : Fin 3) : ℝ := (block key b).card

/-- **#120 Theorem 3 (ii), complete.** Two ridges (ordered partitions into three nonempty blocks) have the same Vacuus plate
exactly when: the outer blocks differ in size and the second ridge is the first or the first read backwards; or both ridges
have outer blocks of equal size and the same middle block or complementary middle blocks. -/
theorem plate_eq_iff {key key' : Fin n → Fin 3} (hk : Function.Surjective key) (hk' : Function.Surjective key') :
    permPlate (block key 0) (block key 1) (block key 2) =
        permPlate (block key' 0) (block key' 1) (block key' 2) ↔
      (sz key 0 ≠ sz key 2 ∧ (key' = key ∨ key' = Fin.rev ∘ key)) ∨
      (sz key 0 = sz key 2 ∧ sz key' 0 = sz key' 2 ∧
        (block key' 1 = block key 1 ∨ block key' 1 = (block key 1)ᶜ)) := by
  sorry

/-! ### The number of plates -/

/-- The plate of a ridge. -/
def plate (key : Fin n → Fin 3) : Submodule ℝ (Fin n → ℝ) :=
  permPlate (block key 0) (block key 1) (block key 2)

/-- The set of all ridge plates of the permutohedron in `Fin n → ℝ`. -/
def plateSet (n : ℕ) : Set (Submodule ℝ (Fin n → ℝ)) :=
  {P | ∃ key : Fin n → Fin 3, Function.Surjective key ∧
    permPlate (block key 0) (block key 1) (block key 2) = P}

/-- Block sizes as natural numbers. -/
def bc (key : Fin n → Fin 3) (b : Fin 3) : ℕ := (block key b).card

/-- The admissible size triples: `a + b + c = n`, all at least `1`, `a < c`. -/
def sizes (n : ℕ) : Finset (Fin 3 → ℕ) :=
  (Finset.Nat.antidiagonalTuple 3 n).filter fun t => 1 ≤ t 0 ∧ 1 ≤ t 1 ∧ 1 ≤ t 2 ∧ t 0 < t 2

/-- **The number of distinct Vacuus plates of the permutohedron** (`n ≥ 3`):
`∑_{a+b+c=n, a,b,c ≥ 1, a<c} n!/(a! b! c!) + T(n)`, with `T(n) = 2^(n-2) - 1` for `n` even and `2^(n-1) - 1` for `n` odd. -/
theorem card_plateSet (hn : 3 ≤ n) :
    (plateSet n).ncard =
      ∑ t ∈ sizes n, n.factorial / ((t 0).factorial * (t 1).factorial * (t 2).factorial) +
        (if Even n then 2 ^ (n - 2) - 1 else 2 ^ (n - 1) - 1) := by
  sorry

theorem plates_three : (plateSet 3).ncard = 3 := by
  sorry

theorem plates_four : (plateSet 4).ncard = 15 := by
  sorry

theorem plates_five : (plateSet 5).ncard = 65 := by
  sorry

theorem plates_six : (plateSet 6).ncard = 225 := by
  sorry

theorem plates_seven : (plateSet 7).ncard = 770 := by
  sorry

theorem plates_eight : (plateSet 8).ncard = 2443 := by
  sorry

/-! ### The Resonus -/

/-- **Parallel facets.** For `∅ ≠ S, S' ≠ univ`, the facets of `S` and `S'` have the same directions exactly when
`S' = S` or `S' = Sᶜ`. -/
theorem dirs_eq_iff {S S' : Finset (Fin n)} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hS' : S'.Nonempty)
    (hSc' : S'ᶜ.Nonempty) : dirs S = dirs S' ↔ S' = S ∨ S' = Sᶜ := by
  sorry

/-- **The Resonus of the permutohedron**: the direction spaces of its facets (the hyperplanes of the sum-zero space through
the centre parallel to a facet), parallel facets sharing one. -/
def resonusSet (n : ℕ) : Set (Submodule ℝ (Fin n → ℝ)) :=
  {D | ∃ S : Finset (Fin n), S.Nonempty ∧ Sᶜ.Nonempty ∧ vectorSpan ℝ (facet S) = D}

/-- The same two facet statements for the two sets named in `dirs_eq_iff`, in terms of the facets themselves. -/
theorem vectorSpan_facet_eq_iff {S S' : Finset (Fin n)} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hS' : S'.Nonempty)
    (hSc' : S'ᶜ.Nonempty) : vectorSpan ℝ (facet S) = vectorSpan ℝ (facet S') ↔ S' = S ∨ S' = Sᶜ := by
  sorry

/-- **The number of Resonus planes of the permutohedron is `2^(n-1) - 1`** (all `n`; the paper's range is `n ≥ 2`). -/
theorem card_resonusSet (n : ℕ) : (resonusSet n).ncard = 2 ^ (n - 1) - 1 := by
  sorry

theorem resonus_three : (resonusSet 3).ncard = 3 := by
  sorry

theorem resonus_four : (resonusSet 4).ncard = 7 := by
  sorry

theorem resonus_five : (resonusSet 5).ncard = 15 := by
  sorry

theorem resonus_six : (resonusSet 6).ncard = 31 := by
  sorry

theorem resonus_seven : (resonusSet 7).ncard = 63 := by
  sorry

theorem resonus_eight : (resonusSet 8).ncard = 127 := by
  sorry

/-- **Each Resonus plane is parallel to a facet**: it is `dirs S` for a facet `S`, the facet is nonempty and lies in the
translate of the plane through any of its points, and the plane has dimension `n - 2`. -/
theorem resonus_parallel {D : Submodule ℝ (Fin n → ℝ)} (hD : D ∈ resonusSet n) :
    ∃ S : Finset (Fin n), S.Nonempty ∧ Sᶜ.Nonempty ∧ D = dirs S ∧ (facet S).Nonempty ∧
      (∀ x ∈ facet S, facet S ⊆ x +ᵥ (D : Set (Fin n → ℝ))) ∧ Module.finrank ℝ D = n - 2 := by
  sorry

/-- **When a Resonus plane is a Vacuus plate.** The direction space of the facet of `S` is the plate of the ridge with blocks
`B₁, B₂, B₃` exactly when `B₁` and `B₃` have equal size and `S` is the middle block `B₂` or its complement. -/
theorem dirs_eq_plate_iff {key : Fin n → Fin 3} (hk : Function.Surjective key) (S : Finset (Fin n)) :
    dirs S = plate key ↔ bc key 0 = bc key 2 ∧ (S = block key 1 ∨ S = (block key 1)ᶜ) := by
  sorry

/-- **`n` odd: every Resonus plane is a Vacuus plate.** -/
theorem resonusSet_subset_plateSet_of_odd (hn : 3 ≤ n) (ho : ¬ Even n) : resonusSet n ⊆ plateSet n := by
  sorry

/-- **`n` even: exactly `2^(n-2)` Resonus planes are not Vacuus plates** (and `2^(n-2) - 1` are). -/
theorem card_resonus_diff_plate_even (hn : 3 ≤ n) (he : Even n) :
    (resonusSet n \ plateSet n).ncard = 2 ^ (n - 2) := by
  sorry

end VR
