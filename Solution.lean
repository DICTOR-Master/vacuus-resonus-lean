module

public import Mathlib
public import VacuusResonus

@[expose] public section

/-!
# The Vacuus and the Resonus, machine-checked (DICTO #120)

**Informal statement.** A convex polytope `P` with the centre `O = 0` inside. Its *Vacuus* is the set of planes through `O`
and a ridge (an edge in 3-space); its *Resonus* is the set of planes through `O` parallel to a facet. A facet lies on a plane
`⟪a, x⟫ = 1`; the vectors `a` are the corners of the polar `P*`.

1. `resonusPlane_eq_orthogonal` (**#120 Theorem 4 (a), the polar link**): the plane through `O` parallel to the facet plane
   `⟪a, x⟫ = 1` (the translations carrying it into itself) is the orthogonal complement of the line to the polar corner `a`.
2. `span_ridgeFlat` (**#120 Theorem 2, the pencil lemma**): for independent `u₁, u₂` and `h₁, h₂ ≠ 0`, the plane through `O`
   and the flat of `⟪u₁, y⟫ = h₁`, `⟪u₂, y⟫ = h₂` is the zero set of `h₂ u₁ - h₁ u₂`.
3. `vacuusPlate_polar` (**#120 Theorem 4 (b), any dimension**): a ridge whose affine span is the flat of `⟪a, x⟫ = 1` and
   `⟪b, x⟫ = 1` spans the plane at right angles to the polar edge direction `a - b`.
4. `heart_of_symm` (**#120 Theorem 1, one direction**): a centrally symmetric set is of the heart kind: the opposite of every
   ridge (a nonempty exposed face of dimension `finrank E - 2`) is again a ridge. (The converse is not formalized here.)
5. `span_permFlat` (**#120 Theorem 3 (i)**): in `ℝⁿ`, the plane through `O` and the flat of the permutohedron ridge
   `(B₁, B₂, B₃)` (facet planes `∑_{B₁} y = a(b+c)/2`, `∑_{B₁ ∪ B₂} y = (a+b)c/2`, inside `∑ y = 0`; `a, b, c` the block sizes)
   is `{y | ∑ y = 0 ∧ c(a+b) ∑_{B₁} y + a(b+c) ∑_{B₃} y = 0}`.
6. `web_iff` (**lattice webs, Theorem 0**): for a convex, centrally symmetric cell `P` with interior points, a functional `f ≠ 0`
   with least upper bound `h` on `P`, and a lattice `Λ`: every translate of a central plane `f x = f λ` that meets the interior
   of a cell `P + μ` is that cell's own central plane if and only if every `ν ∈ Λ` has `f ν = 0` or `h ≤ |f ν|`.

**Sources.** DICTO's paper #120 (Theorems 1 to 4); the polar and face duality as in Ziegler, *Lectures on Polytopes*; the
pencil lemma is standard linear algebra. Every definition and statement is copied from the Lean library `VacuusResonus`
(here namespace `VR`).
-/

namespace VR

open scoped RealInnerProductSpace Pointwise
open Finset

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The facet plane `⟪a, x⟫ = 1`. -/
def facetPlane (a : E) : Set E := {x | ⟪a, x⟫ = 1}

/-- The Resonus plane of the facet plane `⟪a, x⟫ = 1`: the translations carrying it into itself. -/
def resonusPlane (a : E) : Set E := {v | ∀ p ∈ facetPlane a, p + v ∈ facetPlane a}

/-- The points on both facet planes `⟪u₁, y⟫ = h₁` and `⟪u₂, y⟫ = h₂`. -/
def ridgeFlat (u₁ : E) (h₁ : ℝ) (u₂ : E) (h₂ : ℝ) : Set E := {y | ⟪u₁, y⟫ = h₁ ∧ ⟪u₂, y⟫ = h₂}

/-- The pencil form `h₂ u₁ - h₁ u₂`. -/
def pencil (u₁ : E) (h₁ : ℝ) (u₂ : E) (h₂ : ℝ) : E := h₂ • u₁ - h₁ • u₂

/-- A ridge of `X`: a nonempty exposed face of dimension `finrank E - 2`. -/
def IsRidge (X R : Set E) : Prop :=
  R.Nonempty ∧ IsExposed ℝ X R ∧ Module.finrank ℝ (vectorSpan ℝ R) + 2 = Module.finrank ℝ E

/-- The heart kind: the opposite of every ridge is a ridge. -/
def IsHeart (X : Set E) : Prop := ∀ R, IsRidge X R → IsRidge X (-R)

theorem resonusPlane_eq_orthogonal {a : E} (ha : a ≠ 0) :
    resonusPlane a = ((ℝ ∙ a)ᗮ : Submodule ℝ E) := by
  exact VacuusResonus.resonusPlane_eq_orthogonal ha

theorem span_ridgeFlat {u₁ u₂ : E} (hli : LinearIndependent ℝ ![u₁, u₂]) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) :
    Submodule.span ℝ (ridgeFlat u₁ h₁ u₂ h₂) = (ℝ ∙ pencil u₁ h₁ u₂ h₂)ᗮ := by
  exact VacuusResonus.span_ridgeFlat hli hh₁ hh₂

theorem vacuusPlate_polar {R : Set E} {a b : E} (hli : LinearIndependent ℝ ![a, b])
    (hR : (affineSpan ℝ R : Set E) = ridgeFlat a 1 b 1) :
    Submodule.span ℝ R = (ℝ ∙ (a - b))ᗮ := by
  exact VacuusResonus.vacuusPlate_polar hli hR

theorem heart_of_symm {X : Set E} (hs : -X = X) : IsHeart X := by
  exact VacuusResonus.heart_of_symm hs

end General

section Perm
variable {n : ℕ}

/-- The flat of the permutohedron ridge `(B₁, B₂, B₃)` inside `∑ y = 0`. -/
def permFlat (B₁ B₂ B₃ : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {y | ∑ i ∈ B₁, y i = (B₁.card : ℝ) * ((B₂.card : ℝ) + B₃.card) / 2 ∧
       ∑ i ∈ B₁ ∪ B₂, y i = ((B₁.card : ℝ) + B₂.card) * B₃.card / 2 ∧ ∑ i, y i = 0}

theorem span_permFlat {B₁ B₂ B₃ : Finset (Fin n)} (h12 : Disjoint B₁ B₂) (h13 : Disjoint B₁ B₃)
    (h23 : Disjoint B₂ B₃) (hu : B₁ ∪ B₂ ∪ B₃ = univ) (ha : B₁.Nonempty) (hb : B₂.Nonempty) (hc : B₃.Nonempty) :
    (Submodule.span ℝ (permFlat B₁ B₂ B₃) : Set (Fin n → ℝ)) =
      {y | ∑ i, y i = 0 ∧ (B₃.card : ℝ) * ((B₁.card : ℝ) + B₂.card) * ∑ i ∈ B₁, y i +
        (B₁.card : ℝ) * ((B₂.card : ℝ) + B₃.card) * ∑ i ∈ B₃, y i = 0} := by
  exact congrArg SetLike.coe (VacuusResonus.span_permFlat h12 h13 h23 hu ha hb hc)

end Perm

section Webs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem web_iff {P : Set E} (hc : Convex ℝ P) (hs : ∀ x ∈ P, -x ∈ P)
    (hi : (interior P).Nonempty) {f : E →L[ℝ] ℝ} (hf : f ≠ 0) {h : ℝ} (hh : IsLUB (f '' P) h)
    (Λ : AddSubgroup E) :
    (∀ lam ∈ Λ, ∀ μ ∈ Λ, (∃ x ∈ interior ((fun y => y - μ) ⁻¹' P), f x = f lam) → f lam = f μ) ↔
      ∀ ν ∈ Λ, f ν = 0 ∨ h ≤ |f ν| := by
  exact VacuusResonus.web_iff hc hs hi hf hh Λ

end Webs

end VR
