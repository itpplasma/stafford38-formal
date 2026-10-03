module
public import Stafford38.Geometry.AffineConormalSpan
public import Stafford38.Geometry.GenericPointKaehlerConormal
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section

set_option autoImplicit false

namespace Stafford38.Geometry.EtaleTangentKernel

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

/-- Chain rule for a derivation out of a polynomial algebra into an arbitrary
field-valued point. -/
theorem derivation_eq_sum_pderiv
    {S : Type*} [Field S] [Algebra k S]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S]
    (D : Derivation k (MvPolynomial (Fin n) k) S)
    (q : Fin n → S)
    (halg : ∀ p, algebraMap (MvPolynomial (Fin n) k) S p = aeval q p)
    (f : MvPolynomial (Fin n) k) :
    D f = ∑ i, aeval q (pderiv i f) * D (X i) := by
  have hD : D = MvPolynomial.mkDerivation k (fun i => D (X i)) := by
    apply MvPolynomial.derivation_ext
    intro i
    simp [MvPolynomial.mkDerivation_X]
  calc
    D f = MvPolynomial.mkDerivation k (fun i => D (X i)) f :=
      congrArg (fun E : Derivation k (MvPolynomial (Fin n) k) S => E f) hD
    _ = ∑ i, aeval q (pderiv i f) * D (X i) :=
      Stafford38.Geometry.GenericPointKaehlerConormal.mkDerivation_eq_sum_pderiv
        q (fun i => D (X i)) halg f

/-- If an ambient polynomial derivation annihilates an ideal at a point, its
actual coordinate-value vector lies in the equation-defined Zariski tangent
space of that ideal after scalar extension. -/
theorem derivationVector_mem_zariskiTangentSpace_of_vanishes
    {S : Type*} [Field S] [Algebra k S]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S]
    (D : Derivation k (MvPolynomial (Fin n) k) S)
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin n → S)
    (halg : ∀ p, algebraMap (MvPolynomial (Fin n) k) S p = aeval q p)
    (hD : ∀ f ∈ I, D f = 0)
    (hq : ∀ f ∈ I, aeval q f = 0) :
    (fun i ↦ D (X i)) ∈ zariskiTangentSpace q
      (I.map (MvPolynomial.map (algebraMap k S))) := by
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator]
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨g, rfl⟩
      have hmap : ∀ h : MvPolynomial (Fin n) S,
          h ∈ I.map (MvPolynomial.map (algebraMap k S)) →
            MvPolynomial.eval q h = 0 ∧
              differentialCovector q h (fun i ↦ D (X i)) = 0 := by
        intro h hh
        rw [Ideal.map] at hh
        induction hh using Submodule.span_induction with
        | mem h hh =>
            rcases hh with ⟨g, hg, rfl⟩
            constructor
            · rw [MvPolynomial.eval_map]
              exact hq g hg
            · have hderiv := derivation_eq_sum_pderiv D q halg g
              rw [hD g hg] at hderiv
              simpa [differentialCovector, differentialAt,
                MvPolynomial.pderiv_map, MvPolynomial.eval_map, aeval_def] using hderiv.symm
        | zero =>
            simp [differentialCovector, differentialAt]
        | add h₁ h₂ hh₁ hh₂ ih₁ ih₂ =>
            constructor
            · rw [MvPolynomial.eval_add, ih₁.1, ih₂.1, add_zero]
            · have hi := congrArg₂ (· + ·) ih₁.2 ih₂.2
              change ∑ i, MvPolynomial.eval q
                  (MvPolynomial.pderiv i (h₁ + h₂)) * D (X i) = 0
              simp only [map_add, MvPolynomial.eval_add, add_mul]
              rw [Finset.sum_add_distrib]
              simpa [differentialCovector, differentialAt] using hi
        | smul a h hh ih =>
            constructor
            · simpa [smul_eq_mul, ih.1]
            · have ihD : ∑ i, MvPolynomial.eval q
                  (MvPolynomial.pderiv i h) * D (X i) = 0 := by
                simpa [differentialCovector, differentialAt] using ih.2
              have hprod : differentialCovector q (a * h) (fun i ↦ D (X i)) =
                  MvPolynomial.eval q h *
                      differentialCovector q a (fun i ↦ D (X i)) +
                    MvPolynomial.eval q a *
                      differentialCovector q h (fun i ↦ D (X i)) := by
                have h := congrArg (fun ψ : Module.Dual S (Fin n → S) =>
                    ψ (fun i ↦ D (X i))) (differentialCovector_mul q a h)
                simpa [smul_eq_mul] using h
              rw [show (a • h : MvPolynomial (Fin n) S) = a * h by rfl]
              rw [hprod]
              simp [ih.1, ih.2]
      exact (hmap g.1 g.2).2
  | zero => simp
  | add φ ψ hφ hψ ihφ ihψ => simpa [ihφ, ihψ]
  | smul a φ hφ ihφ => simpa [ihφ]

/-- The converse coordinate calculation: an ambient tangent vector defines the
canonical polynomial derivation, and that derivation vanishes on every equation
of the ideal. -/
theorem mkDerivation_vanishes_of_mem_zariskiTangentSpace
    {S : Type*} [Field S] [Algebra k S]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q v : Fin n → S)
    (halg : ∀ p, algebraMap (MvPolynomial (Fin n) k) S p = aeval q p)
    (hv : v ∈ zariskiTangentSpace q
      (I.map (MvPolynomial.map (algebraMap k S)))) :
    ∀ f ∈ I, MvPolynomial.mkDerivation k v f = 0 := by
  intro f hf
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator] at hv
  have hfmap : MvPolynomial.map (algebraMap k S) f ∈
      I.map (MvPolynomial.map (algebraMap k S)) := Ideal.mem_map_of_mem _ hf
  have hcov := hv (differentialCovector q (MvPolynomial.map (algebraMap k S) f))
    (Submodule.subset_span ⟨⟨MvPolynomial.map (algebraMap k S) f, hfmap⟩, rfl⟩)
  have hformula := Stafford38.Geometry.GenericPointKaehlerConormal.mkDerivation_eq_sum_pderiv
    q v halg f
  have hsum : (∑ i, aeval q (pderiv i f) * v i) =
      differentialCovector q (MvPolynomial.map (algebraMap k S) f) v := by
    simp [differentialCovector, differentialAt, MvPolynomial.pderiv_map,
      MvPolynomial.eval_map, aeval_def]
  calc
    MvPolynomial.mkDerivation k v f =
        differentialCovector q (MvPolynomial.map (algebraMap k S) f) v := by
      rw [hformula, hsum]
    _ = 0 := hcov

/-- Precomposing a genuine derivation on a target algebra along a polynomial
chart map produces an actual vector in the ambient equation tangent kernel,
provided the equations vanish in that target algebra. -/
theorem chartDerivation_mem_zariskiTangentSpace
    {n : ℕ} {B S : Type*} [CommRing B] [Field S] [Algebra k B] [Algebra k S]
    [Algebra (MvPolynomial (Fin n) k) B]
    [IsScalarTower k (MvPolynomial (Fin n) k) B]
    [Algebra B S] [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower (MvPolynomial (Fin n) k) B S]
    [IsScalarTower k B S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S]
    (D : Derivation k B S)
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin n → S)
    (halg : ∀ p, algebraMap (MvPolynomial (Fin n) k) S p = aeval q p)
    (hI : ∀ f ∈ I, algebraMap (MvPolynomial (Fin n) k) B f = 0) :
    (fun i ↦ D.compAlgebraMap (MvPolynomial (Fin n) k) (X i)) ∈
      zariskiTangentSpace q (I.map (MvPolynomial.map (algebraMap k S))) := by
  apply derivationVector_mem_zariskiTangentSpace_of_vanishes
    (D := D.compAlgebraMap (MvPolynomial (Fin n) k)) I q halg
  · intro f hf
    change D (algebraMap (MvPolynomial (Fin n) k) B f) = 0
    rw [hI f hf, map_zero]
  · intro f hf
    rw [← halg f, IsScalarTower.algebraMap_eq (MvPolynomial (Fin n) k) B S]
    simp [hI f hf]


end

end Stafford38.Geometry.EtaleTangentKernel
