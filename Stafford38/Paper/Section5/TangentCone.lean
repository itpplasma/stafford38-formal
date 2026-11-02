module

public import Stafford38.Geometry.AffineConormalSpan
public import Stafford38.Geometry.PowerSeriesArcTangency
public import Stafford38.Geometry.ProjectiveConormalDehomogenization

@[expose] public section

/-!
# Lemmas 5.12(b), 5.13 and the cone part of Lemma 5.12(a)

Section 5.2 works at the generic point `y = (q_1/q_0, …, q_n/q_0)` with
coordinates in a field `L` (there `L = κ((t))`).  `Θ_y` is the tangent space
cut out by the differentials of the equations, the map
`ρ(v)_i = (v_i q_0 - q_i v_0) / q_0²` sends a homogeneous vector to the affine
direction it induces at `q`, and `𝒞 = ρ⁻¹(Θ_y)` is the affine cone over the
projective tangent plane.

In Lean `Θ_y` is `zariskiTangentSpace y (𝔭 ⊗ L)`, the common kernel of the
differentials of all equations with coefficients extended to `L`; this is the
paper's `⋂_{f ∈ 𝔭} ker df_y`, because `L`-combinations of equations that vanish
at `y` have the same differentials as the corresponding combinations of the
equations themselves.
-/

namespace Stafford38.Paper.Section5

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ProjectiveConormalDehomogenization

noncomputable section

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] {n : ℕ}

/-- The paper's `ρ : L^{n+1} → L^n`, `ρ(v)_i = (v_i q_0 - q_i v_0) / q_0²`. -/
def rho (q : Fin (n + 1) → L) : (Fin (n + 1) → L) →ₗ[L] (Fin n → L) where
  toFun v i := (v i.succ * q 0 - q i.succ * v 0) / q 0 ^ 2
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem rho_apply (q v : Fin (n + 1) → L) (i : Fin n) :
    rho q v i = (v i.succ * q 0 - q i.succ * v 0) / q 0 ^ 2 := rfl

/-- The tangent space `Θ_y` at `y = q_i / q_0`. -/
def tangentSpaceAt (q : Fin (n + 1) → L) (I : Ideal (MvPolynomial (Fin n) k)) :
    Submodule L (Fin n → L) :=
  zariskiTangentSpace (dehomogenizedPoint q) (I.map (MvPolynomial.map (algebraMap k L)))

/-- The affine cone `𝒞 = ρ⁻¹(Θ_y)` over the projective tangent plane. -/
def tangentCone (q : Fin (n + 1) → L) (I : Ideal (MvPolynomial (Fin n) k)) :
    Submodule L (Fin (n + 1) → L) :=
  (tangentSpaceAt q I).comap (rho q)

/-- `ρ` is onto: `(0, q_0 w)` is sent to `w`. -/
theorem rho_surjective (q : Fin (n + 1) → L) (hq0 : q 0 ≠ 0) :
    Function.Surjective (rho q) := by
  intro w
  refine ⟨Fin.cons 0 (fun i ↦ q 0 * w i), ?_⟩
  funext i
  simp only [rho_apply, Fin.cons_succ, Fin.cons_zero, mul_zero, sub_zero]
  field_simp

/-- The kernel of `ρ` is the line `L q`. -/
theorem ker_rho (q : Fin (n + 1) → L) (hq0 : q 0 ≠ 0) :
    LinearMap.ker (rho q) = Submodule.span L {q} := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [Submodule.mem_span_singleton]
    refine ⟨v 0 / q 0, ?_⟩
    funext a
    refine Fin.cases ?_ (fun i ↦ ?_) a
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · have hi := congrFun hv i
      simp only [rho_apply, Pi.zero_apply, div_eq_zero_iff, pow_eq_zero_iff, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, hq0, or_false, sub_eq_zero] at hi
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_eq_iff hq0]
      linear_combination -hi
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    funext i
    simp

/-- `ρ` maps `𝒞` onto `Θ_y`. -/
theorem rho_map_tangentCone (q : Fin (n + 1) → L) (hq0 : q 0 ≠ 0)
    (I : Ideal (MvPolynomial (Fin n) k)) :
    (tangentCone q I).map (rho q) = tangentSpaceAt q I :=
  Submodule.map_comap_eq_of_surjective (rho_surjective q hq0) _

/-- **Lemma 5.12(a), cone part.** `dim 𝒞 = dim Θ_y + 1`. -/
theorem lemma_5_12_a_cone (q : Fin (n + 1) → L) (hq0 : q 0 ≠ 0)
    (I : Ideal (MvPolynomial (Fin n) k)) :
    Module.finrank L (tangentCone q I) = Module.finrank L (tangentSpaceAt q I) + 1 := by
  classical
  let f : tangentCone q I →ₗ[L] tangentSpaceAt q I :=
    (rho q).restrict (p := tangentCone q I) (q := tangentSpaceAt q I) (fun v hv ↦ hv)
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := rho_surjective q hq0 w
    exact ⟨⟨v, hw⟩, rfl⟩
  have hq : q ∈ tangentCone q I := by
    change rho q q ∈ tangentSpaceAt q I
    have : rho q q = 0 := by
      rw [← LinearMap.mem_ker, ker_rho q hq0]
      exact Submodule.mem_span_singleton_self q
    rw [this]
    exact zero_mem _
  have hker : Module.finrank L (LinearMap.ker f) = 1 := by
    have hq' : (⟨q, hq⟩ : tangentCone q I) ≠ 0 := by
      intro h
      exact hq0 (congrFun (congrArg Subtype.val h) 0)
    rw [finrank_eq_one_iff_of_nonzero' (⟨⟨q, hq⟩, ?_⟩ : LinearMap.ker f) ?_]
    · rintro ⟨⟨v, hv⟩, hvk⟩
      have hv0 : v ∈ LinearMap.ker (rho q) := by
        rw [LinearMap.mem_ker]
        exact congrArg Subtype.val (LinearMap.mem_ker.mp hvk)
      rw [ker_rho q hq0, Submodule.mem_span_singleton] at hv0
      obtain ⟨c, rfl⟩ := hv0
      exact ⟨c, rfl⟩
    · rw [LinearMap.mem_ker]
      apply Subtype.ext
      change rho q q = 0
      rw [← LinearMap.mem_ker, ker_rho q hq0]
      exact Submodule.mem_span_singleton_self q
    · intro h
      exact hq' (congrArg Subtype.val h)
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hker] at this
  omega

/-- **Lemma 5.12(b).** If the equations vanish at `y`, then `δq ∈ 𝒞` for every
`K`-derivation `δ` of `L`, and `q ∈ 𝒞`. -/
theorem lemma_5_12_b (q : Fin (n + 1) → L) (hq0 : q 0 ≠ 0)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hbase : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k L) (dehomogenizedPoint q) f = 0) :
    (∀ δ : Derivation k L L, (fun a ↦ δ (q a)) ∈ tangentCone q I) ∧
      q ∈ tangentCone q I := by
  constructor
  · intro δ
    -- `δ(f(y)) = df_y · δy`, so `δy ∈ Θ_y`.
    have htan := Stafford38.Geometry.PowerSeriesArcTangency.derivationVector_mem_zariskiTangentSpace_of_eval₂_eq_zero
      δ I (dehomogenizedPoint q) hbase
    -- Quotient rule: `ρ(δq) = δy`.
    have hquot : rho q (fun a ↦ δ (q a)) = fun i ↦ δ (dehomogenizedPoint q i) := by
      funext i
      rw [rho_apply, dehomogenizedPoint, Derivation.leibniz_div]
      simp only [smul_eq_mul]
      field_simp
    change rho q (fun a ↦ δ (q a)) ∈ tangentSpaceAt q I
    rw [hquot]
    exact htan
  · change rho q q ∈ tangentSpaceAt q I
    have : rho q q = 0 := by
      rw [← LinearMap.mem_ker, ker_rho q hq0]
      exact Submodule.mem_span_singleton_self q
    rw [this]
    exact zero_mem _

/-- **Lemma 5.13.** A row vector annihilating `𝒞` has its affine part
`(ℓ_1, …, ℓ_n)` in `span {df_y : f ∈ 𝔭}`. -/
theorem lemma_5_13 (q : Fin (n + 1) → L) (hq0 : q 0 ≠ 0)
    (I : Ideal (MvPolynomial (Fin n) k)) (ell : Fin (n + 1) → L)
    (hell : ∀ v ∈ tangentCone q I, ∑ a, ell a * v a = 0) :
    coordinateCovector (fun i : Fin n ↦ ell i.succ) ∈
      equationCovectorSpan (dehomogenizedPoint q)
        (I.map (MvPolynomial.map (algebraMap k L))) := by
  rw [← affineConormalSpace_eq_equationCovectorSpan, affineConormalSpace,
    Submodule.mem_dualAnnihilator]
  intro w hw
  -- `ρ(𝒞) = Θ_y`.
  have hw' : w ∈ (tangentCone q I).map (rho q) := by
    rw [rho_map_tangentCone q hq0]
    exact hw
  obtain ⟨v, hv, rfl⟩ := hw'
  have hq : q ∈ tangentCone q I := by
    change rho q q ∈ tangentSpaceAt q I
    have : rho q q = 0 := by
      rw [← LinearMap.mem_ker, ker_rho q hq0]
      exact Submodule.mem_span_singleton_self q
    rw [this]
    exact zero_mem _
  -- `ℓ(q) = 0` and `ℓ(v) = 0` give `Σ ℓ_i ρ(v)_i = 0`.
  have hellq := hell q hq
  have hellv := hell v hv
  rw [Fin.sum_univ_succ] at hellq hellv
  rw [coordinateCovector_apply]
  simp only [rho_apply]
  have hsum : ∑ i : Fin n, ell i.succ * ((v i.succ * q 0 - q i.succ * v 0) / q 0 ^ 2) =
      (q 0 * ∑ i : Fin n, ell i.succ * v i.succ -
        v 0 * ∑ i : Fin n, ell i.succ * q i.succ) / q 0 ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hsum]
  have h1 : ∑ i : Fin n, ell i.succ * v i.succ = -(ell 0 * v 0) := by linear_combination hellv
  have h2 : ∑ i : Fin n, ell i.succ * q i.succ = -(ell 0 * q 0) := by linear_combination hellq
  rw [h1, h2]
  ring_nf

#print axioms lemma_5_12_a_cone
#print axioms lemma_5_12_b
#print axioms lemma_5_13

end

end Stafford38.Paper.Section5
