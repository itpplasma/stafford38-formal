module
public import Stafford38.MathlibCompat.MvPolynomialCoeff
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

open MvPolynomial


namespace Stafford38.Geometry.TiltedArcAvoidance

set_option autoImplicit false

variable {k : Type*} [Field k] [Infinite k]

/-- Over an infinite field, a nonzero polynomial has a nonzero value somewhere. -/
theorem exists_eval_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) k) (hp : p ≠ 0) :
    ∃ x : Fin n → k, MvPolynomial.eval x p ≠ 0 := by
  induction n with
  | zero =>
      let x : Fin 0 → k := Fin.elim0
      refine ⟨x, ?_⟩
      have hcoeff : p.coeff 0 ≠ 0 := by
        intro hz
        apply hp
        ext d
        have hd : d = 0 := Subsingleton.elim _ _
        subst d
        simpa using hz
      have hx0 : x = (0 : Fin 0 → k) := Subsingleton.elim _ _
      rw [hx0, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
      exact hcoeff
  | succ n ih =>
      let P : Polynomial (MvPolynomial (Fin n) k) := MvPolynomial.finSuccEquiv k n p
      have hP : P ≠ 0 := by
        intro h
        apply hp
        exact (MvPolynomial.finSuccEquiv k n).injective h
      obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
        by_contra h
        push Not at h
        exact hP (Polynomial.ext fun i => h i)
      obtain ⟨y, hy⟩ := ih (P.coeff i) hi
      let Q : Polynomial k := Polynomial.map (MvPolynomial.eval y) P
      have hQ : Q ≠ 0 := by
        intro h
        apply hy
        have hc := congrArg (fun q : Polynomial k => q.coeff i) h
        simpa [Q, Polynomial.coeff_map] using hc
      have hdeg : Q.natDegree < Cardinal.mk k := by
        calc
          (Q.natDegree : Cardinal) < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
          _ ≤ Cardinal.mk k := Cardinal.infinite_iff.mp ‹Infinite k›
      obtain ⟨x₀, hx₀⟩ := Q.exists_eval_ne_zero_of_natDegree_lt_card hQ hdeg
      refine ⟨Fin.cons x₀ y, ?_⟩
      rw [MvPolynomial.eval_eq_eval_mv_eval' y x₀ p]
      simpa [Q] using hx₀

/-- A nonzero homogeneous polynomial is nonzero somewhere with its first coordinate fixed to 1.
The distinguished coordinate represents the original t-axis. -/
theorem exists_eval_ne_zero_first_one {n r : ℕ}
    (p : MvPolynomial (Fin (n + 1)) k) (hp : p.IsHomogeneous r) (hp0 : p ≠ 0) :
    ∃ x : Fin n → k, MvPolynomial.eval (Fin.cons 1 x) p ≠ 0 := by
  let P : Polynomial (MvPolynomial (Fin n) k) := MvPolynomial.finSuccEquiv k n p
  have hP : P ≠ 0 := by
    intro h
    apply hp0
    exact (MvPolynomial.finSuccEquiv k n).injective h
  obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (Polynomial.ext fun i => h i)
  have hir : i ≤ r := by
    have hbound : P.natDegree ≤ r := by
      rw [MvPolynomial.natDegree_finSuccEquiv]
      calc
        MvPolynomial.degreeOf 0 p ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
        _ = r := hp.totalDegree hp0
    by_contra h
    have hlt : P.natDegree < i := lt_of_le_of_lt hbound (Nat.lt_of_not_ge h)
    exact hi (Polynomial.coeff_eq_zero_of_natDegree_lt hlt)
  have hhom (j : ℕ) (hj : j ∈ Finset.range (r + 1)) :
      (P.coeff j).IsHomogeneous (r - j) := by
    apply hp.finSuccEquiv_coeff_isHomogeneous
    have hjle : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    omega
  let q : MvPolynomial (Fin n) k := ∑ j ∈ Finset.range (r + 1), P.coeff j
  have hcomp : MvPolynomial.homogeneousComponent (r - i) q = P.coeff i := by
    dsimp [q]
    rw [map_sum, Finset.sum_eq_single i]
    · rw [MvPolynomial.homogeneousComponent_of_mem (hhom i (Finset.mem_range.mpr (Nat.lt_succ_of_le hir)))]
      simp
    · intro j hj hji
      rw [MvPolynomial.homogeneousComponent_of_mem (hhom j hj)]
      have hjle : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hne : r - i ≠ r - j := by omega
      simp [hne]
    · intro hi'
      exact (hi' (Finset.mem_range.mpr (Nat.lt_succ_of_le hir))).elim
  have hq : q ≠ 0 := by
    intro hq
    have := congrArg (MvPolynomial.homogeneousComponent (r - i)) hq
    rw [hcomp] at this
    exact hi (by simpa using this)
  obtain ⟨x, hx⟩ := exists_eval_ne_zero q hq
  refine ⟨x, ?_⟩
  rw [MvPolynomial.eval_eq_eval_mv_eval' x 1 p]
  have hPdeg : P.natDegree ≤ r := by
    rw [MvPolynomial.natDegree_finSuccEquiv]
    calc
      MvPolynomial.degreeOf 0 p ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
      _ = r := hp.totalDegree hp0
  have hQdeg : (Polynomial.map (MvPolynomial.eval x) P).natDegree ≤ r :=
    (Polynomial.natDegree_map_le).trans hPdeg
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQdeg)]
  simp [Polynomial.coeff_map, ← map_sum]
  exact hx

private def alphaProduct {n : ℕ} (α : Fin n → k) (d : Fin n →₀ ℕ) : k :=
  ∏ i ∈ d.support, α i ^ d i

omit [Infinite k] in
private theorem tilt_prod {n : ℕ} (α : Fin n → k) (d : Fin n →₀ ℕ) :
    d.prod (fun i e =>
      (MvPowerSeries.C (α i) * MvPowerSeries.X (PUnit.unit : PUnit)) ^ e) =
        MvPowerSeries.C (alphaProduct α d) * MvPowerSeries.X PUnit.unit ^ d.degree := by
  classical
  rw [Finsupp.prod]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  · dsimp [alphaProduct]
    calc
      (∏ i ∈ d.support, MvPowerSeries.C (α i) ^ d i) =
          ∏ i ∈ d.support, MvPowerSeries.C ((α i) ^ d i) := by simp
      _ = MvPowerSeries.C (∏ i ∈ d.support, (α i) ^ d i) := by
        exact (map_prod (MvPowerSeries.C : k →+* MvPowerSeries PUnit k)
          (fun i => (α i) ^ d i) d.support).symm
  · rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

omit [Infinite k] in
/-- Substituting a linear t-axis into a homogeneous polynomial gives its value at the direction
vector, times the corresponding t-monomial. -/
private theorem subst_homogeneous_polynomial {n r : ℕ}
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous r) (α : Fin n → k) :
    MvPowerSeries.subst
      (fun i => MvPowerSeries.C (α i) * MvPowerSeries.X (PUnit.unit : PUnit))
      (p : MvPowerSeries (Fin n) k) =
        MvPowerSeries.C (MvPolynomial.eval α p) * MvPowerSeries.X PUnit.unit ^ r := by
  classical
  let a := fun i : Fin n => MvPowerSeries.C (α i) * MvPowerSeries.X (PUnit.unit : PUnit)
  have ha : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by simp [a])
  have hmono (d : Fin n →₀ ℕ) (c : k) :
      MvPolynomial.aeval a (MvPolynomial.monomial d c : MvPolynomial (Fin n) k) =
        MvPowerSeries.C c * d.prod (fun i e => a i ^ e) :=
    MvPolynomial.aeval_monomial a d c
  rw [← MvPowerSeries.substAlgHom_apply ha, MvPowerSeries.substAlgHom_coe ha]
  conv_lhs => rw [p.as_sum, map_sum]
  have hdeg (d : Fin n →₀ ℕ) (hd : d ∈ p.support) : d.degree = r := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  calc
    (∑ d ∈ p.support,
        MvPolynomial.aeval a (MvPolynomial.monomial d (p.coeff d))) =
        ∑ d ∈ p.support,
          MvPowerSeries.C (p.coeff d) * d.prod (fun i e => a i ^ e) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hmono d (p.coeff d)
    _ =
        ∑ d ∈ p.support,
          MvPowerSeries.C (p.coeff d * alphaProduct α d) *
            MvPowerSeries.X PUnit.unit ^ r := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [tilt_prod, hdeg d hd]
      rw [map_mul]
      simp [alphaProduct, mul_assoc]
    _ = MvPowerSeries.C
          (∑ d ∈ p.support, p.coeff d * alphaProduct α d) *
          MvPowerSeries.X PUnit.unit ^ r := by
      rw [← Finset.sum_mul, ← map_sum]
    _ = MvPowerSeries.C (MvPolynomial.eval α p) * MvPowerSeries.X PUnit.unit ^ r := by
      rw [MvPolynomial.eval_eq]
      simp [alphaProduct]

/-- A nonzero formal series remains nonzero on some tilted t-axis. The first input variable is
fixed to `t`; only the transverse variables are tilted by constants. -/
theorem exists_tilt_subst_ne_zero {n : ℕ}
    (f : MvPowerSeries (Fin (n + 1)) k) (hf : f ≠ 0) :
    ∃ α : Fin n → k,
      MvPowerSeries.subst
        (fun i => MvPowerSeries.C ((Fin.cons 1 α : Fin (n + 1) → k) i) *
          MvPowerSeries.X (PUnit.unit : PUnit)) f ≠ 0 := by
  have hfinite : f.order.toNat = f.order := MvPowerSeries.ne_zero_iff_order_finite.mp hf
  let r : ℕ := f.order.toNat
  have hr : f.order = (r : ℕ∞) := hfinite.symm
  have horderCoeff := f.exists_coeff_ne_zero_and_order hfinite
  obtain ⟨d, hcoeff, hdegree⟩ := horderCoeff
  have hdegreeR : d.degree = r := by
    rw [hr] at hdegree
    exact_mod_cast hdegree
  let h : MvPowerSeries (Fin (n + 1)) k := f.homogeneousComponent r
  have hh : h.IsHomogeneous r := by
    exact MvPowerSeries.isHomogeneous_homogeneousComponent f r
  let q : MvPolynomial (Fin (n + 1)) k := h.truncTotal (r + 1)
  let p : MvPolynomial (Fin (n + 1)) k := MvPolynomial.homogeneousComponent r q
  have hp : p.IsHomogeneous r := MvPolynomial.homogeneousComponent_isHomogeneous r q
  have hqcoeff : q.coeff d ≠ 0 := by
    dsimp [q]
    have hd : d.degree < r + 1 := by rw [hdegreeR]; omega
    have htrunc : MvPolynomial.coeff d (MvPowerSeries.truncTotal (r + 1) h) =
        MvPowerSeries.coeff d h := by
      simpa [MvPolynomial.coeff] using
        (MvPowerSeries.coeff_truncTotal (p := h) hd)
    rw [htrunc]
    simpa [h, MvPowerSeries.coeff_homogeneousComponent, hdegreeR] using hcoeff
  have hp0 : p ≠ 0 := by
    intro hzero
    have hz := congrArg (fun z : MvPolynomial (Fin (n + 1)) k => z.coeff d) hzero
    apply hqcoeff
    dsimp [p] at hz
    have hz' : AddMonoidAlgebra.coeff (MvPolynomial.homogeneousComponent r q) d = 0 := by
      simpa [MvPolynomial.coeff] using hz
    rw [MvPolynomial.coeff_homogeneousComponent r q d, ite_eq_left hdegreeR] at hz'
    change MvPolynomial.coeff d q = 0 at hz'
    exact hz'
  have hpseries : h = (p : MvPowerSeries (Fin (n + 1)) k) := by
    ext e
    by_cases he : e.degree = r
    ·
      simp [p, q, MvPolynomial.coeff_coe, MvPolynomial.coeff_homogeneousComponent,
        MvPowerSeries.coeff_truncTotal, he]
    · have hz : MvPowerSeries.coeff e h = 0 := hh.coeff_eq_zero he
      simp [p, MvPolynomial.coeff_coe, MvPolynomial.coeff_homogeneousComponent, he, hz]
  obtain ⟨α, hEval⟩ := exists_eval_ne_zero_first_one p hp hp0
  let a : Fin (n + 1) → MvPowerSeries PUnit k := fun i =>
    MvPowerSeries.C ((Fin.cons 1 α : Fin (n + 1) → k) i) *
      MvPowerSeries.X (PUnit.unit : PUnit)
  have hconst : ∀ i, MvPowerSeries.constantCoeff (a i) = 0 := by
    intro i
    simp [a]
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero hconst
  have hlow (i : ℕ) (hi : i < r) : f.homogeneousComponent i = 0 := by
    apply f.homogeneousComponent_of_lt_order_eq_zero
    rw [hr]
    exact_mod_cast hi
  have hsum :
    (∑ i ∈ Finset.range (r + 1), (f.homogeneousComponent i).subst a) =
        (f.homogeneousComponent r).subst a := by
    rw [Finset.sum_eq_single r]
    · intro i hi hir
      have hi' : i < r + 1 := Finset.mem_range.mp hi
      have hil : i < r := by omega
      rw [hlow i hil]
      rw [← MvPowerSeries.substAlgHom_apply ha]
      exact (MvPowerSeries.substAlgHom ha).map_zero
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self r))).elim
  have htrunc :
      MvPowerSeries.truncTotal (r + 1) (f.subst a) =
        ((f.homogeneousComponent r).subst a).truncTotal (r + 1) := by
    rw [MvPowerSeries.truncTotal_subst_eq_truncTotal_sum_subst ha hconst, hsum]
  let e : PUnit →₀ ℕ := Finsupp.single PUnit.unit r
  have hedegree : e.degree = r := by simp [e, Finsupp.degree_single]
  have hebelow : e.degree < r + 1 := by omega
  have hcoefTrunc := congrArg
    (fun z : MvPolynomial PUnit k => AddMonoidAlgebra.coeff z e) htrunc
  rw [MvPowerSeries.coeff_truncTotal (p := f.subst a) hebelow,
    MvPowerSeries.coeff_truncTotal (p := (f.homogeneousComponent r).subst a) hebelow]
    at hcoefTrunc
  have hsub : (f.homogeneousComponent r).subst a = (p : MvPowerSeries (Fin (n + 1)) k).subst a :=
    congrArg (fun z : MvPowerSeries (Fin (n + 1)) k => MvPowerSeries.subst a z) hpseries
  have hcoefEval :
      MvPowerSeries.coeff e ((f.homogeneousComponent r).subst a) =
        MvPolynomial.eval (Fin.cons 1 α : Fin (n + 1) → k) p := by
    rw [hsub, subst_homogeneous_polynomial p hp (Fin.cons 1 α)]
    simp [e, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]
  refine ⟨α, ?_⟩
  intro hzero
  apply hEval
  rw [← hcoefEval, ← hcoefTrunc, hzero]
  simp

#print axioms exists_tilt_subst_ne_zero

end Stafford38.Geometry.TiltedArcAvoidance
