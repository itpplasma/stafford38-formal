import AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

namespace Stafford38.Characteristic.LocalizedDerivationQuotient

open AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

noncomputable section

universe u

private theorem derivation_unit_inv_apply
    {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    (D : Derivation k B B) (u : Bˣ) :
    D (↑(u⁻¹) : B) = -(↑(u⁻¹) : B) * ↑(u⁻¹) * D (u : B) := by
  have hsum : (u : B) * D (↑(u⁻¹) : B) +
      (↑(u⁻¹) : B) * D (u : B) = 0 := by
    have hzero : D ((u : B) * (↑(u⁻¹) : B)) = 0 := by simp
    have h := D.leibniz (u : B) (↑(u⁻¹) : B)
    rw [hzero] at h
    simpa [smul_eq_mul] using h.symm
  have hmul : (u : B) * D (↑(u⁻¹) : B) =
      -((↑(u⁻¹) : B) * D (u : B)) := by
    exact eq_neg_of_add_eq_zero_left hsum
  have hu : IsUnit (u : B) := ⟨u, rfl⟩
  apply hu.mul_right_inj.mp
  calc
    (u : B) * D (↑(u⁻¹) : B) = -((↑(u⁻¹) : B) * D (u : B)) := hmul
    _ = (u : B) * (-(↑(u⁻¹) : B) * ↑(u⁻¹) * D (u : B)) := by
      calc
        -((↑(u⁻¹) : B) * D (u : B)) =
            -((1 : B) * ↑(u⁻¹) * D (u : B)) := by simp
        _ = -(((u : B) * (↑(u⁻¹) : B)) * ↑(u⁻¹) * D (u : B)) := by
              have heq := congrArg
                (fun z : B => -(z * (↑(u⁻¹) : B) * D (u : B))) u.val_inv
              simpa using heq.symm
        _ = (u : B) * (-(↑(u⁻¹) : B) * ↑(u⁻¹) * D (u : B)) := by ring

theorem extendDerivation_apply_mk'_cross
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (S : Submonoid A) [IsLocalization S B]
    (D : Derivation k A B) (a : A) (s : S) :
    (extendDerivation k A B S D) (IsLocalization.mk' B a s) *
        (algebraMap A B (s : A)) ^ 2 =
      algebraMap A B (s : A) * D a - algebraMap A B a * D (s : A) := by
  let E := extendDerivation k A B S D
  let u : B := algebraMap A B (s : A)
  let uunit : Bˣ := (IsLocalization.map_units B s).unit
  let ui : B := ↑(uunit⁻¹)
  let v : B := algebraMap A B a
  have hu : IsUnit u := IsLocalization.map_units B s
  have hui : u * ui = 1 := by
    change u * (↑(uunit⁻¹) : B) = 1
    rw [← hu.unit_spec]
    exact hu.unit.val_inv
  have hcomp := extendDerivation_compAlgebraMap k A B S D
  have hdu : E u = D (s : A) := by
    have h := Derivation.congr_fun hcomp (s : A)
    change E (algebraMap A B (s : A)) = D (s : A) at h
    change E u = D (s : A)
    exact h
  have hdv : E v = D a := by
    have h := Derivation.congr_fun hcomp a
    change E (algebraMap A B a) = D a at h
    change E v = D a
    exact h
  have hrepr : IsLocalization.mk' B a s = v * ui := by
    apply hu.mul_right_inj.mp
    calc
      u * IsLocalization.mk' B a s = v := by
        calc
          u * IsLocalization.mk' B a s = IsLocalization.mk' B a s * u := by ac_rfl
          _ = v := IsLocalization.mk'_spec B a s
      _ = u * (v * ui) := by
        calc
          v = v * 1 := by rw [mul_one]
          _ = v * (u * ui) := by rw [hui]
          _ = u * (v * ui) := by ac_rfl
  have hcancel : u ^ 2 * ui = u := by
    calc
      u ^ 2 * ui = u * (u * ui) := by ring
      _ = u := by rw [hui, mul_one]
  have hinv2 : u ^ 2 * ui ^ 2 = 1 := by
    rw [← mul_pow, hui, one_pow]
  calc
    E (IsLocalization.mk' B a s) * u ^ 2 =
        u ^ 2 * (v * E ui + ui * E v) := by
          rw [hrepr, Derivation.leibniz]
          simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
          ring
    _ = u * D a - v * D (s : A) := by
          have hinv : E ui = -(ui * ui * E u) := by
            simpa [ui, uunit, u, hu.unit_spec] using
              (derivation_unit_inv_apply E uunit)
          rw [hinv, hdv, hdu]
          calc
            u ^ 2 * (v * (-(ui * ui * D (s : A))) + ui * D a) =
                -(v * D (s : A) * (u ^ 2 * ui ^ 2)) +
                  (u ^ 2 * ui) * D a := by ring
            _ = u * D a - v * D (s : A) := by rw [hinv2, hcancel]; ring

end
end Stafford38.Characteristic.LocalizedDerivationQuotient
