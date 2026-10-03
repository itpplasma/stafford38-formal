module
public import Stafford38.Geometry.SameWitness.CommonOpenArc
public import Stafford38.Geometry.SameWitness.ChartGroundMap
public import Stafford38.Geometry.A0ChartFormalEtale
public import Stafford38.Geometry.EtaleGenericOpenExtraAwayB

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Stafford38.Geometry.SameWitness

open Stafford38.Geometry.A0ChartFormalEtale
open Stafford38.Geometry.EtaleGenericOpenTransport
open Stafford38.Geometry.GeneralDivisorialVisibleFrame
open Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale
open Stafford38.Geometry.ProjectiveChartSameFieldOverlap

universe u

/-- Polynomial coordinates compose with a ground-compatible map to an open
algebra without installing another scalar action. -/
private def coordinateMapToOpen
    {k R B U : Type u} [CommSemiring k] [Semiring R] [Semiring B] [Semiring U]
    [Algebra k R] [Algebra k B] [Algebra k U]
    (f : R →ₐ[k] B) (F : B →+* U)
    (hF : F.comp (algebraMap k B) = algebraMap k U) : R →ₐ[k] U where
  toRingHom := F.comp f.toRingHom
  commutes' c := (congrArg F (f.commutes c)).trans (RingHom.congr_fun hF c)

/-- Point-local formal étaleness transports to the explicit polynomial map
on the common open (paper proof, common-open étale step). -/
private theorem formallyEtale_coordinateMapToOpen
    {k R B Q : Type u} [Field k] [CommRing R] [CommRing B] [CommRing Q]
    [Algebra k R] [Algebra k B] [Algebra k Q] [Algebra Q B]
    (fCoord : R →ₐ[k] B) (M : Ideal B) [M.IsPrime]
    (hEtM : letI : Algebra R B := fCoord.toRingHom.toAlgebra
      Algebra.FormallyEtale R (Localization.AtPrime M))
    (f : Q) (e : Localization.Away f ≃ₐ[Q] Localization.Away (algebraMap Q B f))
    (g : Q)
    (hbase : (genericOpenExtraAwayBMap M f e g).comp (algebraMap k B) =
      algebraMap k (genericOpenExtraAwayB M f e g)) :
    @Algebra.FormallyEtale R (genericOpenExtraAwayB M f e g) _ _
      (@RingHom.toAlgebra R (genericOpenExtraAwayB M f e g) inferInstance inferInstance
        (coordinateMapToOpen fCoord (genericOpenExtraAwayBMap M f e g) hbase).toRingHom) := by
  letI : Algebra R B := fCoord.toRingHom.toAlgebra
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hEtM
  let Cq := genericOpenRing M f e
  let U := genericOpenExtraAwayB M f e g
  letI : Algebra R Cq := ((algebraMap B Cq).comp fCoord.toRingHom).toAlgebra
  let rawAction : Algebra R U := Algebra.compHom U (algebraMap R Cq)
  have hRaw : @Algebra.FormallyEtale R U _ _ rawAction :=
    formallyEtale_genericOpenExtraAway_of_pointLocal M f e g
  have hAction : rawAction =
      (@RingHom.toAlgebra R (genericOpenExtraAwayB M f e g) inferInstance inferInstance
        (coordinateMapToOpen fCoord (genericOpenExtraAwayBMap M f e g) hbase).toRingHom) := by
    apply Algebra.algebra_ext
    intro x
    rfl
  exact hAction ▸ hRaw

/-- The original-chart map and selected polynomial coordinates are k-algebra
maps on the same common open, with the formally-etale structures required by
the affine-fibre endpoint (paper proof, common-open étale step). -/
structure CommonOpenEtaleData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords) where
  φk : OriginalAffineChartQuotient (k := k) P →ₐ[k] arc.common.U
  ψU : MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
      →ₐ[k] arc.common.U
  hψAction :
    letI : arc.common.M.IsMaximal := arc.common.hM
    let B := actualSelectedNormalization P w
    let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
    ((algebraMap arc.common.Cq arc.common.U).comp
      ((algebraMap B arc.common.Cq).comp
        (@AlgHom.toRingHom k R B inferInstance inferInstance inferInstance
          inferInstance coords.coeff.toAlgebra coords.fFin))).toAlgebra =
      (@RingHom.toAlgebra (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) arc.common.U inferInstance inferInstance ψU.toRingHom)
  hφEtale : @Algebra.FormallyEtale
    (OriginalAffineChartQuotient (k := k) P) arc.common.U _ _
    (@RingHom.toAlgebra (OriginalAffineChartQuotient (k := k) P) arc.common.U inferInstance inferInstance φk.toRingHom)
  hψEtale : @Algebra.FormallyEtale
    (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k)
    arc.common.U _ _ (@RingHom.toAlgebra (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) arc.common.U inferInstance inferInstance ψU.toRingHom)

/-- The T13 ground-map identity extends to the inherited k-algebra structure
on the common open by the actual normalization map (paper proof, common-open
étale step). -/
private theorem originalChartToCommonOpen_groundMap_k
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords) :
    arc.common.φ.comp
      (algebraMap k (OriginalAffineChartQuotient (k := k) P)) =
        algebraMap k arc.common.U := by
  letI : arc.common.M.IsMaximal := arc.common.hM
  let Q := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  let qToU : Q →+* arc.common.U :=
    (algebraMap arc.common.Cq arc.common.U).comp (algebraMap Q arc.common.Cq)
  have hφQ := originalAffineChartToCommonOpen_groundMap
    P setup.j arc.common.hxj arc.common.hsel arc.common.M setup.f setup.e
  have hφQ' : arc.common.φ.comp
      (algebraMap k (OriginalAffineChartQuotient (k := k) P)) =
        qToU.comp (algebraMap k Q) := by
    change arc.common.φ.comp
      (algebraMap k (OriginalAffineChartQuotient (k := k) P)) =
        qToU.comp (algebraMap k Q) at hφQ
    exact hφQ
  have hcoeff : @algebraMap k B _ _ coords.coeff.toAlgebra =
      (algebraMap Q B).comp (algebraMap k Q) := by
    rw [coords.hcoeff]
    apply RingHom.ext
    intro c
    rfl
  apply RingHom.ext
  intro c
  have hφc := congrArg (fun f : k →+* arc.common.U => f c) hφQ'
  have hQc := congrArg (fun f : Q →+* arc.common.U => f (algebraMap k Q c))
    arc.common.hbaseMap
  have hkUc := congrArg (fun f : k →+* arc.common.U => f c) arc.hbaseMap
  have hcoeffc := congrArg (fun f : k →+* B => f c) hcoeff
  calc
    arc.common.φ (algebraMap k (OriginalAffineChartQuotient (k := k) P) c) =
        qToU (algebraMap k Q c) := hφc
    _ = genericOpenExtraAwayBMap arc.common.M setup.f setup.e arc.common.g
        (algebraMap Q B (algebraMap k Q c)) := by
          exact hQc.symm
    _ = genericOpenExtraAwayBMap arc.common.M setup.f setup.e arc.common.g
        (@algebraMap k B _ _ coords.coeff.toAlgebra c) := by
          exact congrArg (genericOpenExtraAwayBMap arc.common.M setup.f setup.e arc.common.g)
            hcoeffc.symm
    _ = algebraMap k arc.common.U c := hkUc

/-- The common-open étale maps are obtained from the selected chart map and
the retained ground-point formal-etale certificate. -/
theorem nonempty_commonOpenEtaleData
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (setup : ChartSetup hm P w)
    (coords : CoordinatePresentation hm P w setup)
    (arc : CommonOpenArcData hm P w setup coords) :
    Nonempty (CommonOpenEtaleData hm P w setup coords arc) := by
  classical
  letI : arc.common.M.IsMaximal := arc.common.hM
  let B := actualSelectedNormalization P w
  let Q := actualSelectedChartAlgebra P w
  let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
  let fFin : R →+* B := @AlgHom.toRingHom k R B
    inferInstance inferInstance inferInstance inferInstance coords.coeff.toAlgebra coords.fFin
  let φk : OriginalAffineChartQuotient (k := k) P →ₐ[k] arc.common.U :=
    { toRingHom := arc.common.φ
      commutes' := fun c =>
        congrArg (fun f : k →+* arc.common.U => f c)
          (originalChartToCommonOpen_groundMap_k hm P w setup coords arc) }
  let ψU : R →ₐ[k] arc.common.U := @coordinateMapToOpen k R B arc.common.U
    inferInstance inferInstance inferInstance inferInstance inferInstance
    coords.coeff.toAlgebra _ coords.fFin
    (genericOpenExtraAwayBMap arc.common.M setup.f setup.e arc.common.g) arc.hbaseMap
  have hφEtale : @Algebra.FormallyEtale
      (OriginalAffineChartQuotient (k := k) P) arc.common.U _ _
      (@RingHom.toAlgebra (OriginalAffineChartQuotient (k := k) P) arc.common.U inferInstance inferInstance φk.toRingHom) := by
    exact formallyEtale_originalAffineChartToCommonOpen
      P setup.j arc.common.hxj arc.common.hsel arc.common.M setup.f setup.e
  have hψAction : ((algebraMap arc.common.Cq arc.common.U).comp
      ((algebraMap B arc.common.Cq).comp fFin)).toAlgebra =
        (@RingHom.toAlgebra (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k) arc.common.U inferInstance inferInstance ψU.toRingHom) := by
    apply Algebra.algebra_ext
    intro x
    rfl
  have hψEtale : @Algebra.FormallyEtale R arc.common.U _ _
      (@RingHom.toAlgebra R arc.common.U inferInstance inferInstance ψU.toRingHom) := by
    apply @formallyEtale_coordinateMapToOpen k R B Q
      inferInstance inferInstance inferInstance inferInstance inferInstance
      coords.coeff.toAlgebra inferInstance inferInstance coords.fFin
      arc.common.M (inferInstance : arc.common.M.IsPrime) arc.common.hEtM
      setup.f setup.e arc.common.g arc.hbaseMap
  exact ⟨{
    φk := φk
    ψU := ψU
    hφEtale := hφEtale
    hψEtale := hψEtale
    hψAction := hψAction
  }⟩

end Stafford38.Geometry.SameWitness

end
