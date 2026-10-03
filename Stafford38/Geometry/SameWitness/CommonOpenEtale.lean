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

universe u

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
  φk : OriginalAffineChartQuotient (k := k) P →ₐ[k] arc.U
  ψU : MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
      →ₐ[k] arc.U
  hφEtale : @Algebra.FormallyEtale
    (OriginalAffineChartQuotient (k := k) P) arc.U _ _
    φk.toRingHom.toAlgebra
  hψEtale : @Algebra.FormallyEtale
    (MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k)
    arc.U _ _ ψU.toRingHom.toAlgebra
  hψAction : ((algebraMap arc.Cq arc.U).comp
      ((algebraMap (actualSelectedNormalization P w) arc.Cq).comp
        coords.fFin.toRingHom)).toAlgebra = ψU.toRingHom.toAlgebra

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
    (arc : CommonOpenArcData hm P w setup) :
    arc.φ.comp
      (algebraMap k (OriginalAffineChartQuotient (k := k) P)) =
        algebraMap k arc.U := by
  let Q := actualSelectedChartAlgebra P w
  let B := actualSelectedNormalization P w
  let qToU : Q →+* arc.U :=
    (algebraMap arc.Cq arc.U).comp (algebraMap Q arc.Cq)
  have hφQ := originalAffineChartToCommonOpen_groundMap
    P setup.j arc.hxj arc.hsel arc.M setup.f setup.e
  have hφQ' : arc.φ.comp
      (algebraMap k (OriginalAffineChartQuotient (k := k) P)) =
        qToU.comp (algebraMap k Q) := by
    change arc.φ.comp
      (algebraMap k (OriginalAffineChartQuotient (k := k) P)) =
        qToU.comp (algebraMap k Q) at hφQ
    exact hφQ
  have hcoeff : @algebraMap k B _ _ coords.coeff.toAlgebra =
      (algebraMap Q B).comp (algebraMap k Q) := by
    apply RingHom.ext
    intro c
    rfl
  apply RingHom.ext
  intro c
  have hφc := congrArg (fun f : k →+* arc.U => f c) hφQ'
  have hQc := congrArg (fun f : Q →+* arc.U => f (algebraMap k Q c))
    arc.toCommonOpenData.hbaseMap
  have hkUc := congrArg (fun f : k →+* arc.U => f c) arc.hbaseMap
  have hcoeffc := congrArg (fun f : k →+* B => f c) hcoeff
  calc
    arc.φ (algebraMap k (OriginalAffineChartQuotient (k := k) P) c) =
        qToU (algebraMap k Q c) := hφc
    _ = genericOpenExtraAwayBMap arc.M setup.f setup.e arc.g
        (algebraMap Q B (algebraMap k Q c)) := by
          simpa only [RingHom.comp_apply] using hQc.symm
    _ = genericOpenExtraAwayBMap arc.M setup.f setup.e arc.g
        (algebraMap k B c) := by
          exact congrArg (genericOpenExtraAwayBMap arc.M setup.f setup.e arc.g)
            hcoeffc.symm
    _ = algebraMap k arc.U c := hkUc

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
  let B := actualSelectedNormalization P w
  let Q := actualSelectedChartAlgebra P w
  let R := MvPolynomial (Option (Fin (@Fintype.card coords.t coords.htFinite))) k
  let φk : OriginalAffineChartQuotient (k := k) P →ₐ[k] arc.U :=
    { toRingHom := arc.φ
      commutes' := fun c =>
        congrArg (fun f : k →+* arc.U => f c)
          (originalChartToCommonOpen_groundMap_k hm P w setup coords arc) }
  let ψU : R →ₐ[k] arc.U :=
    { toRingHom :=
        (genericOpenExtraAwayBMap arc.M setup.f setup.e arc.g).comp
          coords.fFin.toRingHom
      commutes' := fun c => by
        change genericOpenExtraAwayBMap arc.M setup.f setup.e arc.g
          (coords.fFin (algebraMap k R c)) = algebraMap k arc.U c
        rw [coords.fFin.commutes c]
        exact congrArg (fun f : k →+* arc.U => f c) arc.hbaseMap }
  have hφEtale : @Algebra.FormallyEtale
      (OriginalAffineChartQuotient (k := k) P) arc.U _ _
      φk.toRingHom.toAlgebra := by
    exact formallyEtale_originalAffineChartToCommonOpen
      P setup.j arc.hxj arc.hsel arc.M setup.f setup.e
  have hψAction : ((algebraMap arc.Cq arc.U).comp
      ((algebraMap B arc.Cq).comp coords.fFin.toRingHom)).toAlgebra =
        ψU.toRingHom.toAlgebra := by
    apply Algebra.algebra_ext
    intro x
    rfl
  have hψEtaleRaw : @Algebra.FormallyEtale R arc.U _ _
      ((algebraMap arc.Cq arc.U).comp
        ((algebraMap B arc.Cq).comp coords.fFin.toRingHom)).toAlgebra := by
    exact @formallyEtale_genericOpenExtraAway_of_pointLocal
      R _ Q _ B _ (inferInstance : Algebra Q B)
      coords.fFin.toRingHom.toAlgebra arc.M (inferInstance : arc.M.IsPrime)
      setup.f setup.e arc.g arc.hEtM
  have hψEtale : @Algebra.FormallyEtale R arc.U _ _
      ψU.toRingHom.toAlgebra := by
    rw [← hψAction]
    exact hψEtaleRaw
  exact ⟨{
    φk := φk
    ψU := ψU
    hφEtale := hφEtale
    hψEtale := hψEtale
    hψAction := hψAction
  }⟩

end Stafford38.Geometry.SameWitness

end
