module
public import Stafford38.Geometry.EtaleGenericOpenTransport
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Stafford38.Geometry.EtaleGenericOpenTransport
universe u v

abbrev finiteBirationalOpen
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q) : Type v :=
  Localization (M.primeCompl.map
    (algebraMap B (Localization.Away (algebraMap Q B f))))

abbrev pointLocalAwayOpen
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q) : Type v :=
  Localization.Away
    (algebraMap B (Localization.AtPrime M) (algebraMap Q B f))

/-- The genuine B-algebra structure on the generic open is induced by the
point map `B → Q_f` transported through `Q_f ≃ B_f`. -/
noncomputable def genericOpenBMap
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) : B →+* genericOpenRing M f e :=
  (algebraMap (Localization.Away f) (genericOpenRing M f e)).comp
    (genericPointMap f e)

noncomputable instance instGenericOpenBAlgebra
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    Algebra B (genericOpenRing M f e) :=
  (genericOpenBMap M f e).toAlgebra

/-- The generic-open presentation obtained from `Q_f` and the image of `B \ M`
identifies with the same open constructed from the actual local ring `B_M`.
No condition says `f` avoids `M`; the common open inverts it generically. -/
noncomputable def genericOpenEquiv_pointLocalAway_overB
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f)) :
    genericOpenRing M f e ≃ₐ[B] pointLocalAwayOpen M f := by
  let Qf := Localization.Away f
  let Bf := Localization.Away (algebraMap Q B f)
  let Cq := genericOpenRing M f e
  let Cb := finiteBirationalOpen M f
  let Bm := Localization.AtPrime M
  let Cl := pointLocalAwayOpen M f
  let Nq : Submonoid Qf := genericOpenDenominators M f e
  let Nb : Submonoid Bf := M.primeCompl.map (algebraMap B Bf)
  let Sq := IsLocalization.localizationLocalizationSubmodule
    (Submonoid.powers f) Nq
  let Sb := IsLocalization.localizationLocalizationSubmodule
    (Submonoid.powers (algebraMap Q B f)) Nb
  let Sl := IsLocalization.localizationLocalizationSubmodule
    M.primeCompl (Submonoid.powers (algebraMap B Bm (algebraMap Q B f)))
  have hcomp : (e : Qf →* Bf).comp (genericPointMap f e) = (algebraMap B Bf : B →* Bf) := by
    ext b
    change e (e.symm (algebraMap B Bf b)) = algebraMap B Bf b
    exact e.apply_symm_apply _
  have hmap : Submonoid.map (e : Qf ≃* Bf) Nq = Nb := by
    change Submonoid.map (e : Qf →* Bf)
      (Submonoid.map (genericPointMap f e) M.primeCompl) =
      Submonoid.map (algebraMap B Bf : B →* Bf) M.primeCompl
    calc
      _ = Submonoid.map ((e : Qf →* Bf).comp (genericPointMap f e)) M.primeCompl :=
        Submonoid.map_map _ _ _
      _ = _ := by rw [hcomp]
  let eQB : Cq ≃ₐ[Q] Cb :=
    IsLocalization.algEquivOfAlgEquiv (A := Q) (R := Qf) (M := Nq) Cq
      (P := Bf) (T := Nb) Cb e hmap
  let bToCb : B →+* Cb :=
    (algebraMap Bf Cb).comp (algebraMap B Bf)
  let bToCl : B →+* Cl :=
    (algebraMap Bm Cl).comp (algebraMap B Bm)
  let bToCq : B →+* Cq := genericOpenBMap M f e
  let eBL : Cb ≃ₐ[B] Cl := by
    letI : IsLocalization Sb Cb :=
      IsLocalization.localization_localization_isLocalization
        (Submonoid.powers (algebraMap Q B f)) Nb Cb
    letI : IsLocalization Sl Cl :=
      IsLocalization.localization_localization_isLocalization
        M.primeCompl
        (Submonoid.powers (algebraMap B Bm (algebraMap Q B f))) Cl
    let fB : B := algebraMap Q B f
    let fM : Bm := algebraMap B Bm fB
    have hunitF : IsUnit (bToCl fB) := by
      change IsUnit (algebraMap Bm (Localization.Away fM) fM)
      exact IsLocalization.Away.algebraMap_isUnit fM
    let bFToCl : Bf →+* Cl :=
      IsLocalization.Away.lift (algebraMap Q B f) hunitF
    have hbFComp : bFToCl.comp (algebraMap B Bf) = bToCl := by
      exact IsLocalization.Away.lift_comp (algebraMap Q B f) hunitF
    have hbFComp_apply (b : B) :
        bFToCl (algebraMap B Bf b) = bToCl b := by
      have hh := congrArg (fun g : B →+* Cl => g b) hbFComp
      simpa only [RingHom.comp_apply] using hh
    have hunitSb : ∀ s : Sb, IsUnit (bToCl s.1) := by
      intro s
      rcases IsLocalization.mem_localizationLocalizationSubmodule.mp s.2 with
        ⟨y, z, hyz⟩
      have hrepr : bToCl s.1 = bFToCl y.1 * bFToCl (algebraMap B Bf z.1) := by
        calc
          bToCl s.1 = bFToCl (algebraMap B Bf s.1) :=
            (hbFComp_apply s.1).symm
          _ = bFToCl (y.1 * algebraMap B Bf z.1) := by rw [hyz]
          _ = bFToCl y.1 * bFToCl (algebraMap B Bf z.1) := map_mul _ _ _
      rw [hrepr]
      rcases y.2 with ⟨b, hb, hyEq⟩
      have hy : IsUnit (bFToCl y.1) := by
        rw [← hyEq]
        have hu : IsUnit (algebraMap Bm Cl (algebraMap B Bm b)) := by
          exact IsUnit.map (algebraMap Bm Cl) (IsLocalization.map_units Bm ⟨b, hb⟩)
        rw [hbFComp_apply b]
        simpa [bToCl] using hu
      have hz : IsUnit (bFToCl (algebraMap B Bf z.1)) := by
        rcases (Submonoid.mem_powers_iff _ _).mp z.2 with ⟨n, hn⟩
        have hpow : bFToCl (algebraMap B Bf z.1) = bToCl fB ^ n := by
          rw [← hn]
          calc
            bFToCl (algebraMap B Bf (fB ^ n)) =
                bFToCl (algebraMap B Bf fB ^ n) := by simp only [map_pow]
            _ = bFToCl (algebraMap B Bf fB) ^ n := by rw [map_pow]
            _ = bToCl fB ^ n := by rw [hbFComp_apply fB]
        rw [hpow]
        exact IsUnit.pow _ hunitF
      exact hy.mul hz
    let bMToCb : Bm →+* Cb := IsLocalization.lift
      (M := M.primeCompl) (g := bToCb) (fun x => by
        have hden : (algebraMap B Bf x.1) ∈ Nb := ⟨x.1, x.2, rfl⟩
        exact IsLocalization.map_units Cb ⟨algebraMap B Bf x.1, hden⟩)
    have hbMComp : bMToCb.comp (algebraMap B Bm) = bToCb := by
      exact IsLocalization.lift_comp (M := M.primeCompl)
        (g := bToCb) (fun x => by
          have hden : (algebraMap B Bf x.1) ∈ Nb := ⟨x.1, x.2, rfl⟩
          exact IsLocalization.map_units Cb ⟨algebraMap B Bf x.1, hden⟩)
    have hbMComp_apply (b : B) :
        bMToCb (algebraMap B Bm b) = bToCb b := by
      have hh := congrArg (fun g : B →+* Cb => g b) hbMComp
      simpa only [RingHom.comp_apply] using hh
    have hf : IsUnit (bMToCb fM) := by
      have heq : bMToCb fM = algebraMap Bf Cb (algebraMap B Bf fB) := by
        calc
          bMToCb fM = bToCb fB := hbMComp_apply fB
          _ = algebraMap Bf Cb (algebraMap B Bf fB) := rfl
      rw [heq]
      have hfB : IsUnit (algebraMap B Bf fB) := by
        simpa [fB] using IsLocalization.Away.algebraMap_isUnit (algebraMap Q B f)
      exact IsUnit.map (algebraMap Bf Cb) hfB
    have hunitSl : ∀ s : Sl, IsUnit (bToCb s.1) := by
      intro s
      rcases IsLocalization.mem_localizationLocalizationSubmodule.mp s.2 with
        ⟨y, z, hyz⟩
      have hrepr : bToCb s.1 = bMToCb y.1 * bMToCb (algebraMap B Bm z.1) := by
        calc
          bToCb s.1 = bMToCb (algebraMap B Bm s.1) :=
            (hbMComp_apply s.1).symm
          _ = bMToCb (y.1 * algebraMap B Bm z.1) := by rw [hyz]
          _ = bMToCb y.1 * bMToCb (algebraMap B Bm z.1) := map_mul _ _ _
      rw [hrepr]
      rcases y.2 with ⟨n, hn⟩
      have hy : IsUnit (bMToCb y.1) := by
        rw [← hn, map_pow]
        exact IsUnit.pow _ hf
      have hz : IsUnit (bMToCb (algebraMap B Bm z.1)) := by
        rw [hbMComp_apply z.1]
        have hden : algebraMap B Bf z.1 ∈ Nb := ⟨z.1, z.2, rfl⟩
        have hu : IsUnit (algebraMap Bf Cb (algebraMap B Bf z.1)) :=
          IsLocalization.map_units Cb ⟨algebraMap B Bf z.1, hden⟩
        simpa [bToCb] using hu
      exact hy.mul hz
    let toCl : Cb →+* Cl := IsLocalization.lift hunitSb
    let toCb : Cl →+* Cb := IsLocalization.lift hunitSl
    have htoCl : toCl.comp bToCb = bToCl := IsLocalization.lift_comp hunitSb
    have htoCb : toCb.comp bToCl = bToCb := IsLocalization.lift_comp hunitSl
    have hbCb : bToCb = algebraMap B Cb :=
      IsScalarTower.algebraMap_eq B Bf Cb |>.symm
    have hbCl : bToCl = algebraMap B Cl :=
      IsScalarTower.algebraMap_eq B Bm Cl |>.symm
    have hleft : toCb.comp toCl = RingHom.id Cb := by
      apply IsLocalization.ringHom_ext Sb
      calc
        (toCb.comp toCl).comp (algebraMap B Cb) =
            toCb.comp (toCl.comp (algebraMap B Cb)) := RingHom.comp_assoc _ _ _
        _ = toCb.comp (toCl.comp bToCb) := by rw [← hbCb]
        _ = toCb.comp bToCl := by rw [htoCl]
        _ = bToCb := by rw [htoCb]
        _ = (RingHom.id Cb).comp (algebraMap B Cb) := by
          simp [RingHom.id_comp, hbCb]
    have hright : toCl.comp toCb = RingHom.id Cl := by
      apply IsLocalization.ringHom_ext Sl
      calc
        (toCl.comp toCb).comp (algebraMap B Cl) =
            toCl.comp (toCb.comp (algebraMap B Cl)) := RingHom.comp_assoc _ _ _
        _ = toCl.comp (toCb.comp bToCl) := by rw [← hbCl]
        _ = toCl.comp bToCb := by rw [htoCb]
        _ = bToCl := by rw [htoCl]
        _ = (RingHom.id Cl).comp (algebraMap B Cl) := by
          simp [RingHom.id_comp, hbCl]
    let er : Cb ≃+* Cl := RingEquiv.ofRingHom toCl toCb hright hleft
    exact AlgEquiv.ofRingEquiv (f := er) (fun b => by
      change toCl (algebraMap B Cb b) = algebraMap B Cl b
      rw [← hbCb, ← hbCl]
      exact congrArg (fun g : B →+* Cl => g b) htoCl)
  let eBLQ : Cb ≃ₐ[Q] Cl := eBL.restrictScalars Q
  let eQB_B : Cq ≃ₐ[B] Cb := AlgEquiv.ofRingEquiv
    (f := eQB.toRingEquiv) (by
      intro b
      have hlocal (x : Qf) :
          eQB (algebraMap Qf Cq x) = algebraMap Bf Cb (e x) := by
        simpa [eQB] using
          (IsLocalization.algEquivOfAlgEquiv_eq
            (S := Cq) (Q := Cb) (h := e) (H := hmap) x)
      calc
        eQB (bToCq b) =
            eQB (algebraMap Qf Cq (genericPointMap f e b)) := rfl
        _ = algebraMap Bf Cb (e (genericPointMap f e b)) := hlocal _
        _ = algebraMap Bf Cb (algebraMap B Bf b) := by
          change algebraMap Bf Cb
            (e (e.symm (algebraMap B Bf b))) = _
          rw [e.apply_symm_apply]
        _ = bToCb b := rfl)
  exact eQB_B.trans eBL

/-- If the actual local chart `B_M` is formally étale over a parameter ring `R`,
then so is the equivalent generic-open presentation. The denominator may lie
in `M`; it is inverted only after passing to the generic open. -/
theorem formallyEtale_genericOpenRing_of_pointLocal
    {R : Type*} [CommRing R]
    {Q : Type u} [CommRing Q] {B : Type v} [CommRing B] [Algebra Q B]
    [Algebra R B]
    (M : Ideal B) [M.IsPrime] (f : Q)
    (e : Localization.Away f ≃ₐ[Q]
      Localization.Away (algebraMap Q B f))
    [Algebra.FormallyEtale R (Localization.AtPrime M)] :
    letI : Algebra R (genericOpenRing M f e) :=
      ((algebraMap B (genericOpenRing M f e)).comp (algebraMap R B)).toAlgebra
    Algebra.FormallyEtale R (genericOpenRing M f e) := by
  letI : Algebra.FormallyEtale (Localization.AtPrime M)
      (pointLocalAwayOpen M f) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (algebraMap B (Localization.AtPrime M)
        (algebraMap Q B f)))
  letI : Algebra.FormallyEtale R (pointLocalAwayOpen M f) :=
    Algebra.FormallyEtale.comp R (Localization.AtPrime M) (pointLocalAwayOpen M f)
  letI : Algebra R (genericOpenRing M f e) :=
    ((algebraMap B (genericOpenRing M f e)).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B (genericOpenRing M f e) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let eB : genericOpenRing M f e ≃ₐ[B] pointLocalAwayOpen M f :=
    genericOpenEquiv_pointLocalAway_overB M f e
  exact Algebra.FormallyEtale.of_equiv (eB.restrictScalars R).symm

end Stafford38.Geometry.EtaleGenericOpenTransport
end
