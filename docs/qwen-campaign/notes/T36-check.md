# T36 candidate notes

The assigned target is frozen from PLAN.md, section 9, character for
character:

```lean
theorem axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (w : GeneralDivisorialVisibleFrameWitness hm P)
    (hpoint : actualSameWitnessGroundPointOutput hm P w)
    (hsmoothOpen : ∃ fbar : MvPolynomial (Fin m) k ⧸ P.asIdeal,
      fbar ≠ 0 ∧ Algebra.Smooth k (Localization.Away fbar)) :
    (fun i : Fin m => if i = (⟨0, hm⟩ : Fin m) then (1 : k) else 0) ∈
      MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (Stafford38.Geometry.ProjectiveConormalDirections.smoothConormalFibreProjection
            P.asIdeal))
```

The unconditional consumer is prepared at
`tests/SameWitness/AffineFibreClosureConsumer.lean`. Its statement has no
`hpoint` or `hsmoothOpen`; its proof supplies both via the prescribed
same-witness ground-point completion and generic smooth principal open.

The candidate is staged in
`Stafford38/Geometry/SameWitness/AffineFibreClosure.lean`. It assembles the
planned T30–T35 packages and applies the T22 ring-hom endpoint. T34 has
approved a positions/columns split; the candidate now consumes both
`CommonOpenPositionData` and `CommonOpenColumnsData`. The source interfaces
are still being finalized and no Lean command has been run; the controller
owns the guarded queue. The current source statement diff against
`.lake/qwen/T36-statement.lean` is empty. The required `letI`/`haveI` and
`compHom` scans on the candidate source are also empty, and `git diff
--check` passes for the two owned Lean files. Recheck the statement and source
after the upstream declarations land and make any API corrections before
requesting the T36 check.

Expected T22 inputs, in endpoint order after its map and Laurent-series
prelude: `qC`, `qPre`, `rows`, `chart`, `axis`, `a`, `b`, `beta`, `alpha`,
`u₀`, `u₁`, `hchartPre`, `hdata`, `hposition`, `htransverse`, `hraw`,
`hchart`, `p`, `fbar`, `hrep`, `hsmooth`, `hnumerator`. T22 owns that exact
signature; this note does not replace its source declaration.

No new structure or definition is planned for T36, so no definition-owner
entry is required. Existing same-witness helpers and step structures remain
the source of every argument.
