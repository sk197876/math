(** Federer (1969), 3.2.47(3), p. 283: the
    exact mass identity on Borel finite rectifiable subsets
    of a class-one sphere submanifold. Actual coarea,
    the computed tangent Jacobian, and the whole-fibre
    isometry discharge every geometric premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates LinearBasis EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric HilbertFormCompactness OrthogonalMaps EuclideanHomInnerCharts
  FiniteInnerChartUP FiniteInnerSubmanifoldUP FiniteInnerTangentPartialJacobian FiniteInnerSubsetCoareaVolumes
  NormDifferentialUP NormDifferentialLinear NormFiniteLinearBound NormOpenDomainLaws
  EuclideanSubmanifoldUP UnitSphereSpace SphericalOrthogonalOrbitDifferential
  SphericalOrthogonalPreimageSubmanifold SphericalPreimageJacobian SphericalOrthogonalFibreIsometry
  SphericalOrthogonalMeasureRectifiablePullback SphericalOrthogonalPreimageBorel
  SphericalOrthogonalProductAlgebra SphericalProductPreimageImage SphericalOrbitCompactness
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialExteriorNormUP
  LipschitzUP LipschitzBasic RectifiableSetUP HausdorffMeasure MeasureUP MeasureBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_submanifold_subset_mass]: the
    coarea calculation in the final paragraph of 3.2.47,
    p. 283, for a finite rectifiable Borel subset
    E of a class-one sphere submanifold M. Original
    E and whole original preimages remain. No supplied
    differential, tangent, Jacobian, or preimage finiteness
    hypothesis is added. *)
Theorem spherical_submanifold_subset_mass (R:realType) n r
    (c:R_n R n.+1) (M E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  @is_euclidean_submanifold R n.+1 r 1%N M ->
  M `<=` @euclidean_unit_sphere_set R n.+1 ->E `<=` M ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n.+1)) E ->
  ((((Num.sqrt (2:R))^-1)^+r)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)=
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E)%E.
Proof.
move=>hc hMan hMSphere hEM hRectE hEB.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hV:=@euclidean_inner_productP R n.+1.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
pose mu:=(n*(n-1)%/2)%N.
pose S:=spherical_orthogonal_preimage c E.
pose P:=spherical_orthogonal_preimage c M.
have hES:E `<=` @euclidean_unit_sphere_set R n.+1.
  move=>a ha; exact:hMSphere a (hEM a ha).
have [N [e [p [hChart hPMan]]]]:=
  @spherical_orthogonal_preimage_submanifold R n r 1%N c M hc (leqnn 1) hMan hMSphere.
pose idV:Hom V V:=hom_of_linear (linear_id V).
have hTarget:is_finite_inner_chart (@euclidean_inner_product R n.+1) idV idV by constructor.
have hRectS:=@spherical_orthogonal_measure_rectifiable_pullback R n c E r hc hES hRectE hEB.
have hSB:=@spherical_orthogonal_preimage_borel R n.+1 c E hEB.
have hSP:S `<=` P.
  move=>g hg; exact (conj hg.1 (hEM _ hg.2)).
have hLip:exists L,@is_metric_lipschitz_bound R (inner_metric_space hH) (inner_metric_space hV)
    S (spherical_orthogonal_orbit c) L.
  have [L [_ hBound]]:=spherical_orthogonal_orbit_lipschitz c.
  exists L; exact (@metric_lipschitz_bound_restrict R (inner_metric_space hH)
    (inner_metric_space hV) setT S (spherical_orthogonal_orbit c) L (fun g _=>I) hBound).
have hDiff g (hg:S g):exists D:Hom (R_n R N) V,
    has_norm_differential (inner_norm (@euclidean_inner_productP R N)) (inner_norm hV) setT
      (fun z=>idV (spherical_orthogonal_orbit c (e z))) (p g) D /\
    is_partial_exterior_norm r (partial_function_source_restrict
      (TangentConeUP.norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` P) (p g))
      (partial_function_total D)) (((Num.sqrt (2:R))^-1)^+r).
  have [T [hT hJac]]:=@spherical_preimage_tangent_jacobian R n r c M g hc hMan hMSphere (hSP g hg).
  have [b hb]:=grassmann_proof T.
  pose L:=spherical_orthogonal_orbit c.
  pose D:=hom_comp idV (hom_comp L e).
  exists D; split.
  - change (has_norm_differential (inner_norm (@euclidean_inner_productP R N)) (inner_norm hV)
      setT D (p g) D).
    apply:(@norm_differential_linear R (R_n R N) V _ _
      (inner_norm_real_norm (@euclidean_inner_productP R N)) (inner_norm_real_norm hV)
      setT (p g) D (norm_full_domain_interior _ _)).
    exact (@norm_finite_linear_bounded R (R_n R N) V _ _
      (inner_norm_real_norm (@euclidean_inner_productP R N)) (inner_norm_real_norm hV)
      N (@coordinate_basis R N) (@coordinate_basisP R N) D).
  - exact (@finite_inner_tangent_partial_jacobian_chart R H V _ _ hH hV N n.+1
      e p idV P g (grassmann_val T) (r+mu)%N b hb L r _ hChart
      (fun x y=>erefl _) hT hJac).
have hFibre y (hy:E y):@hausdorff_measure R (inner_metric_space hH) (r+mu-r)%N
    [set g|S g /\spherical_orthogonal_orbit c g=y]=
    @hausdorff_measure R (inner_metric_space hH) mu (spherical_orthogonal_isotropy c).
  rewrite addKn.
  have hSet:[set g|S g /\spherical_orthogonal_orbit c g=y]=
      [set g|is_orthogonal_map (@euclidean_inner_product R n.+1)
        (@euclidean_inner_product R n.+1) (hom_as_linear g) /\g c=y].
    apply/seteqP; split=>g.
    - by move=>[[hg _] hValue]; split.
    - move=>[hg hValue]; split; last exact hValue.
      split; first exact hg; change (E (g c)); by rewrite hValue.
  rewrite hSet; exact (@spherical_orthogonal_fibre_measure R n c y hc (hES y hy) mu).
apply:(@finite_inner_subset_coarea_volumes R H V _ _ hH hV N n.+1 (r+mu)%N r
  e p idV idV P S E (spherical_orthogonal_orbit c) (((Num.sqrt (2:R))^-1)^+r)
  (@hausdorff_measure R (inner_metric_space hH) mu (spherical_orthogonal_isotropy c))
  hChart hTarget hPMan hSP hRectS hSB hRectE hEB).
- exact:leq_addr.
- apply:exprn_ge0; by rewrite invr_ge0 sqrtr_ge0.
- exact (@measure_nonnegative R (inner_metric_space hH)
    (@hausdorff_measure R (inner_metric_space hH) mu)
    (@hausdorff_measure_is_measure R (inner_metric_space hH) mu) (spherical_orthogonal_isotropy c)).
- exact hLip.
- by move=>g hg; exact hg.2.
- exact hDiff.
- exact hFibre.
Qed.
