(** Federer (1969), 3.2.47(3), p. 283: on
    any original subset of O(n), the actual r-Jacobian
    of evaluation is bounded by 2^(-r/2). The
    approximate tangent lies in the actual group tangent;
    the pointwise horizontal bound and exterior estimate prove it. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates LinearBasis HomCompositionDeterminant
  EuclideanInnerProduct InnerProductUP InnerProductRestriction InnerRestrictedNorm InnerNorm InnerMetric
  HilbertFormCompactness OrthogonalMaps EuclideanHomInnerCharts EuclideanStiefelSmooth
  FiniteInnerSmoothSubmanifoldUP FiniteInnerTangentPlane FiniteInnerChartUP FiniteInnerTangentPartialJacobian
  EuclideanLinearMaps NormDifferentialUP NormDifferentialLinear NormFiniteLinearBound NormOpenDomainLaws
  TangentConeUP SphericalOrthogonalTangents SphericalOrthogonalOrbitDifferential
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialExteriorNormUP
  MeasureRestriction MeasureApproximateJacobian RestrictedApproximateJacobianTangentBound
  ExteriorMaps ExteriorOperatorNorm ExteriorPowerLinearBound OperatorNormUP InnerExteriorPositivity
  HausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_group_subset_jacobian_bound]: the
    bound needed for the original arbitrary-set version of
    3.2.47(3), p. 283. It holds wherever
    the actual approximate Jacobian is defined, without a
    source measurability, finite-mass, tangent-plane or supplied
    derivative premise. All density and exterior degrees remain. *)
Theorem spherical_group_subset_jacobian_bound (R:realType) n d m q
    (e:Hom (R_n R d) (Hom (R_n R n.+1) (R_n R n.+1)))
    (p:Hom (Hom (R_n R n.+1) (R_n R n.+1)) (R_n R d))
    (c:R_n R n.+1) (W:set (R_n R d)) z J:
  is_finite_inner_chart (@euclidean_hom_inner_product R n.+1 n.+1) e p ->
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  W `<=` p @` [set g|is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear g)] ->W z ->
  partial_function_graph (measure_approximate_jacobian (measure_restrict
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R d)) m) W) m q
    (partial_function_source_restrict W (partial_function_total (fun x=>e x c)))) z J ->
  J<=(((Num.sqrt (2:R))^-1)^+q).
Proof.
move=>hChart hc hWO hz hJ.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hV:=@euclidean_inner_productP R n.+1.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
pose O:set H:=[set g|is_orthogonal_map (@euclidean_inner_product R n.+1)
  (@euclidean_inner_product R n.+1) (hom_as_linear g)].
have [g hg hpg]:=hWO z hz.
move:hJ; rewrite -hpg=>hJ.
pose nu:=(n.+1*(2*n.+1-n.+1-1)%/2)%N.
have hOMan:=inner_smooth_submanifold_class (@euclidean_stiefel_smooth_submanifold R n.+1 n.+1) 1%N.
have [T hTan]:=@finite_inner_submanifold_tangent_plane R H _ hH _
  (@hom_rank_one_base R V V n.+1 n.+1 (@coordinate_basis R n.+1)
    (@coordinate_basisP R n.+1) (@coordinate_basis R n.+1))
  (@hom_rank_one_baseP R V V n.+1 n.+1 (@coordinate_basis R n.+1)
    (@coordinate_basisP R n.+1) (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1))
  nu 1%N O g (leqnn 1) hOMan hg.
pose hT:=restricted_inner_productP hH (grassmann_val T).
have [b hb]:=grassmann_proof T.
pose L:=hom_comp (spherical_orthogonal_orbit c)
  (hom_of_linear (subspace_inclusion (grassmann_val T))).
pose s:=(Num.sqrt (2:R))^-1.
have hs:0<=s by rewrite /s invr_ge0 sqrtr_ge0.
have hBound u:inner_norm hV (L u)<=s*inner_norm hT u.
  rewrite restricted_inner_normE.
  apply:(@spherical_actual_tangent_evaluation_bound R n.+1 g (subspace_val u) c hg hc).
  by rewrite hTan; exact:subspace_valP.
pose j0:=exterior_operator_norm (euclidean_two_nonzero R) hT hV hb (hom_as_linear L) q.
have hNorm:is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hT q)
    (exterior_inner_productP (euclidean_two_nonzero R) hV q)
    (exterior_power_map (hom_as_linear L) q) j0.
  exact:exterior_operator_normP.
have hUpper:j0<=s^+q.
  exact (@exterior_power_linear_bound R (euclidean_two_nonzero R) (subspace_space (grassmann_val T)) V
    _ _ hT hV nu b hb (hom_as_linear L) s q hs hBound).
pose idV:Hom V V:=hom_of_linear (linear_id V).
pose D:=hom_comp idV (hom_comp (spherical_orthogonal_orbit c) e).
have hPartial:is_partial_exterior_norm q (partial_function_source_restrict
    (norm_tangent_cone (inner_norm (@euclidean_inner_productP R d)) (p @` O) (p g))
    (partial_function_total D)) j0.
  exact (@finite_inner_tangent_partial_jacobian_chart R H V _ _ hH hV d n.+1 e p idV O g
    (grassmann_val T) nu b hb (spherical_orthogonal_orbit c) q j0 hChart (fun x y=>erefl _) hTan hNorm).
have hD:has_norm_differential (inner_norm (@euclidean_inner_productP R d)) (inner_norm hV)
    setT (fun x=>e x c) (p g) D.
  change (has_norm_differential (inner_norm (@euclidean_inner_productP R d)) (inner_norm hV) setT D (p g) D).
  apply:(@norm_differential_linear R (R_n R d) V _ _
    (inner_norm_real_norm (@euclidean_inner_productP R d)) (inner_norm_real_norm hV)
    setT (p g) D (norm_full_domain_interior _ _)).
  exact (@norm_finite_linear_bounded R (R_n R d) V _ _
    (inner_norm_real_norm (@euclidean_inner_productP R d)) (inner_norm_real_norm hV)
    d (@coordinate_basis R d) (@coordinate_basisP R d) D).
have hLower:J<=j0.
  exact (@restricted_approximate_jacobian_tangent_bound R d n.+1 m q
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R d)) m) W (p @` O)
    (fun x=>e x c) (p g) D J j0
    (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R d)) m)
    hWO hD (partial_exterior_norm_nonnegative hPartial) (partial_exterior_norm_bound hPartial) hJ).
exact (le_trans hLower hUpper).
Qed.
