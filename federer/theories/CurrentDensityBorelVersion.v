(** Federer (1969), 4.1.7, pp. 357–358:
    measurable multivector fields on U have Borel
    representatives for Radon measures. This supporting
    consequence of 2.3.6, p. 77, uses the
    actual finite multivector norm topology and the
    original compact neighbourhood exhaustion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import FiniteCoordinates RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentCoefficientNorms
  CurrentVectorSpaces CurrentMultivectorDual CurrentWeakNormTopology OpenFamilyTopologyMathcomp
  OpenFamilyTopologyUP NormOpenTopology FiniteNormMetricPolish VectorDaniellHypotheses
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableTotalBasic
  BorelFunctionUP BorelFunctionBasic LusinBorelVersion RadonMeasureUP
  SmoothDomainCompactOpenCover RadonCompactCoverCountablyMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_density_borel_version]: an
    original weakly measurable multivector field has
    an almost equal norm-Borel representative,
    supporting Federer 4.1.7, pp. 357–358,
    by Lusin's corollary 2.3.6, p. 77.
    No bound on the field or on the total
    Radon measure is assumed. *)
Theorem current_density_borel_version (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (mu:set (current_domain R n U)->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (xi:current_domain R n U->exterior_power (R_n R n) m):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1))) ->
  exists z:current_domain R n U->exterior_power (R_n R n) m,
    is_borel_function (fun x=>(z x:real_norm_metric_space (@current_vector_mass_real_norm R h2 n m))) /\
    measure_almost_everywhere mu [set x|xi x=z x].
Proof.
move=>hXi.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose UT:=current_domain R n U.
pose V:=exterior_power X m.
pose VN:=@current_vector_mass R h2 n m.
pose hVN:=@current_vector_mass_real_norm R h2 n m.
pose VW:=open_family_topological_space (@current_multivector_weak_laws R n m).1.
have hIdentity:continuous (fun z:VW=>(z:real_norm_metric_space hVN)).
  rewrite continuousP; exact:(@current_weak_mass_norm_continuous R h2 n m).
have hNormMeas:=@measurable_total_borel_postcomposition R UT VW (real_norm_metric_space hVN)
  mu hm (fun x=>(xi x:VW)) (fun z=>(z:real_norm_metric_space hVN)) hXi
  (continuous_borel_function hIdentity).
have [d [b hb]]:=@current_vector_finite_basis R h2 n m.
have [D [hDCount hDDense]]:=@finite_norm_metric_separable R V VN hVN d b hb.
have [C [W [hC [hW [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R X NX hNX n (@coordinate_basis R n)
    (@coordinate_basisP R n) U hU.
have hCount:=@radon_compact_cover_countably_measurable R UT mu hm hr C hC hCover.
have [z [hZ hAgree]]:=@lusin_borel_version_radon R UT (real_norm_metric_space hVN)
  mu hm hr D (partial_function_total (fun x=>(xi x:real_norm_metric_space hVN))) 0
  hDCount hDDense hNormMeas hCount.
exists z; split; first exact:hZ.
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hAgree)=>x [v [hXiV hZV]].
change (xi x=v) in hXiV; change (z x=v) in hZV.
change (xi x=z x); by rewrite hXiV hZV.
Qed.
