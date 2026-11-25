(** Federer (1969), 4.1.23, p. 380:
    the actual cone over a compact zero-current
    has the printed boundary and its mass is
    bounded by the support distance times the
    original current mass. Reuse the preceding
    point-join boundary and original orientation-weight
    mass estimate, including the scalar degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading ExteriorPowers
  ExteriorHomogeneousProducts CurrentCoefficientNorms CurrentDomain
  CurrentSpaces CurrentBoundary CurrentIntegrationCriterion CurrentMassSealed
  CurrentCompactSmoothValue CurrentDirac CurrentDiracSmooth
  CurrentCompactElementaryPushforwards CurrentJoinSealed
  CurrentJoinBoundaryDegree CurrentJoinBoundaryBothZero CurrentJoinConeMass
  CurrentDegreeTransportIdentity CurrentOrientationSealed
  CurrentOrientationAlmost CurrentExteriorProductMass
  CurrentExteriorOperatorMassBound CurrentAffineConstantWeightBound
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci SummableRealFunctionUP MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds.
From Federer Require Import MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ZeroCurrentPointCone.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation XT := (current_domain R n Full).
Variable b : X.
Variable T : @current_space R h2 n Full hFull 0%N.
Hypothesis hCompact : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull 0%N T).
Local Notation D := (@dirac_current R h2 n Full hFull b).
Local Notation hD := (@current_compact_dirac_support R h2 n Full hFull b Logic.I).
Local Notation Cone := (@CurrentJoin.value R h2 n 0%N 0%N D T hD hCompact).

(** Source for [zero_current_point_cone_boundary]:
    boundary([b] join T)=T-T(1)[b],
    the actual cone filling used for
    each transverse cell in Federer
    4.1.23, p. 380. Compactness suffices;
    no representation or normality is required
    for this algebraic identity. *)
Theorem zero_current_point_cone_boundary :
  @current_boundary R h2 n 0%N Full hFull Cone=
    T-(@current_compact_total R h2 n Full hFull T hCompact)*:D.
Proof.
have hBoundary := @current_join_boundary_both_zero R h2 n D T hD hCompact.
rewrite /current_join_boundary /current_join_successor
  current_degree_transport_identity in hBoundary.
have hTotal := @dirac_current_total R h2 n Full hFull b Logic.I hD.
by rewrite hTotal scale1r in hBoundary.
Qed.

(** Source for [zero_current_point_cone_mass_bound]:
    M([b] join T)<=d M(T), the
    individual-cell cone mass estimate in
    Federer 4.1.23, p. 380. The
    cap is imposed only on the
    actual support and the measure is
    the original normalized variation of T. *)
Theorem zero_current_point_cone_mass_bound
    (hT : @is_integration_representable_current R h2 n 0%N Full hFull T)
    (mass d : R)
    (hMass : @CurrentMass.value R h2 n 0%N Full hFull T=mass%:E)
    (hDistance : forall x, @current_support R h2 n Full hFull 0%N T x ->
      NX (x-b)<=d) :
  (@CurrentMass.value R h2 n 1%N Full hFull Cone<=(d*mass)%:E)%E.
Proof.
pose mu := @NormalisedCurrent.measure R h2 n 0%N Full hFull T hT.
pose hm := distribution_representation_measure
  (normalised_distribution_representation_laws
    (@NormalisedCurrent.laws R h2 n 0%N Full hFull T hT)).
pose w := fun x : XT => NX (set_val x-b).
pose weight := @current_join_cone_weight R h2 n 0%N b T hT.
have hAlmost : measure_almost_everywhere mu
    (partial_extended_le_locus weight (real_total_integrand w)).
  apply: (@measure_almost_everywhere_mono R XT mu hm _ _ _
    (@current_orientation_unit_mass R h2 n 0%N Full hFull T hT)).
  move=> x [eta [hEta hUnit]].
  pose a := @current_vector_mass R h2 n 1%N
    (exterior_product (exterior_first_inclusion X (set_val x-b)) eta).
  have hGraph : partial_function_graph weight x a%:E.
    apply/(@current_join_cone_weight_graph R h2 n 0%N b T hT x a%:E).
    by exists eta; split.
  have hCap : a<=w x.
    have hWedge := @current_exterior_product_mass_bound R h2 n 1%N 0%N
      (exterior_first_inclusion X (set_val x-b)) eta.
    by rewrite hUnit mulr1 current_first_vector_mass in hWedge.
  exists a%:E,(w x)%:E; split; first exact: hGraph.
  split; first by apply/real_total_integrand_graph.
  by rewrite lee_fin.
have hIntegral := @measure_lower_integral_monotone R XT mu hm
  weight (real_total_integrand w) hAlmost.
have hBound := @current_original_variation_bounded_integral R h2 n 0%N
  Full hFull T hT mass d w hMass
  (fun x hx => @hDistance (set_val x) hx).
have hCone := @current_join_point_cone_mass_bound R h2 n 0%N b T hT hCompact.
rewrite invr1 mul1e in hCone.
exact: le_trans hCone (le_trans hIntegral hBound).
Qed.
End ZeroCurrentPointCone.
