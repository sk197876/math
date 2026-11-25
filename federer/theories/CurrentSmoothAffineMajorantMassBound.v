(** Federer (1969), 4.1.14, p. 371: apply the preceding
    affine mass estimate to smooth approximations whose two
    differentials have a common pointwise bound. The bound
    is needed only on the original current support. The
    variation and scalar integral remain on the original source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanHomOperator OperatorNormUP OperatorNormSealed CurrentDomain
  CurrentSpaces CurrentMapDifferential CurrentIntegrationCriterion
  CurrentRadonSupport NormalisedCurrentSealed
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  CurrentHomotopyUP CurrentHomotopyCylinder CurrentDeformationChainSealed
  CurrentAffineHomotopyMaximumBound CurrentAffineConstantWeightBound
  CurrentMassSealed PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothAffineMajorantMassBound.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu m : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Variable A : set R.
Variables (U : set X) (V : set Y).
Variables (f g : X -> Y) (h : R_n R (1+n)%N -> Y).
Hypothesis hH : @is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h hH.1).
Variable T : @current_space R h2 n U hU m.
Hypothesis hT : @is_integration_representable_current R h2 n m U hU T.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation a := (fun x:UT => NY (g (set_val x)-f (set_val x))).
Local Notation b := (fun x:UT => Op (@current_map_differential R n nu U f (set_val x))).
Local Notation c := (fun x:UT => Op (@current_map_differential R n nu U g (set_val x))).
Local Notation rho := (fun x:UT => Num.max (b x) (c x)).
Local Notation hm := (distribution_representation_measure
  (normalised_distribution_representation_laws
    (@NormalisedCurrent.laws R h2 n m U hU T hT))).
Hypothesis hAffine : forall t x, A t -> U x ->
  @current_homotopy_slice_map R n nu h t x=(1-t)*:f x+t*:g x.
Hypothesis hProper : @is_current_homotopy_proper R h2 n nu m A U V f g h hH.1 T.
Local Notation chain := (@CurrentDeformationChain.value R h2 n nu m
  A U V f g h hH T hProper).

(** Source for [current_smooth_affine_majorant_mass_bound]:
    replace both endpoint differential norms by their common
    support-wise majorant in the last estimate of 4.1.9,
    p. 364, as used in Federer 4.1.14, p. 371.
    Degree zero, singular variation and infinite integrals remain. *)
Theorem current_smooth_affine_majorant_mass_bound (sigma : X -> R) :
  (forall x, support x ->
    Op (@current_map_differential R n nu U f x)<=sigma x) ->
  (forall x, support x ->
    Op (@current_map_differential R n nu U g x)<=sigma x) ->
  (@CurrentMass.value R h2 nu (1+m)%N V hV chain <=
    measure_lower_integral mu
      (real_total_integrand (fun x:UT => (a x*(sigma (set_val x))^+m)%R)))%E.
Proof.
move=> hF hG.
have hMass := (@current_affine_homotopy_maximum_bound R h2 n nu m
  A U V f g h hH T hT hAffine hProper).2.
apply: (le_trans hMass).
apply: (@measure_lower_integral_monotone R UT mu hm).
apply: (@measure_almost_everywhere_mono R UT mu hm
  [set x | support (set_val x)] _ _
  (@current_radon_outside_support_null R h2 n m U hU T hT)).
move=> x hx.
exists (a x*(rho x)^+m)%:E,(a x*(sigma (set_val x))^+m)%:E.
split; first by apply/real_total_integrand_graph.
split; first by apply/real_total_integrand_graph.
rewrite lee_fin.
have ha : 0<=a x := inner_norm_nonnegative (@euclidean_inner_productP R nu) _.
have hb : 0<=b x := real_seminorm_nonnegative
  (@euclidean_operator_norm_is_norm R n nu).1 _.
have hRho : 0<=rho x by rewrite /rho le_max hb.
have hCap : rho x<=sigma (set_val x).
  rewrite /rho ge_max; apply/andP; split.
  - exact: hF (set_val x) hx.
  - exact: hG (set_val x) hx.
exact: (@nonnegative_affine_weight_cap R (a x) (rho x) (a x)
  (sigma (set_val x)) m ha hRho ha (le_trans hRho hCap) (lexx _) hCap).
Qed.
End CurrentSmoothAffineMajorantMassBound.
