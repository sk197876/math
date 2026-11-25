(** Federer (1969), 4.1.7, p. 359:
    the original half-line current has finite
    normal mass. The direct bound uses
    the original scalar pairing integral on
    (0,b], not compactness of its support
    in the half-line. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import NormBoundedLinearTopology Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormOpenTopology InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate FiniteCoordinates FiniteExteriorPowers AlternatingForms AlternatingPairing
  PairingLinear RealFunctionalNormUP CurrentCoefficientNorms CurrentDualNorm EuclideanTopCurrentMass
  CurrentSpaces CurrentMassUP CurrentMassSealed CurrentGlobalComassBound ExtendedSupremumUP
  CurrentNormalMass NormalCurrentsUP CurrentDirac DiracCurrentBounds
  HalflineCurrents HalflineCurrentBoundary EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanDistributionMeasureContext ScalarEuclideanApproximateLimits LebesgueScalarMeasure
  PartialFunctionUP MeasureUP MeasureFiniteClosure MeasureBasic
  TopologicalBorel MeasureIntegralUP MeasureSubsetIntegral SubsetIntegralUpperConstant
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineFiniteNormalMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation U := (@current_halfline_domain R).
Local Notation hU := (@current_halfline_domain_open R).
Local Notation value := (@current_test_value R h2 1 U hU 1%N).
Local Notation action := (@current_value R h2 1 U hU 1%N).
Local Notation M := (fun k=>@CurrentMass.value R h2 1 k U hU).
Local Notation mu := (@euclidean_lebesgue_measure R 1).
Local Notation hm := (euclidean_lebesgue_is_measure R 1).
Local Notation unit := (e_lambda (@coordinate_basis R 1) (ord_tuple 1)).

(** Source for [halfline_current_mass_bound]: the
    original interval current has mass at
    most b, supporting N(T)<infinity in
    Federer 4.1.7, p. 359. *)
Theorem halfline_current_mass_bound b:0<b->(M 1%N (@halfline_current R h2 b)<=b%:E)%E.
Proof.
move=>hb.
pose A:set X:=[set x|0<x ord0<=b].
have hOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx).
have hMeasU:=@euclidean_distribution_measure_borel R 1 U (open_borel_set hOpen).
have hMeasA:measure_measurable mu A.
  have hSet:A=U `&` @current_halfline_upper_set R b.
    apply:funext=>x;apply:propext;split.
    - move/andP=>[h0 hxb];by split.
    - move=>[h0 hxb];by apply/andP;split.
  rewrite hSet.
  exact:(@measure_measurable_intersection R X mu hm U (@current_halfline_upper_set R b)
    hMeasU (@current_halfline_upper_set_measurable R b)).
have hMassA:(mu A<=b%:E)%E.
  have hSegment:(mu [set x:X|0<=x ord0<=b]=b%:E).
    have hScalar:=@lebesgue_scalar_segment R 0 b (ltW hb).
    rewrite (@euclidean_one_project_measure_preimage R `[0,b]) in hScalar.
    rewrite subr0 in hScalar.
    have hSet:((@euclidean_one_project R) @^-1` `[0,b])=[set x:X|0<=x ord0<=b].
      apply:funext=>x;apply:propext;by rewrite /= in_itv /euclidean_one_project.
    by rewrite hSet in hScalar.
  rewrite -hSegment.
  apply:(@measure_mono R X mu hm A [set x:X|0<=x ord0<=b])=>x /andP [h0 hx].
  apply/andP;split;[exact:ltW h0|exact:hx].
apply:(extended_supremum_least (@CurrentMass.laws R h2 1 1%N U hU (@halfline_current R h2 b)))=>a [psi [hPsi <-]].
have hPairBound x (hx:A x):pairing unit (value psi x)<=1.
  have hPair:=real_functional_norm_bound (@current_mass_pairing_norm R h2 1 1%N unit) (value psi x).
  rewrite euclidean_top_current_vector_mass_one mul1r in hPair.
  apply:le_trans (ler_norm _) (le_trans hPair _).
  exact:(@current_global_comass_bound R h2 1 1%N U (value psi) 1).1 hPsi x (andP hx).1.
have hIntegral:=@halfline_current_action R h2 b psi.
have hComparison:forall x j,A x->
    partial_function_graph (real_total_integrand (fun x=>pairing unit (value psi x))) x j->
    (j<=1)%E.
  move=>x j hx hj.
  have ->:j=(pairing unit (value psi x))%:E:=
    esym ((@real_total_integrand_graph R X
      (fun z=>pairing unit (value psi z)) x j).1 hj).
  rewrite lee_fin;exact:(@hPairBound x hx).
have hBound:=@subset_integral_positive_constant_upper_bound R X mu hm A
  (real_total_integrand (fun x=>pairing unit (value psi x))) (action (@halfline_current R h2 b) psi)%:E 1
  hMeasA ltr01 hComparison hIntegral.
rewrite mul1e in hBound;exact:le_trans hBound hMassA.
Qed.

(** Source for [halfline_current_normal_mass_bound]:
    the original example has N(T)<=b+1
    and hence finite N(T), Federer 4.1.7,
    p. 359. This implies local normality;
    it does not assert compact support
    in the open half-line. *)
Theorem halfline_current_normal_mass_bound b:0<b->
  (@current_normal_mass R h2 1 U hU 1%N (@halfline_current R h2 b) < +oo)%E /\
  @is_locally_normal_current R h2 1 U hU 1%N (@halfline_current R h2 b).
Proof.
move=>hb.
have hPoint:U (euclidean_one_embed b) by change (is_true (0<euclidean_one_project (euclidean_one_embed b)));
  rewrite euclidean_one_embedK;exact:hb.
have hDirac:=(@dirac_current_finite_mass R h2 1 U hU (euclidean_one_embed b) hPoint).1.
have hBound:(@current_normal_mass R h2 1 U hU 1%N (@halfline_current R h2 b) < +oo)%E.
  rewrite current_normal_mass_positive_degree halfline_current_boundary.
  apply:lte_add_pinfty.
  - exact:le_lt_trans (halfline_current_mass_bound hb) (ltry b).
  - exact:le_lt_trans hDirac (ltry 1).
split=>//;exact:finite_normal_mass_locally_normal.
Qed.
End HalflineFiniteNormalMass.
