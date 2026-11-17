(** Federer 2.10.27, p. 191: the exact real-degree profile
    integral for positive degree and radius. The unit-ball identity
    and existing Lebesgue affine transport supply its full centre
    and radius dependence. Zero endpoints are treated separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealPower RealPowerSuccessor RealPowerNaturalHausdorff RealHausdorffBallCoefficient
  RealEuclideanBallSectionProfileUP RealEuclideanBallSectionProfileSealed
  RealUnitBallSectionProfileIntegral RealBallSectionProfileFinite RealBallSectionRadiusRescaling
  EuclideanPositiveAffineIntegral MeasureIntegralUP MeasureIntegralGraphEquivalence
  PartialFunctionUP PartialFunctionBasic SummableRealFunctionUP SummableRealArithmetic
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Close Scope ereal_scope.

(** Source for [real_ball_section_profile_positive_integral]: the
    first display of Federer 2.10.27, p. 191, for positive real
    section degree and positive radius, with arbitrary original
    centre and natural base dimension, including dimension zero. *)
Theorem real_ball_section_profile_positive_integral (R:realType) m (k:R) (hk:0<=k)
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R) q:
  0<k ->0<r ->is_real_euclidean_ball_section_profile hk u r q ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(q y:extended_real_line R)))
    (real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m))*real_power r (k+m%:R))%:E.
Proof.
move=> hkPos hr hq.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose p:=@RealEuclideanBallSectionProfile.value R m k hk 0 1.
have hp:=@RealEuclideanBallSectionProfile.laws R m k hk 0 1.
pose f (y:X):R:=fine (p y).
pose a:=real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)).
have hUnit:=@real_unit_ball_section_profile_integral R m k hk p hkPos hp.
have hFine:is_measure_integral mu (real_total_integrand f) a%:E.
  apply:(measure_integral_graph_equivalent _ hUnit)=>y z.
  by rewrite real_total_integrand_graph /f (fineK (@real_ball_section_profile_finite R m k hk 0 1 p hp y)).
have hAffine:=@euclidean_positive_affine_integral R m u r f a hr hFine.
have hScaled:=@real_total_integral_scale R X mu hm
  (fun y=>f (r^-1*:(y-u))) (r^+m*a) (real_power r k) hAffine.
have hValue:real_power r k*(r^+m*a)=a*real_power r (k+m%:R).
  rewrite real_power_add_exponents_positive //
    (@real_power_natural_exponent R r m (ltW hr));ring.
rewrite hValue in hScaled.
apply:(measure_integral_graph_equivalent _ hScaled)=>y z.
have hEq:=@real_ball_section_profile_rescaling R m k hk u r p q hr hp hq y.
rewrite real_total_integrand_graph /f EFinM
  (fineK (@real_ball_section_profile_finite R m k hk 0 1 p hp (r^-1*:(y-u)))).
by rewrite -hEq.
Qed.
