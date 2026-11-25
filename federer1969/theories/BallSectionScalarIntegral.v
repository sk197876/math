(** Federer (1969), 3.2.36, p. 273:
    the existing actual ball-section profile
    supplies the finite radial test function. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBallVolume
  EuclideanBallSectionProfileUP EuclideanBallSectionProfile EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ball_section_profile_finite]: supporting
    the radial coefficient evaluation of
    Federer 3.2.36, p. 273, through
    the actual ball-section profile of 2.10.27,
    p. 191. Its independent inside/outside
    laws prove finite values everywhere, including
    zero section degree and its nonzero
    boundary value. No implementation of the
    opaque section-profile witness is inspected. *)
Lemma ball_section_profile_finite (R:realType) m k
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R) (hr:0<=r) y:
  @euclidean_ball_section_profile R m k u r hr y \is a fin_num.
Proof.
have hProfile:=@euclidean_ball_section_profile_specification R m k u r hr.
case:(leP (mdist u y) r)=>hy.
- by rewrite (ball_section_profile_inside hProfile hy) fin_numE.
- by rewrite (ball_section_profile_outside hProfile hy) fin_numE.
Qed.

(** Source for [ball_section_scalar_integral]: supporting
    actual radial integration in Federer
    3.2.36, p. 273. The real
    finite part of the existing ball-section
    profile has the actual ball-volume integral
    already proved in 2.10.27, p. 191.
    Finiteness precedes exact graph transfer;
    all natural source/section dimensions and
    nonnegative radii remain. *)
Theorem ball_section_scalar_integral (R:realType) m k
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R) (hr:0<=r):
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (fun y:inner_metric_space (@euclidean_inner_productP R m)=>
      fine (@euclidean_ball_section_profile R m k u r hr y)))
    (euclidean_unit_ball_volume R (k+m)*r^+(k+m))%R%:E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose q:=@euclidean_ball_section_profile R m k u r hr.
have hIntegral:=@euclidean_ball_section_profile_integral R m k u r hr.
have hGraph (y:X) (z:extended_real_line R):
    partial_function_graph (partial_function_total (fun x:X=>(q x:extended_real_line R))) y z <->
    partial_function_graph (real_total_integrand (fun x:X=>fine (q x))) y z.
  by rewrite real_total_integrand_graph (fineK (@ball_section_profile_finite R m k u r hr y)).
exact:measure_integral_graph_equivalent hGraph hIntegral.
Qed.
