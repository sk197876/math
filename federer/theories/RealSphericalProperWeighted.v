(** Federer (1969), 2.10.24, p. 188: real-degree spherical weighted-integral
    equality on boundedly compact metric spaces. Repair the printed
    closed-ball-family justification by the proved comparison H^m<=S^m<=2^m
    H^m of 2.10.2(2), p. 171. Finite spherical weighted limit bounds the
    Hausdorff upper integral, whose positive support has a countable
    finite-Hausdorff-mass cover, hence a finite-spherical-mass cover. Apply
    the already checked sigma-finite spherical equality. The local
    counterexample to the closed-ball-family assertion is in
    ClosedBallHausdorffApproximation.v; the spherical equality itself
    remains valid by this route. The erratum p. 4, book p. 188 line 21,
    corrects script S notation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealHausdorffNormalisation RealHausdorffMeasure RealHausdorffMeasureLaws RealPowerCoverVariants MetricRealPowerCost
  RealHausdorffEnlargement RealSphericalEnlargement ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasureBasic MeasureIntegralBounds HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure
  HausdorffDiameterCost HausdorffSphericalComparison LipschitzFunctionCompact WeightedMetricLimit WeightedMetricLimitLaws
  WeightedUpperIntegralBound WeightedCoverInjectiveTransport UpperIntegralSupportCover RealHausdorffProperWeighted RealSphericalWeightedSigmaFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_weighted_limit_le_spherical]: supporting
    weighted-family comparison in the repair of the
    spherical application of 2.10.24, p. 188.
    Every ball is a nonempty Hausdorff generator,
    and a spherical null set is Hausdorff null;
    finite real coefficients are preserved injectively. *)
Theorem real_hausdorff_weighted_limit_le_spherical (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R) (f : X -> \bar R) :
  weighted_metric_limit (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) (@real_hausdorff_measure R X p hp) f<=
  weighted_metric_limit (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) (@real_spherical_measure R X p hp) f.
Proof.
pose J := @positive_closed_metric_balls R X.
pose K := @nonempty_metric_sets R X.
pose q (j : J) : K := exist _ (val j) (mem_set (positive_metric_closed_ball_nonempty (set_valP j))).
have hq : injective q.
  move=> i j he; apply: val_inj; exact (congr1 (fun k : K=>(val k : set X)) he).
have hnull (N : set X) : (@real_spherical_measure R X p hp) N=0 -> (@real_hausdorff_measure R X p hp) N=0.
  move=> hN; have hh := @real_hausdorff_le_spherical R X p hp N.
  rewrite hN in hh; apply/eqP; by rewrite eq_le hh (measure_nonnegative (@real_hausdorff_measure_is_measure R X p hp)).
exact: (@weighted_limit_injective_transport R X J K (fun j=>val j) (fun j=>val j)
  (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j))
  (@real_spherical_measure R X p hp) (@real_hausdorff_measure R X p hp) q _ _ f
  (@real_hausdorff_measure_is_measure R X p hp) hq (fun j=>@metric_real_diameter_cost_ge0 R X (real_hausdorff_normalisation hp) p (val j) (ltW (real_hausdorff_normalisation_positive hp)))
  hnull (fun j x hx=>hx) (fun _=>lexx _) (fun _=>lexx _)
  (weighted_metric_limit_specification _ _ _) (weighted_metric_limit_specification _ _ _)).
Qed.

(** Source for [real_spherical_weighted_proper_equality]: direct
    real-degree spherical application in 2.10.24, p. 188,
    with the false auxiliary closed-family claim
    replaced by Hausdorff comparison. All boundedly
    compact metric spaces and nonnegative extended-real
    f are covered, including infinite integrals. *)
Theorem real_spherical_weighted_proper_equality (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R)
    (f : X -> extended_real_line R) :
  metric_boundedly_compact X -> (forall x, 0<=f x) ->
  weighted_metric_limit (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) (@real_spherical_measure R X p hp) f=
      measure_upper_integral (@real_spherical_measure R X p hp) (partial_function_total f).
Proof.
move=> hX hf.
pose J := @positive_closed_metric_balls R X.
pose S (j : J) := (val j : set X).
pose c (j : J) := @metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p (val j).
pose psi := @real_spherical_measure R X p hp.
pose L := @weighted_metric_limit R X J S c psi.
have hL := @weighted_metric_limit_specification R X J S c psi.
have hupper := @weighted_metric_limit_upper_integral_bound R X J S c psi L f
  (@real_spherical_measure_specification R X p hp) (fun j=>@metric_real_diameter_cost_ge0 R X (real_hausdorff_normalisation hp) p (val j) (ltW (real_hausdorff_normalisation_positive hp))) hL hf.
apply/eqP; rewrite eq_le hupper /=.
change (is_true (measure_upper_integral psi (partial_function_total f)<=L f)).
have hnon : 0<=L f := @weighted_metric_limit_nonnegative R X J S c psi L hL f.
case hval : (L f)=> [M| |] in hnon *; [|exact: leey|by []].
have hIfinite : measure_upper_integral (@real_hausdorff_measure R X p hp) (partial_function_total f)< +oo.
  have hh := @real_hausdorff_weighted_limit_le_spherical R X p hp f.
  rewrite (@real_hausdorff_weighted_proper_equality R X p hp f hX hf) in hh.
  change (is_true (measure_upper_integral (@real_hausdorff_measure R X p hp) (partial_function_total f)<=L f)) in hh.
  rewrite hval in hh; exact: le_lt_trans hh (ltry _).
have [A [hAfin hsupport]] := @finite_upper_integral_positive_support_cover R X (@real_hausdorff_measure R X p hp) f
  (@real_hausdorff_measure_is_measure R X p hp) hf hIfinite.
have hASfinite n : psi (A n)< +oo.
  apply: le_lt_trans (@real_spherical_le_double_hausdorff R X p hp (A n)) _.
  have hA0 := measure_nonnegative (@real_hausdorff_measure_is_measure R X p hp) (A n).
  have hAnum : (@real_hausdorff_measure R X p hp) (A n) \is a fin_num by rewrite (ge0_fin_numE hA0).
  have he := fineK hAnum.
  rewrite -he -EFinM; exact: ltry.
have heq : L f=measure_upper_integral psi (partial_function_total f) :=
  @real_spherical_weighted_sigma_finite_equality R X p hp f A hf hASfinite hsupport.
by rewrite -heq hval.
Qed.
