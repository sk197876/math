(** Federer (1969), 3.1.4, pp. 214–216: coordinate reduction
    uses density-zero sets of bad relative increments supplied by
    each scalar approximate differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNorm RealNormUP EuclideanLebesgueDimensions EuclideanApproximateContext
  EuclideanApproximateTranslation CenteredBallRelations PartialFunctionUP
  MeasureSetDensity LocalZeroDensity ApproximateDifferentialUP ApproximateDifferentialRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_differential_increment_density_zero]:
    supporting scalar-to-vector reduction in Federer 3.1.4, p. 214,
    using the relative-remainder definition of 3.1.2, p. 212.
    Translation moves the base point to zero without changing density. *)
Theorem approximate_differential_increment_density_zero (R : realType) m
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (A : set (R_n R m)) (f : R_n R m -> Y) a (L : Hom (R_n R m) Y) e :
  has_approximate_differential NY A f a L -> 0<e ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
    [set h | e*inner_norm (@euclidean_inner_productP R m) h<NY (f (a+h)-f a-L h)])
    (0 : inner_metric_space (@euclidean_inner_productP R m)) 0%E.
Proof.
move=> hf he.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose N := ~` (@approximate_remainder_good_points R m Y NY A f a L e).
have hd := @approximate_remainder_exceptional_density R m Y NY hNY A f a L e hf he.
have hd' : partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R [the metricType R of X]) N) (a+0) 0%E.
  by rewrite addr0.
have ht := @euclidean_zero_density_translation R m a 0 N hd'.
apply: (@local_zero_density_mono R [the metricType R of X]
  (@euclidean_lebesgue_measure R m)
  (@centered_closed_ball_relation R [the metricType R of X]) _
  ((fun h : X=>a+h) @^-1` N) setT 0 (euclidean_approximate_context R m)
  openT Logic.I _ ht)=> h _ hh [hx [hn hgood]].
have hdiff : a+h-a=h by rewrite addrAC subrr add0r.
move: hgood; rewrite hdiff=> hg.
by have := lt_trans hh hg; rewrite ltxx.
Qed.
