(** Federer (1969), 3.2.29, p. 268: supporting the use of
    3.2.3 for the critical image of the global class-one approximant.
    Local derivative bounds and a countable base replace a global
    Lipschitz premise, which is not asserted for the approximant. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormClassOneUP NormClassOneLocalLipschitz LipschitzUP MetricClosedBalls
  EuclideanClosedBallCompact EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanLebesgueHaar
  MeasureUP MeasureBasic CountableBaseLindelof.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_countable_finite_lipschitz_cover]:
    supporting the final null critical-image claim of Federer
    3.2.29, p. 268. The actual global class-one map has a
    countable open cover by sets of finite Lebesgue measure on
    each of which its actual values have a finite Lipschitz bound.
    No new chosen global cover or extension is introduced. *)
Theorem class_one_countable_finite_lipschitz_cover (R:realType) m n
    (f:R_n R m->R_n R n):
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  exists C:set (set (inner_metric_space (@euclidean_inner_productP R m))),
    countable C /\ setT `<=` \bigcup_(U in C) U /\
    forall U,C U -> open U /\ (@euclidean_lebesgue_measure R m U < +oo)%E /\
      exists M,@is_metric_lipschitz_bound R
        (inner_metric_space (@euclidean_inner_productP R m))
        (inner_metric_space (@euclidean_inner_productP R n)) U f M.
Proof.
move=>hf.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose A:set (set X):=[set U|open U /\ (mu U < +oo)%E /\
  exists M,@is_metric_lipschitz_bound R X (inner_metric_space (@euclidean_inner_productP R n)) U f M].
have hCover:setT `<=` \bigcup_(U in A) U.
  move=>a _.
  have [M [d [hM [hd [_ hBound]]]]]:=@norm_class_one_local_lipschitz R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f a I hf.
  pose U:set X:=[set x|mdist a x<d].
  exists U; last by rewrite /U /= mdistxx.
  split; first exact:metric_open_ball_open.
  split.
  - have hSub:U `<=` metric_closed_ball a d by move=>x hx; exact:ltW hx.
    exact (le_lt_trans (measure_mono (euclidean_lebesgue_is_measure R m) hSub)
      (euclidean_compact_finite (@euclidean_closed_metric_ball_compact R m a d))).
  - exists M; split; first exact:ltW hM.
    move=>x y hx hy; rewrite !inner_metric_distanceE.
    apply:hBound.
    + by move:hx; rewrite /U /= (metric_sym a x) inner_metric_distanceE.
    + by move:hy; rewrite /U /= (metric_sym a y) inner_metric_distanceE.
have [B hB]:=euclidean_countable_open_base R m.
have [C [hCA [hC hT]]]:=@countable_base_open_subcover [the topologicalType of X] B setT A hB
  (fun U hU=>hU.1) hCover.
exists C; split; first exact hC.
split; first exact hT.
move=>U hU; exact:hCA U hU.
Qed.
