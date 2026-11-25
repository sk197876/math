(** Federer (1969), 3.2.33, p. 270: local
    chart bounds transport analytic root null sets.
    Expand the class-one local bounds of 3.1.1,
    pp. 210–211, using a countable Euclidean base. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormClassOneUP NormClassOneLocalLipschitz LipschitzUP MetricClosedBalls
  EuclideanLebesgueHaar CountableBaseLindelof.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_domain_countable_lipschitz_cover]:
    the countable local chart reduction supporting the
    analytic alternative in Federer 3.2.33, p. 270.
    A class-one map on its actual open domain has a
    countable cover by open subsets carrying finite
    Lipschitz bounds. No global Lipschitz bound is imposed. *)
Theorem class_one_domain_countable_lipschitz_cover (R:realType) m n
    (A:set (R_n R m)) (f:R_n R m->R_n R n):
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) A f ->
  exists C:set (set (inner_metric_space (@euclidean_inner_productP R m))),
    countable C /\A `<=` \bigcup_(U in C) U /\
    forall U,C U ->open U /\U `<=` A /\
      exists M,@is_metric_lipschitz_bound R
        (inner_metric_space (@euclidean_inner_productP R m))
        (inner_metric_space (@euclidean_inner_productP R n)) U f M.
Proof.
move=>hf.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose F:set (set X):=[set U:set X|open U /\U `<=` A /\exists M,
  @is_metric_lipschitz_bound R X Y U f M].
have hCover:A `<=` \bigcup_(U in F) U.
  move=>a ha.
  have [M [d [hM [hd [hDomain hBound]]]]]:=@norm_class_one_local_lipschitz
    R (R_n R m) (R_n R n) (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A f a ha hf.
  pose U:set X:=[set x|mdist (a:X) x<d].
  have hBall (x:X) (hx:U x):inner_norm (@euclidean_inner_productP R m) (x-a)<d.
    by move:hx; rewrite /U /= (metric_sym (a:X) x) inner_metric_distanceE.
  exists U; last by rewrite /U /= mdistxx.
  split; first exact:metric_open_ball_open.
  split; first by move=>x hx; exact:hDomain x (@hBall x hx).
  exists M; split; first exact:ltW hM.
  move=>x y hx hy; rewrite !inner_metric_distanceE.
  exact:hBound x y (@hBall x hx) (@hBall y hy).
have [B hB]:=euclidean_countable_open_base R m.
have [C [hCF [hC hAC]]]:=@countable_base_open_subcover
  [the topologicalType of X] B A F hB (fun U hU=>hU.1) hCover.
exists C; split; first exact hC.
split; first exact hAC.
move=>U hU; exact:hCF U hU.
Qed.
