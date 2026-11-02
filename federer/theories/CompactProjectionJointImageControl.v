(** Federer (1969), 3.2.36, p. 272:
    simultaneous projection and source perturbations
    control the Hausdorff distance of actual images. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric CompactSetDistanceProfile CompactHausdorffMetric
  CompactEuclideanProjectionImage CompactProjectionEvaluationControl CompactImageHausdorffControl
  HausdorffLipschitzImage LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_projection_joint_image_control]:
    supporting continuity of (p,S) -> p(S)
    in Federer 3.2.36, p. 272.
    Uniform projection evaluation on a fixed
    compact source and the actual nonexpanding
    Hausdorff image estimate give a neighbourhood
    controlling both variables. Every image is
    specified by its exact image law, and
    its local compact witness is proved to
    exist. Convexity is unnecessary at this
    purely geometric stage. *)
Theorem compact_projection_joint_image_control (R:realType) n m
    (p:euclidean_projection_space R n m)
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))) (e:R):
  0<e ->exists V:set (euclidean_projection_space R n m),open V /\V p /\
    forall q (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
      (P Q:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m))),
      V q ->mdist A B<e/2 ->val P=euclidean_projection_linear p @` val A ->
      val Q=euclidean_projection_linear q @` val B ->mdist P Q<e.
Proof.
move=>he.
have heHalf:0<e/2 by rewrite divr_gt0 // ltr0n.
have [V [hV [hp hControl]]]:=@compact_projection_evaluation_control R n m (val A) p (e/2)
  (set_valP A).1 heHalf.
exists V; split=>//; split=>// q B P Q hq hAB hP hQ.
have [M hM]:=compact_euclidean_projection_image_exists q A.
have hSameSource:mdist P M<=e/2.
  apply:(@compact_image_hausdorff_change_bound R (R_n R n)
    (inner_metric_space (@euclidean_inner_productP R m)) (val A)
    (euclidean_projection_linear p) (euclidean_projection_linear q) P M (e/2)
    (ltW heHalf) hP hM).
  move=>x hx; exact:ltW (hControl q x hq hx).
have hLipschitz:@is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R m)) setT (euclidean_projection_linear q) 1.
  split; first exact:ler01.
  move=>x y _ _; rewrite mul1r; exact:euclidean_projection_nonexpanding.
have hSameMap:=@compact_hausdorff_lipschitz_image_bound R
  (inner_metric_space (@euclidean_inner_productP R n))
  (inner_metric_space (@euclidean_inner_productP R m)) (euclidean_projection_linear q) 1 A B M Q
  hLipschitz hM hQ.
rewrite mul1r in hSameMap.
have hTriangle:=metric_triangle P M Q.
have hStrict:=le_lt_trans hSameMap hAB.
lra.
Qed.
