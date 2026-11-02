(** Federer (1969), 3.2.28, printed pp. 263–267: the
    isometric Euclidean identifications preserve the actual
    Hausdorff measures in every degree. This derives metric
    invariance from the covering theorem 2.10.11. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric FiniteInnerChartUP
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_chart_hausdorff_invariance]: the
    Hausdorff-isometric identifications of Federer 3.2.28,
    pp. 263–267, by 2.10.11, p. 176. Arbitrary subsets,
    infinite mass and degree zero are included. *)
Theorem finite_inner_chart_hausdorff_invariance (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)):
  is_finite_inner_chart B e p ->forall mu A,
    @hausdorff_measure R (inner_metric_space hB) mu (e @` A)=
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) mu A.
Proof.
move=>h; apply:(@hausdorff_bijective_isometry_invariance R
  (inner_metric_space (@euclidean_inner_productP R n)) (inner_metric_space hB)
  e p (finite_inner_chart_left_inverse h) (finite_inner_chart_right_inverse h)).
move=>x y; rewrite !inner_metric_distanceE.
change (inner_norm hB (e x-e y)=
  inner_norm (@euclidean_inner_productP R n) (x-y)).
have he:e (x-y)=e x-e y:=linearB (hom_as_linear e) x y.
rewrite -he; exact:(@finite_inner_chart_norm R V B hB n e p h (x-y)).
Qed.
