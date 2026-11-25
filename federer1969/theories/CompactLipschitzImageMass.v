(** Federer (1969), 3.2.23, p. 260: compact Lipschitz image
    pieces have finite source-degree Hausdorff mass. This supporting
    bound is 2.10.11 followed by H^m=L^m in the parameter space,
    2.10.35, p. 197, and compact finiteness of Lebesgue measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  HausdorffMeasure HausdorffLipschitzImages EuclideanHausdorffLebesgue
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_lipschitz_image_finite_hausdorff_mass]:
    supporting finite factor masses for the displayed product integral
    of Federer 3.2.23, p. 260. The compact parameter set may
    be empty; all finite source and target dimensions are retained. *)
Theorem compact_lipschitz_image_finite_hausdorff_mass (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)):
  is_metric_lipschitz setT f ->@compact (inner_metric_space (@euclidean_inner_productP R m)) A ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` A)< +oo.
Proof.
move=>[L [_ hF]] hA.
have hBound:=@hausdorff_lipschitz_image_bound R
  (inner_metric_space (@euclidean_inner_productP R m))
  (inner_metric_space (@euclidean_inner_productP R n)) f L m hF A.
rewrite (euclidean_hausdorff_spherical_lebesgue A).1 in hBound.
have hFinite:@euclidean_lebesgue_measure R m A \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R m) A)).
  exact:euclidean_compact_finite hA.
apply:(le_lt_trans hBound).
rewrite -(fineK hFinite) -EFinM.
exact:ltry.
Qed.
