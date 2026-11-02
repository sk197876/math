(** Federer (1969), 3.2.39, pp. 275--276: the
    degree-zero equality retains every finite collection of atoms. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure HausdorffCountingMeasure
  MinkowskiContents MinkowskiZeroCounting CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [zero_degree_hausdorff_minkowski_equalities]: the
    degree-zero boundary of Federer 3.2.39, pp. 275--276.
    Both contents and actual H^0 agree with counting measure
    on every original set, including finite multipoint sources.
    No invalid single-map R^0 parametrization is used. The
    supporting assertion also retains all infinite sets. *)
Lemma zero_degree_hausdorff_minkowski_equalities (R:realType) n
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  upper_minkowski_content 0 W=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0 W /\
  lower_minkowski_content 0 W=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 0 W.
Proof.
rewrite hausdorff_zero_counting_measure; exact:zero_minkowski_contents_counting.
Qed.
