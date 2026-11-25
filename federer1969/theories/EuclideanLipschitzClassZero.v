(** Federer (1969), 3.2.3, p. 243: a
    Lipschitzian Euclidean map is continuous on its whole
    source. This adapter states the intrinsic class-zero
    laws used for the Borel differential and rank loci. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormMetricScaleContinuity NormClassOneUP NormClassZeroWhole LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_lipschitz_norm_class_zero]: the
    continuity premise used with 3.2.2 in Federer 3.2.3,
    p. 243, proved from the Lipschitz bound and the
    unchanged given Euclidean norms. *)
Lemma euclidean_lipschitz_norm_class_zero (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f -> norm_class_zero
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n)) setT f.
Proof.
move=>[M [hM hb]].
apply:(@norm_continuous_whole_class_zero R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) f).
apply:(@metric_fixed_lipschitz_continuous R _ _ _ M hb.1)=>x y.
exact (hb.2 x y Logic.I Logic.I).
Qed.
