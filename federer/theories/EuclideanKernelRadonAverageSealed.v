(** Federer (1969), 4.1.18, p. 375: the
    original average of translated Radon measures,
    with only its independent compact-test integral
    law and Radon properties exposed. The product
    and density construction remain hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain MeasureUP RadonMeasureUP EuclideanKernelRadonAverageUP
  EuclideanKernelRadonAverageExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type EuclideanKernelRadonAverageSignature.
(** Source for [value]: the original compactly
    weighted translated Radon average of 4.1.18,
    p. 375, on the actual ambient R^n. *)
Parameter value:forall (R:realType) n
    (beta:set (current_domain R n (fun _=>True))->\bar R)
    (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta)
    (w:R_n R n->R^o),
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) (fun _=>True) w ->
  (forall z,0<=w z)->forall r:R,
  (forall z,r<inner_norm (@euclidean_inner_productP R n) z->w z= 0)->
  set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))->\bar R.
(** Source for [laws]: the actual original positive
    compact-test translation integral, Radon and measure
    laws of the average in 4.1.18, p. 375. *)
Parameter laws:forall (R:realType) n
    (beta:set (current_domain R n (fun _=>True))->\bar R)
    (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta)
    (w:R_n R n->R^o)
    (hW:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
      (fun t:R^o=>`|t|) (fun _=>True) w)
    (hPositive:forall z,0<=w z) (r:R)
    (hOff:forall z,r<inner_norm (@euclidean_inner_productP R n) z->w z= 0),
  @is_euclidean_kernel_radon_average R n beta hBeta hBetaRadon w
    (@value R n beta hBeta hBetaRadon w hW hPositive r hOff).
End EuclideanKernelRadonAverageSignature.
Module EuclideanKernelRadonAverage:EuclideanKernelRadonAverageSignature.
(** Source for [value]: choose only the separately
    proved original measure witness, supporting
    Federer 4.1.18, p. 375. *)
Definition value (R:realType) n
    (beta:set (current_domain R n (fun _=>True))->\bar R)
    (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta)
    (w:R_n R n->R^o)
    (hW:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
      (fun t:R^o=>`|t|) (fun _=>True) w)
    (hPositive:forall z,0<=w z) (r:R)
    (hOff:forall z,r<inner_norm (@euclidean_inner_productP R n) z->w z= 0):=
  projT1 (cid (@euclidean_kernel_radon_average_exists R n beta hBeta hBetaRadon
    w hW hPositive r hOff)).
(** Source for [laws]: the opaque original average
    satisfies its independently specified compact-test
    formula, Federer 4.1.18, p. 375. *)
Lemma laws (R:realType) n
    (beta:set (current_domain R n (fun _=>True))->\bar R)
    (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta)
    (w:R_n R n->R^o)
    (hW:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
      (fun t:R^o=>`|t|) (fun _=>True) w)
    (hPositive:forall z,0<=w z) (r:R)
    (hOff:forall z,r<inner_norm (@euclidean_inner_productP R n) z->w z= 0):
  @is_euclidean_kernel_radon_average R n beta hBeta hBetaRadon w
    (@value R n beta hBeta hBetaRadon w hW hPositive r hOff).
Proof.
exact:(projT2 (cid (@euclidean_kernel_radon_average_exists R n beta hBeta hBetaRadon
  w hW hPositive r hOff))).
Qed.
End EuclideanKernelRadonAverage.
Arguments EuclideanKernelRadonAverage.value : clear implicits.
Arguments EuclideanKernelRadonAverage.laws : clear implicits.
