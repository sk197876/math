(** Federer (1969), 4.1.1, pp. 343–345: the finite
    source has bounded linear Euclidean coordinates. This
    supporting adapter reuses the Chapter 1 finite-basis inner
    witness, the existing Euclidean chart and finite linear bounds;
    it keeps the source's given norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerMetric NormMetric NormDifferentialUP
  FiniteBasisInnerWitness FiniteInnerChartUP FiniteInnerChart NormFiniteLinearBound
  RealMetricBackground NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_finite_norm_euclidean_chart]: independent
    linear inverse and boundedness laws for finite normed-source
    coordinates, supporting Federer 4.1.1, pp. 343–345. They
    express the finite-dimensional coordinate change already
    used in the book's earlier normed-space calculus. *)
Record is_finite_norm_euclidean_chart (R:realType) (X:lmodType R)
    (NX:X->R) n (e:Hom (R_n R n) X) (p:Hom X (R_n R n)):Prop:={
  (** Source for [finite_norm_chart_left_inverse]: Euclidean
      coordinates recover their input, supporting the finite
      source reduction in Federer 4.1.1, p. 343. *)
  finite_norm_chart_left_inverse:cancel e p;
  (** Source for [finite_norm_chart_right_inverse]: every source
      point is recovered from coordinates, supporting Federer
      4.1.1, p. 343. *)
  finite_norm_chart_right_inverse:cancel p e;
  (** Source for [finite_norm_chart_forward_bounded]: the forward
      chart is bounded in the original source norm, supporting
      topology transport in Federer 4.1.1, pp. 344–345. *)
  finite_norm_chart_forward_bounded:norm_bounded_linear
    (inner_norm (@euclidean_inner_productP R n)) NX e;
  (** Source for [finite_norm_chart_inverse_bounded]: the inverse
      chart is bounded in the original source norm, supporting
      topology transport in Federer 4.1.1, pp. 344–345. *)
  finite_norm_chart_inverse_bounded:norm_bounded_linear NX
    (inner_norm (@euclidean_inner_productP R n)) p
}.

(** Source for [finite_norm_euclidean_chart_exists]: the
    coordinate chart exists for every finite-dimensional normed
    source, including dimension zero, supporting Federer 4.1.1,
    pp. 343–345. Only earlier proved finite-source results are used. *)
Theorem finite_norm_euclidean_chart_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X):
  is_basis b ->exists (e:Hom (R_n R n) X) (p:Hom X (R_n R n)),
    is_finite_norm_euclidean_chart NX e p.
Proof.
move=>hb.
have [B [hB hOrtho]]:=finite_basis_inner_product_witness hb.
have [e [p hChart]]:=finite_inner_chart_exists hB hb.
exists e,p; constructor.
- exact:finite_inner_chart_left_inverse hChart.
- exact:finite_inner_chart_right_inverse hChart.
- exact:(norm_finite_linear_bounded
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNX (@coordinate_basisP R n) e).
- exact:(norm_finite_linear_bounded hNX
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hb p).
Qed.

(** Source for [finite_norm_chart_forward_continuous]: the
    actual Euclidean-to-source chart is continuous, supporting
    compact supports and open coverings in Federer 4.1.1,
    pp. 344–345. *)
Theorem finite_norm_chart_forward_continuous (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n
    (e:Hom (R_n R n) X) (p:Hom X (R_n R n)):
  is_finite_norm_euclidean_chart NX e p ->
  continuous (fun z:inner_metric_space (@euclidean_inner_productP R n)=>
    (e z:real_norm_metric_space hNX)).
Proof.
move=>h; have [C [hC hb]]:=finite_norm_chart_forward_bounded h.
apply:(@metric_fixed_lipschitz_continuous R _ _ _ C hC)=>x y.
change (is_true (NX (e x-e y)<=C * inner_norm (@euclidean_inner_productP R n) (x-y))).
by rewrite -linearB; exact:hb.
Qed.

(** Source for [finite_norm_chart_inverse_continuous]: the
    source-to-Euclidean chart is continuous, supporting local
    finiteness transport in Federer 4.1.1, pp. 344–345. *)
Theorem finite_norm_chart_inverse_continuous (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n
    (e:Hom (R_n R n) X) (p:Hom X (R_n R n)):
  is_finite_norm_euclidean_chart NX e p ->
  continuous (fun x:real_norm_metric_space hNX=>
    (p x:inner_metric_space (@euclidean_inner_productP R n))).
Proof.
move=>h; have [C [hC hb]]:=finite_norm_chart_inverse_bounded h.
apply:(@metric_fixed_lipschitz_continuous R _ _ _ C hC)=>x y.
change (is_true (inner_norm (@euclidean_inner_productP R n) (p x-p y)<=C * NX (x-y))).
by rewrite -linearB; exact:hb.
Qed.
