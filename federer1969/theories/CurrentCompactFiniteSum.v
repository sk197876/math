(** Federer (1969), 4.1.11, pp. 365–366: the
    finite sums of compact face and prism currents have
    compact support. Reuse the original compact linear
    combination law; no support set is reconstructed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCompactSmoothAlgebra
  CurrentCompactCurrentArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCompactFiniteSum.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C := (@current_space R h2 n U hU j).
Local Notation Compact := (fun T:C=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n U hU j T)).

(** Source for [current_compact_finite_sum]: every finite
    sum of original compact currents is compact, supporting
    the face and prism sums in Federer 4.1.11,
    pp. 365–366. The empty sum is included. *)
Theorem current_compact_finite_sum q (T:'I_q->C):
  (forall k,Compact (T k))->Compact (\sum_k T k).
Proof.
elim:q T=>[|q ih] T hT;first by rewrite big_ord0;exact:current_compact_zero_support.
rewrite big_ord_recl.
have hTail:=ih (fun k=>T (lift ord0 k)) (fun k=>hT (lift ord0 k)).
have h:=@current_compact_linear_support R h2 n j U hU 1 (T ord0)
  (\sum_(k<q) T (lift ord0 k)) (hT ord0) hTail.
by rewrite scale1r in h.
Qed.

(** Source for [current_compact_weighted_finite_sum]: the
    original finite signed face sums are compact, supporting
    Federer 4.1.11, pp. 365–366. Arbitrary real weights,
    including zero, are allowed. *)
Theorem current_compact_weighted_finite_sum q (a:'I_q->R) (T:'I_q->C):
  (forall k,Compact (T k))->Compact (\sum_k a k*:T k).
Proof.
move=>hT;apply:current_compact_finite_sum=>k.
exact:(@current_compact_scaled_support R h2 n j U hU (T k) (a k) (hT k)).
Qed.
End CurrentCompactFiniteSum.
