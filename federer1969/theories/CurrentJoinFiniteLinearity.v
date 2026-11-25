(** Federer (1969), 4.1.11, pp. 365–366: expand
    the original point join over the finite signed face
    sums. Derive zero, scaling, addition and finite sums
    from the proved original join linearity and compact
    support laws. No new current space is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCompactSmoothAlgebra CurrentCompactCurrentArithmetic CurrentCompactFiniteSum
  CurrentJoinSealed CurrentJoinLinearity CurrentJoinCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinFiniteLinearity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation C := (fun k=>@current_space R h2 n Full hFull k).
Local Notation Compact := (fun k (T:C k)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull k T)).
Variable S:C i.
Hypothesis hS:Compact i S.
Local Notation J := (fun (T:C j) (hT:Compact j T)=>@CurrentJoin.value R h2 n i j S T hS hT).

(** Source for [current_join_second_zero]: S join 0=0,
    supporting the original finite-sum identities in
    Federer 4.1.11, pp. 365–366. Every compactness
    proof of the zero current is permitted. *)
Theorem current_join_second_zero (hZero:Compact j (0:C j)):J 0 hZero=0.
Proof.
have hCombination:Compact j ((-1:R)*:(0:C j)+0) by rewrite scaler0 add0r.
have hLinear:=@current_join_second_linear R h2 n i j (-1:R) S 0 0 hS hZero hZero hCombination.
have hInput:=@current_join_current_congruence R h2 n i j S S ((-1:R)*:(0:C j)+0) 0
  hS hS hCombination hZero (erefl S) (ltac:(by rewrite scaler0 add0r)).
by rewrite hInput scaleN1r addNr in hLinear.
Qed.

(** Source for [current_join_second_scale]: the original
    point join respects every scalar on the second factor,
    supporting Federer 4.1.11, pp. 365–366. *)
Theorem current_join_second_scale c (T:C j) (hT:Compact j T) (hScaled:Compact j (c*:T)):
  J (c*:T) hScaled=c*:J T hT.
Proof.
pose hZero:=@current_compact_zero_support R h2 n j Full hFull.
pose hCombination:=@current_compact_linear_support R h2 n j Full hFull c T 0 hT hZero.
have hLinear:=@current_join_second_linear R h2 n i j c S T 0 hS hT hZero hCombination.
have hInput:=@current_join_current_congruence R h2 n i j S S (c*:T+0) (c*:T)
  hS hS hCombination hScaled (erefl S) (addr0 (c*:T)).
by rewrite hInput (current_join_second_zero hZero) addr0 in hLinear.
Qed.

(** Source for [current_join_second_add]: the original
    point join preserves addition on compact second factors,
    supporting the face sum in Federer 4.1.11,
    p. 365. Every compactness witness is allowed. *)
Theorem current_join_second_add (T U:C j) (hT:Compact j T) (hU:Compact j U)
    (hSum:Compact j (T+U)):J (T+U) hSum=J T hT+J U hU.
Proof.
pose hCombination:=@current_compact_linear_support R h2 n j Full hFull 1 T U hT hU.
have hLinear:=@current_join_second_linear R h2 n i j 1 S T U hS hT hU hCombination.
have hInput:=@current_join_current_congruence R h2 n i j S S (1*:T+U) (T+U)
  hS hS hCombination hSum (erefl S) (ltac:(by rewrite scale1r)).
by rewrite hInput scale1r in hLinear.
Qed.

(** Source for [current_join_second_weighted_sum]: the
    original point join distributes over every finite
    signed face sum, supporting the alternating boundary
    formula in Federer 4.1.11, p. 365. The empty sum
    and zero weights are retained. *)
Theorem current_join_second_weighted_sum q (a:'I_q->R) (T:'I_q->C j)
    (hT:forall k,Compact j (T k))
    (hSum:Compact j (\sum_k a k*:T k)):
  J (\sum_k a k*:T k) hSum=\sum_k a k*:J (T k) (hT k).
Proof.
elim:q a T hT hSum=>[|q ih] a T hT hSum.
- pose hZero:=@current_compact_zero_support R h2 n j Full hFull.
  have hInput:=@current_join_current_congruence R h2 n i j S S (\sum_k a k*:T k) 0
    hS hS hSum hZero (erefl S) (ltac:(by rewrite big_ord0)).
  by rewrite hInput current_join_second_zero big_ord0.
- pose Tail:=\sum_(k<q) a (lift ord0 k)*:T (lift ord0 k).
  pose hTail:=@current_compact_weighted_finite_sum R h2 n j Full hFull q
    (fun k=>a (lift ord0 k)) (fun k=>T (lift ord0 k)) (fun k=>hT (lift ord0 k)).
  pose hCombination:=@current_compact_linear_support R h2 n j Full hFull (a ord0) (T ord0) Tail
    (hT ord0) hTail.
  have hInput:=@current_join_current_congruence R h2 n i j S S (\sum_k a k*:T k)
    (a ord0*:T ord0+Tail) hS hS hSum hCombination (erefl S) (ltac:(by rewrite big_ord_recl)).
  have hLinear:=@current_join_second_linear R h2 n i j (a ord0) S (T ord0) Tail
    hS (hT ord0) hTail hCombination.
  have hTailValue:=ih (fun k=>a (lift ord0 k)) (fun k=>T (lift ord0 k))
    (fun k=>hT (lift ord0 k)) hTail.
  by rewrite hInput hLinear hTailValue big_ord_recl.
Qed.
End CurrentJoinFiniteLinearity.
