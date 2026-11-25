(** Federer (1969), 4.1.11, p. 366: affine
    transport of the original signed simplex sums.
    Prove the finite-sum law from the preceding
    compact pushforward linearity, zero image and compact
    finite-sum support, without extending the map to
    currents on which it need not be proper. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentCompactSmoothAlgebra CurrentCompactFiniteSum CurrentCompactCurrentArithmetic
  CurrentCompactPushforwardAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCompactMapFiniteSum.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (U:set (R_n R m)) (V:set (R_n R n)).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y.
Variable f:R_n R m->R_n R n.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U f.
Variable k:nat.
Local Notation C := (@current_space R h2 m U hU k).
Local Notation Compact := (fun T:C=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m U hU k T)).
Local Notation Push := (fun (T:C) (hT:Compact T)=>
  @current_compact_map_pushforward R h2 m n U V hU hV f hImage hf k T hT).

(** Source for [current_compact_map_weighted_sum]: the
    original compact pushforward preserves every finite
    weighted sum, supporting the affine transfer and
    rectangular decomposition in Federer 4.1.11, p. 366.
    Empty sums, zero weights and arbitrary witnesses are retained. *)
Theorem current_compact_map_weighted_sum q (a:'I_q->R) (T:'I_q->C)
    (hT:forall r,Compact (T r)) (hSum:Compact (\sum_r a r*:T r)):
  Push (\sum_r a r*:T r) hSum=\sum_r a r*:Push (T r) (hT r).
Proof.
elim:q a T hT hSum=>[|q ih] a T hT hSum.
- pose hZero:=@current_compact_zero_support R h2 m k U hU.
  have hInput:=@current_compact_map_pushforward_congruence R h2 m n U V hU hV f hImage hf k
    (\sum_r a r*:T r) 0 hSum hZero (ltac:(by rewrite big_ord0)).
  have hOutput:=@current_compact_map_pushforward_zero R h2 m n U V hU hV f hImage hf k
    0 hZero (erefl 0).
  by rewrite hInput hOutput big_ord0.
- pose Tail:=\sum_(r<q) a (lift ord0 r)*:T (lift ord0 r).
  pose hTail:=@current_compact_weighted_finite_sum R h2 m k U hU q
    (fun r=>a (lift ord0 r)) (fun r=>T (lift ord0 r)) (fun r=>hT (lift ord0 r)).
  pose hCombination:=@current_compact_linear_support R h2 m k U hU (a ord0) (T ord0) Tail
    (hT ord0) hTail.
  have hInput:=@current_compact_map_pushforward_congruence R h2 m n U V hU hV f hImage hf k
    (\sum_r a r*:T r) (a ord0*:T ord0+Tail) hSum hCombination (ltac:(by rewrite big_ord_recl)).
  have hLinear:=@current_compact_map_pushforward_linear R h2 m n U V hU hV f hImage hf k
    (a ord0) (T ord0) Tail (hT ord0) hTail hCombination.
  have hTailValue:=ih (fun r=>a (lift ord0 r)) (fun r=>T (lift ord0 r))
    (fun r=>hT (lift ord0 r)) hTail.
  by rewrite hInput hLinear hTailValue big_ord_recl.
Qed.
End CurrentCompactMapFiniteSum.
