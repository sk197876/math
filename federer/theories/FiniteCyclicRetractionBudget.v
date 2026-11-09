(** Federer (1969), 3.3.19, p. 304: the
    finite cyclic triangle estimate in the original convex
    boundary argument. It uses only actual metric distances,
    finite sums and a proved cyclic reindexing identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_cyclic_retraction_budget]: the
    middle inequalities of the cyclic boundary sum in
    3.3.19, p. 304. This supporting lemma
    separates the finite metric arithmetic from the
    subsequent actual convex-boundary and radial-retraction
    constructions; none of their conclusions is assumed
    as an original theorem hypothesis. *)
Lemma finite_cyclic_retraction_budget (R:realType) (X:metricType R)
    (I:finType) (sigma:I->I) (c zeta:I->X) (f:X->X) (b:R) (w:I->R):
  injective sigma ->
  (forall i,2* b<=mdist (c i) (c (sigma i))) ->
  (forall i,w i<=b-mdist (f (zeta i)) (c i)) ->
  (forall i,mdist (f (zeta i)) (f (zeta (sigma i)))<=mdist (zeta i) (zeta (sigma i))) ->
  2*(\sum_i w i)<=\sum_i mdist (zeta i) (zeta (sigma i)).
Proof.
move=>hSigma hSeparation hLocal hRetraction.
have hPoint i:w i+w (sigma i)<=mdist (zeta i) (zeta (sigma i)).
  have hFirst:=metric_triangle (c i) (f (zeta i)) (c (sigma i)).
  have hSecond:=metric_triangle (f (zeta i)) (f (zeta (sigma i))) (c (sigma i)).
  rewrite (metric_sym (c i) (f (zeta i))) in hFirst.
  have hSep:=hSeparation i;have hA:=hLocal i;have hB:=hLocal (sigma i).
  have hRetract:=hRetraction i;lra.
have hSum:(\sum_i (w i+w (sigma i)))<=\sum_i mdist (zeta i) (zeta (sigma i)).
  apply:ler_sum=>i _;exact:hPoint.
have hReindex:(\sum_i w i)=\sum_i w (sigma i) by rewrite (reindex_inj hSigma).
rewrite big_split -hReindex in hSum.
have hDouble:2*(\sum_i w i)=(\sum_i w i)+(\sum_i w i) by ring.
by rewrite hDouble.
Qed.
