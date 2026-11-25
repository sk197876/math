(** Federer (1969), 4.1.4, p. 348: the original inward
    positive-radius locus is open. A strictly positive ball
    margin leaves room for a spatial perturbation; no openness
    assumption on A is needed for this supporting step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric InnerParallelFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_parallel_family_open]: openness of the
    original inward locus whose component is C_e in Federer
    4.1.4, p. 348. *)
Theorem inner_parallel_family_open (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) (O:R->set X):
  is_inner_parallel_family NX A O ->forall e:R,0<e ->
  @open (real_norm_metric_space hNX) (O e).
Proof.
move=>hO e he; rewrite openE=>x hx.
have[_ [r [her hBall]]]:=(@hO e he x).1 hx.
pose d:=(r-e)/2.
pose q:=(r+e)/2.
have hd:0<d by rewrite /d divr_gt0 ?subr_gt0 // ltr0n.
have hQ:e<q by rewrite /q; lra.
apply/(metricType_numDomainType.nbhs_mdistP (x:real_norm_metric_space hNX) _).
exists d; first exact hd.
move=>y hy.
have hNear:NX (y-x)<d.
  change (is_true (NX (x-y)<d)) in hy.
  by rewrite (real_seminorm_subtract hNX.1).
have hAy:A y.
  apply:hBall; apply:lt_trans hNear _; rewrite /d; lra.
apply:(@hO e he y).2; split=>//; exists q; split=>// z hz.
have hSum:(z-y)+(y-x)=z-x by rewrite addrA subrK.
have hTriangle:=real_seminorm_triangle hNX.1 (z-y) (y-x).
rewrite hSum in hTriangle; apply:hBall.
apply:le_lt_trans hTriangle _; rewrite /d in hNear; rewrite /q in hz; lra.
Qed.
