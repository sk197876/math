(** Federer (1969), 3.2.31, p. 269: supporting scalar
    choices for a symmetric automorphism with small mu-th
    exterior norm and a controlled inverse on the differential range. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [small_exterior_majorant_scalars]: supporting
    the choice norm(Lambda^mu t)<epsilon and the strict
    inverse-derivative bound in Federer 3.2.31, p. 269.
    Choose a range scale M at least one and a positive small
    kernel scale d at most one. The actual bound is d*M^(mu-1).
    The stronger inverse ratio at most one half is used for
    class-one local unit Lipschitz estimates. No scalar choices
    are added as hypotheses to the final geometric theorem. *)
Lemma small_exterior_majorant_scalars (R:realType) (c epsilon:R) mu:
  0<=c ->0<epsilon ->
  exists M d:R,1<=M /\0<d /\d<=1 /\c/M<=1/2 /\d*M^+mu.-1<epsilon.
Proof.
move=>hc he.
pose M:=2*(c+1).
have hTwo:(0<(2:R)) by rewrite ltr0n.
have hTwoNz:(2:R)!=0 by rewrite gt_eqF.
have hC1:1<=c+1 by rewrite lerDr.
have hM2:2<=M.
  have hh:=ler_wpM2l (ler0n R 2) hC1.
  by rewrite mulr1 in hh.
have hM1:1<=M:=le_trans (ler1n R 2) hM2.
have hM:0<M:=lt_le_trans ltr01 hM1.
have hHalfM:(1/2)*M=c+1.
  by rewrite /M mulrA divfK // mul1r.
have hRatio:c/M<=1/2.
  by rewrite (@ler_pdivrMr R M (1/2) c hM) hHalfM lerDl ler01.
pose q:=M^+mu.-1.
have hq:0<=q:=exprn_ge0 mu.-1 (ltW hM).
have hq1:1<=q+1 by rewrite lerDr.
have hqp:0<q+1:=lt_le_trans ltr01 hq1.
pose d:=Num.min 1 (epsilon/(q+1)).
have hd:0<d by rewrite /d lt_min ltr01 divr_gt0.
have hd1:d<=1 by rewrite /d ge_min lexx.
have hdq:d<=epsilon/(q+1) by rewrite /d ge_min lexx orbT.
have hSmall:d*q<epsilon.
  have hBound:=ler_wpM2l hq hdq.
  have hRatioQ:q/(q+1)<1.
    by rewrite (@ltr_pdivrMr R (q+1) 1 q hqp) mul1r ltrDl.
  have hStrict:epsilon*(q/(q+1))<epsilon.
    by rewrite -[ltRHS]mulr1 (ltr_pM2l he).
  have hEq:q*(epsilon/(q+1))=epsilon*(q/(q+1)) by rewrite mulrCA.
  rewrite hEq in hBound.
  rewrite mulrC; exact (le_lt_trans hBound hStrict).
exists M,d; split; first exact hM1.
split; first exact hd.
split; first exact hd1.
by split.
Qed.
