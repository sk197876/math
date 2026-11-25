(** Federer (1969), 3.4.8(5), p. 328:
    continuous contractions give joint continuity of the
    derivative action. This lemma supplies the metric
    topology form of the bounded bilinear continuity law
    used in 3.1.11, p. 220. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_bilinear_continuous_factors]: joint
    continuity of a bounded bilinear operation, supporting
    the actual derivative action in 3.4.8(5), p. 328.
    Both factors may vary over any topological parameter space. *)
Theorem bounded_bilinear_continuous_factors (R:realType)
    (U V W:lmodType R) (NU:U->R) (NV:V->R) (NW:W->R)
    (hNU:is_real_norm NU) (hNV:is_real_norm NV) (hNW:is_real_norm NW)
    (B:U->V->W) (hB:norm_bounded_bilinear NU NV NW B)
    (P:topologicalType) (f:P->U) (g:P->V):
  continuous (fun p:P=>(f p:real_norm_metric_space hNU)) ->
  continuous (fun p:P=>(g p:real_norm_metric_space hNV)) ->
  continuous (fun p:P=>(B (f p) (g p):real_norm_metric_space hNW)).
Proof.
move=>hF hG p A hA.
have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
  (B (f p) (g p):real_norm_metric_space hNW) A) hA.
have [hBil [C [hC hBound]]]:=hB.
have hNF:=real_seminorm_nonnegative hNU.1 (f p).
have hNG:=real_seminorm_nonnegative hNV.1 (g p).
pose K:R:=C*(NU (f p)+1+NV (g p))+1.
have hSum:0<=NU (f p)+1+NV (g p) by lra.
have hCK:=mulr_ge0 hC hSum.
have hK:0<K by rewrite /K;lra.
pose delta:R:=epsilon/K.
have hDelta:0<delta by rewrite /delta divr_gt0.
have hNearF d (hd:0<d):nbhs p (fun q:P=>NU (f q-f p)<d).
  have hY:nbhs (f p:real_norm_metric_space hNU)
      [set y:real_norm_metric_space hNU|NU (y-f p)<d].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP (f p:real_norm_metric_space hNU) _)).
    exists d;first exact:hd.
    move=>y hy;change (is_true (NU (y-f p)<d)).
    by rewrite (real_seminorm_subtract hNU.1).
  exact:(hF p _ hY).
have hNearG d (hd:0<d):nbhs p (fun q:P=>NV (g q-g p)<d).
  have hY:nbhs (g p:real_norm_metric_space hNV)
      [set y:real_norm_metric_space hNV|NV (y-g p)<d].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP (g p:real_norm_metric_space hNV) _)).
    exists d;first exact:hd.
    move=>y hy;change (is_true (NV (y-g p)<d)).
    by rewrite (real_seminorm_subtract hNV.1).
  exact:(hG p _ hY).
have hBoth:=@filterI P (nbhs p) (nbhs_filter p) _ _
  (hNearF 1 ltr01) (@filterI P (nbhs p) (nbhs_filter p) _ _
    (hNearF delta hDelta) (hNearG delta hDelta)).
change (nbhs p (fun q:P=>A (B (f q) (g q)))).
apply:filterS hBoth=>q [hOne [hFSmall hGSmall]];apply:hBall.
change (is_true (NW (B (f p) (g p)-B (f q) (g q))<epsilon)).
rewrite (real_seminorm_subtract hNW.1).
have hFBound:NU (f q)<=NU (f p)+1.
  have hTriangle:=real_seminorm_triangle hNU.1 (f p) (f q-f p).
  rewrite addrC subrK in hTriangle.
  exact:le_trans hTriangle (lerD (lexx _) (ltW hOne)).
have hFirst:NW (B (f q) (g q-g p))<=C*((NU (f p)+1)*delta).
  apply:le_trans (hBound _ _) _;apply:(ler_wpM2l hC).
  exact:(ler_pM (real_seminorm_nonnegative hNU.1 _) (real_seminorm_nonnegative hNV.1 _)
    hFBound (ltW hGSmall)).
have hSecond:NW (B (f q-f p) (g p))<=C*(delta*NV (g p)).
  apply:le_trans (hBound _ _) _;apply:(ler_wpM2l hC).
  exact:(ler_wpM2r hNG (ltW hFSmall)).
have hEquation:B (f q) (g q)-B (f p) (g p)=
    B (f q) (g q-g p)+B (f q-f p) (g p).
  by rewrite (bilBr hBil) (bilBl hBil) addrA subrK.
rewrite hEquation;apply:le_lt_trans (real_seminorm_triangle hNW.1 _ _) _.
apply:le_lt_trans (lerD hFirst hSecond) _.
have hValue:delta*K=epsilon by rewrite /delta divfK // gt_eqF.
rewrite /K in hValue;nra.
Qed.
