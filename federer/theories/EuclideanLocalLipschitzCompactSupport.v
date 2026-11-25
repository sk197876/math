(** Federer (1969), 4.1.14, p. 371: the compactly localised
    original map admits a finite common Lipschitz bound before
    smoothing. Reuse the compact local bounds of 2.2.7, p. 64,
    on one larger Euclidean ball. The actual plateau values and
    their derivatives are unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import RealNormUP NormMetric NormClassOneUP NormClassZeroWhole
  NormCompactFunctionBound NormLocalLipschitzCompact MetricLocalLipschitzContinuity
  LipschitzUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness MetricClosedBalls EuclideanNormClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_local_lipschitz_compact_support_global]:
    a finite ambient Lipschitz bound for the compactly localised
    field used in Federer 4.1.14, p. 371. This bound is not
    substituted for the original pointwise majorant. It supplies
    only common smoothness and approximation control. *)
Theorem euclidean_local_lipschitz_compact_support_global (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (F:R_n R n->Y)
    (C:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))):
  compact C ->(forall x,~C x->F x=0) ->
  @is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space hNY) setT F ->
  exists L:R,0<L /\ forall x y,NY (F x-F y)<=
    L*inner_norm (@euclidean_inner_productP R n) (x-y).
Proof.
move=>hC hOff hLocal.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hIdentity:norm_class_zero NX NX setT (fun x:X=>x).
  apply:(@norm_continuous_whole_class_zero R X X NX NX hNX hNX (fun x=>x)).
  by move=>x;exact:cvg_id.
have[r [hr hRadius]]:=@norm_class_zero_compact_bounded R X X NX NX hNX hNX
  setT C (fun x=>x) hC (fun _ _=>Logic.I) hIdentity.
have hContinuous:norm_class_zero NX NY setT F:=
  norm_continuous_whole_class_zero (metric_local_lipschitz_continuous_whole hLocal).
have[B [hB hNorm]]:=@norm_class_zero_compact_bounded R X Y NX NY hNX hNY
  setT C F hC (fun _ _=>Logic.I) hContinuous.
pose K:=@metric_closed_ball R (real_norm_metric_space hNX) 0 (r+1).
have hK:compact K:=@euclidean_norm_closed_ball_compact R n 0 (r+1).
have[L0 [hL0 hBound]]:=@norm_local_lipschitz_compact R X Y NX NY hNX hNY F K hLocal hK.
have hCK:C `<=` K.
  move=>x hx.
  change (is_true (NX (0-x)<=r+1)).
  have hZeroDifference:NX (0-x)=NX x.
    rewrite sub0r;exact:real_seminorm_negate hNX.1 x.
  rewrite hZeroDifference.
  have h:=hRadius x hx;lra.
pose L:=L0+B+1.
have hL:0<L by rewrite /L;lra.
have hL0L:L0<=L by rewrite /L;lra.
have hBL:B<=L by rewrite /L;lra.
have hOne:forall x y,C x->NY (F x-F y)<=L*NX (x-y).
  move=>x y hx.
  case:(pselect (K y))=>[hy|hy].
  - exact:(le_trans (hBound.2 x y (hCK x hx) hy)
      (ler_wpM2r (real_seminorm_nonnegative hNX.1 (x-y)) hL0L)).
  - have hNoC:~C y by move=>hCy;exact:hy (hCK y hCy).
    have hFar:r+1<NX y.
      have hNot:~(NX y<=r+1).
        move=>hSmall;apply:hy.
        change (is_true (NX (0-y)<=r+1)).
        have hZeroDifference:NX (0-y)=NX y.
          rewrite sub0r;exact:real_seminorm_negate hNX.1 y.
        by rewrite hZeroDifference.
      by rewrite ltNge;exact/negP.
    have hRadiusX:=hRadius x hx.
    change (is_true (NX x<=r)) in hRadiusX.
    have hTriangle:=real_seminorm_triangle hNX.1 (y-x) x.
    rewrite subrK (real_seminorm_subtract hNX.1 y x) in hTriangle.
    change (is_true (NX y<=NX (x-y)+NX x)) in hTriangle.
    have hDistanceStrict:1<NX (x-y).
      have hUpper:NX y<=NX (x-y)+r:=le_trans hTriangle (lerD (lexx _) hRadiusX).
      have hShift:1+r<NX (x-y)+r.
        rewrite addrC;exact:(lt_le_trans hFar hUpper).
      by move:hShift;rewrite ltrD2r.
    have hDistance:1<=NX (x-y):=ltW hDistanceStrict.
    rewrite (hOff y hNoC) subr0.
    apply:(le_trans (hNorm x hx)).
    have hProduct:=ler_wpM2l (ltW hL) hDistance.
    rewrite mulr1 in hProduct.
    exact:(le_trans hBL hProduct).
exists L;split;first exact:hL.
move=>x y;case:(pselect (C x))=>[hx|hx];first exact:hOne x y hx.
case:(pselect (C y))=>[hy|hy].
- rewrite (real_seminorm_subtract hNY.1 (F x) (F y))
    (real_seminorm_subtract hNX.1 x y);exact:hOne y x hy.
- rewrite (hOff x hx) (hOff y hy) subrr (real_seminorm_zero hNY.1).
  exact:mulr_ge0 (ltW hL) (real_seminorm_nonnegative hNX.1 (x-y)).
Qed.
