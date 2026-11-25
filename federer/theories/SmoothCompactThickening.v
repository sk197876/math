(** Federer (1969), 4.1.2, p. 347: one
    compact bound contains a compact support and
    all its translates by vectors of bounded norm.
    This is the geometric common-support step in
    the original convergence assertion for test functions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LinearBasis NormClassZeroWhole NormCompactFunctionBound
  FiniteNormMetricCompactness SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_thickening]: the common compact
    support used for Phi_epsilon*f at bounded
    positive scales, supporting Federer 4.1.2, p. 347.
    The compact bound is an existence witness;
    it replaces no definition of support. *)
Theorem smooth_compact_thickening (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) d (b:'I_d->X) (hb:is_basis b)
    (K:smooth_compact_set hNX (fun _=>True)) r:
  0<=r ->exists C:smooth_compact_set hNX (fun _=>True),
    (smooth_compact_carrier K `<=` smooth_compact_carrier C) /\
    forall x z,smooth_compact_carrier K z ->NX (x-z)<=r ->smooth_compact_carrier C x.
Proof.
move=>hr.
have hIdCont:continuous (fun x:real_norm_metric_space hNX=>x) by move=>x; exact:cvg_id.
have hId:=@norm_continuous_whole_class_zero R X X NX NX hNX hNX (fun x=>x) hIdCont.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X X NX NX hNX hNX
  setT (smooth_compact_carrier K) (fun x=>x) (smooth_compact_is_compact K) (fun _ _=>Logic.I) hId.
pose C:=@Build_smooth_compact_set R X NX hNX (fun _=>True) [set x|NX x<=M+r]
  (fun _ _=>Logic.I) (@finite_norm_metric_ball_compact R X NX hNX d b hb (M+r)).
exists C; split.
- move=>x hx; apply:le_trans (hBound x hx) _; by rewrite lerDl.
- move=>x z hz hNear.
  have hSum:z+(x-z)=x by rewrite addrC subrK.
  have hTriangle:=real_seminorm_triangle hNX.1 z (x-z).
  rewrite hSum in hTriangle.
  exact:(le_trans hTriangle (lerD (hBound z hz) hNear)).
Qed.
