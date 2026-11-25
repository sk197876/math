(** Federer (1969), 4.1.1, p. 346: one
    compact neighbourhood contains K and all
    its small directional translates. This
    supporting geometric bound is shared by
    smooth-test and C1 integration arguments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LinearBasis NormClassZeroWhole NormCompactFunctionBound
  FiniteNormMetricCompactness SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_translation_tube]: one
    compact C contains K and every K-tv for
    |t|<=1, supporting Federer 4.1.1, p. 346. *)
Theorem smooth_compact_translation_tube (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) d (b:'I_d->X) (hb:is_basis b)
    (K:smooth_compact_set hNX (fun _=>True)) (v:X):
  exists C:smooth_compact_set hNX (fun _=>True),
    (smooth_compact_carrier K `<=` smooth_compact_carrier C) /\
    forall t:R,`|t|<=1 ->forall x,smooth_compact_carrier K (x+t*:v) ->smooth_compact_carrier C x.
Proof.
have hIdCont:continuous (fun x:real_norm_metric_space hNX=>x) by move=>x; exact:cvg_id.
have hId:=@norm_continuous_whole_class_zero R X X NX NX hNX hNX (fun x=>x) hIdCont.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X X NX NX hNX hNX
  setT (smooth_compact_carrier K) (fun x=>x) (smooth_compact_is_compact K) (fun _ _=>Logic.I) hId.
pose C:=@Build_smooth_compact_set R X NX hNX (fun _=>True) [set x|NX x<=M+NX v]
  (fun _ _=>Logic.I) (@finite_norm_metric_ball_compact R X NX hNX d b hb (M+NX v)).
have hNv:=real_seminorm_nonnegative hNX.1 v.
have hKC:smooth_compact_carrier K `<=` smooth_compact_carrier C.
  move=>x hx; apply:le_trans (hBound x hx) _; by rewrite lerDl.
exists C; split; first exact hKC.
move=>t ht x hKx.
have hTriangle:=real_seminorm_triangle hNX.1 (x+t*:v) (-(t*:v)).
rewrite addrK (real_seminorm_negate hNX.1) (real_seminorm_scale hNX.1) in hTriangle.
have hScale:`|t|*NX v<=NX v by have h:=ler_wpM2r hNv ht; by rewrite mul1r in h.
exact:(le_trans hTriangle (lerD (hBound _ hKx) hScale)).
Qed.
