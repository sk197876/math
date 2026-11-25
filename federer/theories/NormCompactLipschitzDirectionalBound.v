(** Federer (1969), 4.1.2, p. 347: one compact Lipschitz
    bound controls every small directional quotient and every actual
    derivative on a compact source part. The same estimate supplies
    local norm integrability and the convolution dominator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteCoordinates LipschitzUP SmoothCompactSet SmoothCompactThickening NormLocalLipschitzCompact
  NormedCurveDerivativeUP PuncturedNormReciprocalSequence NormSequenceLowerLimit ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_compact_lipschitz_directional_bound]: the
    uniform compact bound on input quotients and derivatives used
    in the locally Lipschitz clause of Federer 4.1.2, p. 347.
    No reflexivity is needed for this necessary bound on a
    derivative that exists. *)
Theorem norm_compact_lipschitz_directional_bound (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (f:R_n R n->Y) (v:R_n R n):
  is_locally_metric_lipschitz setT
    (f:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))
      ->real_norm_metric_space hNY) ->
  forall K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True),
  exists M:R,0<=M /\
    (forall x,smooth_compact_carrier K x ->forall t:R,t!=0 ->`|t|<=1 ->
      NY (t^-1*:(f (x+t*:v)-f x))<=M) /\
    (forall x,smooth_compact_carrier K x ->forall w:Y,
      punctured_norm_limit NY (fun t=>t^-1*:(f (x+t*:v)-f x)) w ->NY w<=M).
Proof.
move=>hLocal K.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hNv:=real_seminorm_nonnegative hN.1 v.
have[C [hKC hTube]]:=@smooth_compact_thickening R X N hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) K (N v) hNv.
have[L [hL hLip]]:=@norm_local_lipschitz_compact R X Y N NY hN hNY f
  (smooth_compact_carrier C) hLocal (smooth_compact_is_compact C).
have hQ x (hx:smooth_compact_carrier K x) t (ht:t!=0) (hUnit:`|t|<=1):
    NY (t^-1*:(f (x+t*:v)-f x))<=L*N v.
  have hCx:=hKC x hx.
  have hShift:x+t*:v-x=t*:v by rewrite addrAC subrr add0r.
  have hScale:N (t*:v)=`|t|*N v:=real_seminorm_scale hN.1 t v.
  have hCShift:smooth_compact_carrier C (x+t*:v).
    apply:(@hTube (x+t*:v) x hx).
    change (is_true (N (x+t*:v-x)<=N v)).
    rewrite hShift.
    rewrite hScale.
    have h:=ler_wpM2r hNv hUnit; by rewrite mul1r in h.
  have hAbs:0<`|t| by rewrite normr_gt0.
  rewrite (real_seminorm_scale hNY.1) normfV mulrC ler_pdivrMr //.
  have h:=hLip.2 (x+t*:v) x hCShift hCx.
  change (is_true (NY (f (x+t*:v)-f x)<=L*N (x+t*:v-x))) in h.
  by rewrite hShift hScale mulrA mulrAC in h.
exists (L*N v); split; first exact:mulr_ge0 (ltW hL) hNv.
split; first exact hQ.
move=>x hx w hw.
have hSeq:=@punctured_norm_reciprocal_sequence R Y NY hNY
  (fun t=>t^-1*:(f (x+t*:v)-f x)) w hw.
have hNorm:=@norm_sequence_extended_order_limit R Y NY hNY
  (fun m:nat=>((((m.+1)%:R:R)^-1)^-1*:(f (x+(((m.+1)%:R:R)^-1)*:v)-f x):real_norm_metric_space hNY))
  (w:real_norm_metric_space hNY) hSeq.
have hUpper:((NY w)%:E<=(L*N v)%:E)%E.
  apply:(extended_order_limit_upper_bound hNorm)=>m; rewrite lee_fin.
  have hPos:0<((m.+1)%:R:R) by rewrite ltr0n.
  have hInvPos:0<((m.+1)%:R:R)^-1 by rewrite invr_gt0.
  have hUnit:((m.+1)%:R:R)^-1<=1.
    by rewrite (invf_le1 hPos) ler1n.
  apply:(@hQ x hx (((m.+1)%:R:R)^-1) (lt0r_neq0 hInvPos)).
  by rewrite (ger0_norm (ltW hInvPos)).
by rewrite lee_fin in hUpper.
Qed.
