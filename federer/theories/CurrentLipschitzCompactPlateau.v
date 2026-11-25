(** Federer (1969), 4.1.14, p. 371: local smoothing may
    be performed on an ambient locally Lipschitz representative
    agreeing with f near K. A smooth compact cutoff from 3.1.13,
    p. 225, and ambient zero extension preserve the original
    derivatives on that plateau. No global V-valued extension is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology NormRegularity
  NormClassOneUP LinearBasis SmoothCompactSet CompactSupportFunctionUP
  SmoothCompactCutoffUP SmoothCompactCutoffSealed SmoothZeroExtension
  LipschitzUP NormLocalLipschitzScalarProduct NormLocalLipschitzZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_lipschitz_compact_plateau_exists]: the original
    local smoothing underlying the derivative-majorant assertion of
    Federer 4.1.14, p. 371. The ambient field has compact support
    and agrees with f on an open W containing K. Empty K and U
    are retained without selecting any point of a target open set. *)
Theorem current_lipschitz_compact_plateau_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    n (b:'I_n->X) (hb:is_basis b) (U:set X)
    (hU:forall x,U x->norm_domain_interior NX U x)
    (K:smooth_compact_set hNX U) (f:X->Y):
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U f ->
  exists F:X->Y,exists W C:set X,
    @open (real_norm_metric_space hNX) W /\
    smooth_compact_carrier K `<=` W /\ W `<=` U /\
    (forall x,W x->F x=f x) /\
    @compact (real_norm_metric_space hNX) C /\ C `<=` U /\
    (forall x,~C x->F x=0) /\
    @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
      (real_norm_metric_space hNY) setT F.
Proof.
move=>hLocal.
pose chi:=@SmoothCompactCutoff.value R X NX hNX n b hb U K hU.
pose hChi:=@SmoothCompactCutoff.laws R X NX hNX n b hb U K hU.
pose C:=@real_function_support R (real_norm_metric_space hNX) chi.
have hCClosed:@closed (real_norm_metric_space hNX) C:=
  @real_function_support_closed R (real_norm_metric_space hNX) chi.
have hCU:C `<=` U:=smooth_cutoff_support_in_domain hChi.
have[W [hW [hKW hOne]]]:=smooth_cutoff_neighbourhood_plateau hChi.
pose A:=W `&` U.
have hUOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx).
have hAOpen:@open (real_norm_metric_space hNX) A:=openI hW hUOpen.
have hKA:smooth_compact_carrier K `<=` A.
  move=>x hx;split;[exact:hKW x hx|exact:smooth_compact_in_domain K x hx].
pose p x:=chi x*:f x.
pose F:=norm_zero_extended_function U p.
have hChiLocal:@is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space (@scalar_absolute_value_norm R)) U chi.
  have hFull:=@norm_class_one_locally_metric_lipschitz R X R^o NX
    (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) setT chi
    ((@norm_class_firstP R X R^o NX (fun t:R^o=>`|t|) hNX
      (@scalar_absolute_value_norm R) setT chi).1 (smooth_cutoff_class hChi 1%N)).
  move=>a ha.
  have[V [hV [L [hL hBound]]]]:=hFull a Logic.I.
  exists V;split;first exact:hV.
  exists L;split;first exact:hL.
  split;first exact:hBound.1.
  move=>x y [_ hx] [_ hy];exact:hBound.2 x y (conj Logic.I hx) (conj Logic.I hy).
have hPLocal:=@norm_locally_lipschitz_scalar_product R X Y NX NY hNX hNY U chi f
  hChiLocal hLocal.
have hOffP:forall x,U x->~C x->p x=0.
  move=>x _ hx;rewrite /p (@real_function_zero_off_support R
    (real_norm_metric_space hNX) chi x hx) scale0r;by [].
have hFLocal:=@norm_zero_extended_locally_lipschitz R X Y NX NY hNX hNY U C p
  hU hCClosed hCU hOffP hPLocal.
exists F,A,C;split;first exact:hAOpen.
split;first exact:hKA.
split;first by move=>x [_ hx].
split.
- move=>x [hWx hUx].
  have hValue:F x=p x:=@norm_zero_extended_function_on X Y U p x hUx.
  have hChiOne:chi x = 1:=hOne x hWx.
  have hScale:=congr1 (fun c:R=>c*:f x) hChiOne.
  rewrite scale1r in hScale.
  exact:eq_trans hValue hScale.
- split;first exact:smooth_cutoff_compact hChi.
  split;first exact:hCU.
  split;last exact:hFLocal.
  move=>x hx;rewrite /F;case:(pselect (U x))=>[hUx|hUx].
  + rewrite norm_zero_extended_function_on //;exact:hOffP x hUx hx.
  + exact:(@norm_zero_extended_function_off X Y U p x hUx).
Qed.
