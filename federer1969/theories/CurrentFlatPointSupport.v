(** Federer (1969), 4.1.15, p. 373: a flat
    current supported at one point vanishes in positive
    degree; in degree zero it equals T(1) delta_u.
    Compare identity with the constant retraction only on
    the actual support, then recall 4.1.10, p. 364. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations NormLocalLipschitzScalarProduct
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces CurrentCompactSmoothValue CurrentDirac
  CurrentOpenIdentitySmooth FlatCurrentsUP
  CurrentFlatIdentityPushforward CurrentFlatConstantPushforward
  CurrentFlatLipschitzSupportAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentFlatPointSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable u:X.
Hypothesis hu:U u.
Local Notation hIdImage:=(fun x (hx:U x)=>hx).
Local Notation hConstImage:=(fun (x:X) (_:U x)=>hu).
Local Notation hIdClass:=(@current_open_identity_smooth R n U hU).
Local Notation hConstClass:=(fun k=>@norm_class_constant R X X NX NX
  hNX hNX U u k hU).
Local Notation hIdLocal:=(@norm_class_one_locally_metric_lipschitz R X X NX NX
  hNX hNX U (fun x:X=>x)
  ((@norm_class_firstP R X X NX NX hNX hNX U (fun x:X=>x)).1 (hIdClass 1%N))).
Local Notation hConstLocal:=(@norm_class_one_locally_metric_lipschitz R X X NX NX
  hNX hNX U (fun _:X=>u)
  ((@norm_class_firstP R X X NX NX hNX hNX U (fun _:X=>u)).1 (hConstClass 1%N))).

(** Source for [current_flat_positive_point_support_zero]:
    T=0 when m>0, T is flat and sptT is contained
    in {u}, Federer 4.1.15, p. 373. Degree m=j+1
    retains every original positive natural degree. Neither
    normality nor finite mass is a premise. *)
Theorem current_flat_positive_point_support_zero
    (T:@current_space R h2 n U hU j.+1)
    (hFlat:@is_flat_current R h2 n j.+1 U hU T)
    (hSupport:forall x,@current_support R h2 n U hU j.+1 T x->x=u):
  T=0.
Proof.
have hAgreement:=@current_flat_lipschitz_support_agreement R h2 n n j.+1
  U U hU hU (fun x:X=>x) (fun _:X=>u)
  hIdImage hConstImage hIdLocal hConstLocal T hFlat hSupport.
have hIdentity:=@current_flat_lipschitz_identity_pushforward R h2 n j.+1 U hU
  hIdImage hIdLocal T hFlat.
have hConstant:=@current_flat_constant_positive_pushforward R h2 n U U hU hU
  u hConstImage hConstLocal j T hFlat.
exact:(eq_trans (esym hIdentity) (eq_trans hAgreement hConstant)).
Qed.

(** Source for [current_flat_zero_point_support]:
    T=T(1) delta_u when T is a flat zero-current
    supported in {u}, Federer 4.1.15, p. 373.
    T(1) is the existing actual compact smooth action,
    and every compactness witness gives this same formula. *)
Theorem current_flat_zero_point_support
    (T:@current_space R h2 n U hU 0%N)
    (hFlat:@is_flat_current R h2 n 0%N U hU T)
    (hSupport:forall x,@current_support R h2 n U hU 0%N T x->x=u):
  forall hCompact:@compact (real_norm_metric_space hNX)
    (@current_support R h2 n U hU 0%N T),
    T=@current_compact_total R h2 n U hU T hCompact*:
      @dirac_current R h2 n U hU u.
Proof.
move=>hCompact.
have hAgreement:=@current_flat_lipschitz_support_agreement R h2 n n 0%N
  U U hU hU (fun x:X=>x) (fun _:X=>u)
  hIdImage hConstImage hIdLocal hConstLocal T hFlat hSupport.
have hIdentity:=@current_flat_lipschitz_identity_pushforward R h2 n 0%N U hU
  hIdImage hIdLocal T hFlat.
have hConstant:=@current_flat_constant_zero_pushforward R h2 n U U hU hU
  u hConstImage hConstLocal T hFlat hCompact.
exact:(eq_trans (esym hIdentity) (eq_trans hAgreement hConstant)).
Qed.
End CurrentFlatPointSupport.

Arguments current_flat_positive_point_support_zero : clear implicits.
Arguments current_flat_zero_point_support : clear implicits.
