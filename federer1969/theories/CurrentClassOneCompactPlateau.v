(** Federer (1969), 4.1.14, p. 372, final sentence:
    smooth the original class-one map locally without changing its
    differential near the compact current support. The cutoff class
    law is already proved in 3.1.22, p. 236. All arguments here
    retain class one; no infinite differentiability of f is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLocalAgreement NormBoundedLinearTopology NormClassOneUP
  NormRegularity NormCutoffProductClass GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SmoothCompactSet
  CompactSupportFunctionUP SmoothCompactCutoffUP SmoothCompactCutoffSealed
  CurrentMapDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentClassOneCompactPlateau.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).

(** Source for [current_class_one_map_differential_actual]: the
    actual Df in the class-one clause of Federer 4.1.14, p. 372,
    is supplied by the original class-one hypothesis itself. *)
Theorem current_class_one_map_differential_actual (U:set X) (f:X->Y):
  norm_class_one NX NY U f->forall x,U x->
    has_norm_differential NX NY U f x (@current_map_differential R n nu U f x).
Proof.
move=>[D hD] x hx.
have hActual:=norm_class_one_differential hD hx.
rewrite (@current_map_differential_unique R n nu U f x (D x) hActual).
exact:hActual.
Qed.

(** Source for [current_class_one_differential_plateau]: the local
    representative in the smoothing argument for Federer 4.1.14,
    p. 372, has exactly Df on the original open plateau. *)
Theorem current_class_one_differential_plateau (U W:set X) (f F:X->Y):
  norm_class_one NX NY U f ->
  (forall x,W x->norm_domain_interior NX W x) ->W `<=` U ->
  (forall x,W x->F x=f x) ->
  forall x,W x->@current_map_differential R n nu (fun _=>True) F x=
    @current_map_differential R n nu U f x.
Proof.
move=>hClass hW hWU hAgreement x hx.
have hD:=@current_class_one_map_differential_actual U f hClass x (hWU x hx).
have[r [hr hBall]]:=hW x hx.
apply:current_map_differential_unique.
apply:(@norm_differential_local_agreement R X Y NX NY hNX U (fun _=>True)
  f F x (@current_map_differential R n nu U f x) r hr).
- move=>h hh;split;first by [].
  move=>_;exact:hWU (x+h) (hBall h hh).
- move=>h hh _;exact:esym (hAgreement (x+h) (hBall h hh)).
- exact:hD.
Qed.

(** Source for [current_class_one_compact_plateau_exists]: a
    globally class-one compactly supported ambient representative
    agrees with f and Df on an open neighbourhood of K, supporting
    Federer 4.1.14, p. 372. The original open target is irrelevant
    to this local ambient construction; no point in it is selected. *)
Theorem current_class_one_compact_plateau_exists (U:set X)
    (hU:forall x,U x->norm_domain_interior NX U x)
    (K:smooth_compact_set hNX U) (f:X->Y):
  norm_class_one NX NY U f ->
  exists F:X->Y,exists W C:set X,
    @open (real_norm_metric_space hNX) W /\
    smooth_compact_carrier K `<=` W /\ W `<=` U /\
    (forall x,W x->F x=f x) /\
    @compact (real_norm_metric_space hNX) C /\ C `<=` U /\
    (forall x,~C x->F x=0) /\
    norm_class_one NX NY (fun _=>True) F /\
    forall x,W x->@current_map_differential R n nu (fun _=>True) F x=
      @current_map_differential R n nu U f x.
Proof.
move=>hClass.
pose chi:=@SmoothCompactCutoff.value R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) U K hU.
pose hChi:=@SmoothCompactCutoff.laws R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) U K hU.
pose C:=@real_function_support R (real_norm_metric_space hNX) chi.
have hCU:C `<=` U:=smooth_cutoff_support_in_domain hChi.
have hOffChi:forall x,~C x->chi x=0.
  move=>x hx;exact:(@real_function_zero_off_support R
    (real_norm_metric_space hNX) chi x hx).
have[A [hA [hKA hOne]]]:=smooth_cutoff_neighbourhood_plateau hChi.
pose W:=A `&` U.
have hUOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx).
have hW:@open (real_norm_metric_space hNX) W:=openI hA hUOpen.
have hWInterior:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX W x).2
    (open_nbhs_nbhs (conj hW hx)).
have hKW:smooth_compact_carrier K `<=` W.
  move=>x hx;split;[exact:hKA x hx|exact:smooth_compact_in_domain K x hx].
have hWU:W `<=` U by move=>x [_ hx].
pose F x:=chi x*:f x.
have hAgreement:forall x,W x->F x=f x.
  move=>x [hAx _].
  have hChiOne:chi x = 1:=hOne x hAx.
  have hScale:=congr1 (fun c:R=>c*:f x) hChiOne.
  rewrite scale1r in hScale.
  exact:hScale.
have hFinite:norm_class hNX hNY U f 1%N:=
  (@norm_class_firstP R X Y NX NY hNX hNY U f).2 hClass.
have hFullFinite:=@norm_class_cutoff_product R X Y NX NY hNX hNY U C chi f 1%N
  hFinite (smooth_cutoff_class hChi 1%N)
  (@real_function_support_closed R (real_norm_metric_space hNX) chi) hCU hOffChi.
have hFull:norm_class_one NX NY (fun _=>True) F:=
  (@norm_class_firstP R X Y NX NY hNX hNY (fun _=>True) F).1 hFullFinite.
exists F,W,C;split;first exact:hW.
split;first exact:hKW.
split;first exact:hWU.
split;first exact:hAgreement.
split;first exact:smooth_cutoff_compact hChi.
split;first exact:hCU.
split.
- move=>x hx.
  have hScale:=congr1 (fun c:R=>c*:f x) (hOffChi x hx).
  rewrite scale0r in hScale;exact:hScale.
- split;first exact:hFull.
  exact:current_class_one_differential_plateau hClass hWInterior hWU hAgreement.
Qed.
End CurrentClassOneCompactPlateau.
