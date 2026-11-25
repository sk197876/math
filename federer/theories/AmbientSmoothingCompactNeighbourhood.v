(** Federer (1969), 4.1.14, p. 370: the actual ambient
    smoothings of a map agreeing with f on K take one fixed
    source neighbourhood into the original open target V.
    This supporting geometry keeps the actual smoothing family;
    it does not replace it by a separate extension witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP NormClassZeroTopology
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SmoothCompactSet SmoothCompactOpenTubeClosure
  MetricOpenThickening MetricOpenThickeningClosure MetricCompactNeighbourhood
  EuclideanOwnNormCompleteness SmoothingKernelUP SmoothingDilationUP
  SmoothingConvolutionUP SmoothingLipschitzError.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AmbientSmoothingCompactNeighbourhood.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable K:smooth_compact_set hNX U.
Variables f F:X->Y.
Variable L:R.
Hypothesis hL:0<=L.
Hypothesis hFContinuous:norm_class_zero NX NY (fun _=>True) F.
Hypothesis hFBound:forall x y,NY (F x-F y)<=L*NX (x-y).
Hypothesis hAgreement:forall x,smooth_compact_carrier K x->F x=f x.
Arguments hAgreement : clear implicits.
Hypothesis hImageK:forall x,smooth_compact_carrier K x->V (f x).
Arguments hImageK : clear implicits.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable g:R->X->Y.
Hypothesis hConvolution:forall e:R,0<e->is_smoothing_convolution hNY (family e) F (g e).
Arguments hConvolution : clear implicits.

(** Source for [ambient_smoothing_compact_neighbourhood]: the
    common source Z with compact closure in U and V-valued
    approximants, Federer 4.1.14, p. 370. The empty K gives
    exactly the empty Z, including when V is empty. *)
Theorem ambient_smoothing_compact_neighbourhood:
  exists r:R,exists Z:set X,0<r /\
    (forall x,Z x->norm_domain_interior NX Z x) /\
    smooth_compact_carrier K `<=` Z /\
    @compact XT (@closure XT Z) /\ @closure XT Z `<=` U /\
    (smooth_compact_carrier K=set0->Z=set0) /\
    forall e:R,0<e->e<=r->forall x,Z x->V (g e x).
Proof.
have hNonnegative:0<=L:=hL.
have hFTopology:continuous (fun x:XT=>(F x:YT)).
  move=>x;exact:(@norm_class_zero_continuous_at R X Y NX NY hNX hNY
    (fun _=>True) F x hFContinuous Logic.I).
have hImageCompact:@compact YT (F @` smooth_compact_carrier K).
  exact:continuous_compact (continuous_subspaceT hFTopology) (smooth_compact_is_compact K).
have hVOpen:@open YT V.
  rewrite openE=>y hy.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY V y).1 (hV y hy).
have hImageContained:F @` smooth_compact_carrier K `<=` V.
  move=>y [x hx <-];rewrite (hAgreement x hx);exact:hImageK x hx.
have[d [hd hTargetTube]]:=@compact_metric_open_thickening R YT
  (F @` smooth_compact_carrier K) V hImageCompact hVOpen hImageContained.
have[r0 [hr0 hSourceTube]]:=@smooth_compact_open_tube_closure R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU K.
pose B:R:=4*(L+1).
have hB:0<B.
  rewrite /B;apply:mulr_gt0;first by rewrite ltr0n.
  have hOneBound:1<=L+1 by rewrite lerDr.
  exact:(lt_le_trans ltr01 hOneBound).
pose r:=Num.min r0 (d/B).
have hr:0<r by rewrite /r lt_min hr0 divr_gt0.
have hrr0:r<=r0 by rewrite /r ge_min lexx.
have hrTarget:r<=d/B by rewrite /r ge_min lexx orbT.
have hProduct:B*r<=d.
  have h:=ler_wpM2l (ltW hB) hrTarget.
  have hCancel:B*(d/B)=d by rewrite mulrC divfK ?gt_eqF.
  by rewrite hCancel in h.
have hMargin:2*L*r<d by rewrite /B in hProduct;nra.
pose Z:set X:=@metric_open_thickening R XT (smooth_compact_carrier K) r.
have hZOpen:forall x,Z x->norm_domain_interior NX Z x.
  move=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX Z x).2
    (open_nbhs_nbhs (conj
      (@metric_open_thickening_open R XT (smooth_compact_carrier K) r) hx)).
have hContains:smooth_compact_carrier K `<=` Z:=
  @metric_open_thickening_includes R XT (smooth_compact_carrier K) r hr.
have[hClosureCompact hClosureInDomain]:=hSourceTube r hr hrr0.
exists r,Z;split;first exact:hr.
split;first exact:hZOpen.
split;first exact:hContains.
split;first exact:hClosureCompact.
split;first exact:hClosureInDomain.
split;first by move=>hEmpty;rewrite /Z hEmpty;exact:(@metric_open_thickening_empty R XT r).
move=>e he hSmall x [a ha hax];apply:hTargetTube.
exists (F a);first by exists a.
change (is_true (NY (F a-g e x)<d)).
rewrite (real_seminorm_subtract hNY.1).
have hNear:NX (x-a)<=r.
  change (is_true (NX (a-x)<r)) in hax.
  rewrite (real_seminorm_subtract hNX.1);exact:ltW hax.
have hTriangle:=real_seminorm_triangle hNY.1 (g e x-F x) (F x-F a).
have hSplit:(g e x-F x)+(F x-F a)=g e x-F a by rewrite addrA subrK.
rewrite hSplit in hTriangle.
have hError:=@smoothing_lipschitz_error_bound R n Y NY hNY
  (@euclidean_own_norm_complete R nu) phi hPhi family hFamily e F (g e) L
  he hL (hConvolution e he) hFBound x.
have hLocalBound:=le_trans (hFBound x a) (ler_wpM2l hL hNear).
have hScale:=ler_wpM2l hL hSmall;nra.
Qed.
End AmbientSmoothingCompactNeighbourhood.
