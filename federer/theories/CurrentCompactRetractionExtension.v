(** Federer (1969), 4.1.15, p. 373: by 2.10.43
    a Lipschitz retraction of compact K onto C extends
    to a Lipschitz map from a neighbourhood Z of K
    into U, agreeing with inclusion on C. The ambient
    extension is only an existence witness; its U-image
    is proved on the derived neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP NormClassZeroTopology NormClassHigherRestriction NormOpenPreimage
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric LipschitzUP LipschitzBasic EuclideanLipschitzClassZero
  KirszbraunExtensionUP KirszbraunExtension RetractionUP SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentCompactRetractionExtension.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation MX:=(real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable K:smooth_compact_set hNX U.
Variable C:set X.
Variable r:X->X.
Hypothesis hRetraction:@is_metric_retraction R MX (smooth_compact_carrier K) C r.
Hypothesis hLip:@is_metric_lipschitz R MX MX (smooth_compact_carrier K) r.

(** Source for [current_compact_retraction_extension_exists]: the
    original neighbourhood extension asserted in Federer 4.1.15,
    p. 373. Retain r on K and inclusion on C.
    No retraction or U-valued extension on all U is
    assumed; empty K and C require no selected point. *)
Theorem current_compact_retraction_extension_exists:
  exists F:X->X,exists Z:set X,
    (forall x,Z x->norm_domain_interior NX Z x) /\
    smooth_compact_carrier K `<=` Z /\ Z `<=` U /\
    (forall x,Z x->U (F x)) /\
    @is_metric_lipschitz R MX MX Z F /\
    (forall x,smooth_compact_carrier K x->F x=r x) /\
    (forall x,C x->F x=x) /\ norm_class_zero NX NX setT F.
Proof.
have[L [hL hBound]]:=hLip.
have hInnerBound:@is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R n))
    (smooth_compact_carrier K) r L.
  split;first exact:hBound.1.
  move=>x y hx hy.
  change (is_true (NX (r x-r y)<=L*NX (x-y))).
  exact:hBound.2 x y hx hy.
pose F:=@euclidean_lipschitz_extension R n n (smooth_compact_carrier K) r L hInnerBound.
pose hF:=@euclidean_lipschitz_extension_specification R n n
  (smooth_compact_carrier K) r L hInnerBound.
pose hAgreement:=kirszbraun_extension_agreement_law hF.
pose hGlobalBound:=kirszbraun_extension_bound_law hF.
have hContinuous:norm_class_zero NX NX setT F.
  exact:(@euclidean_lipschitz_norm_class_zero R n n F
    (metric_lipschitz_of_bound hGlobalBound)).
have hRealBound:@is_metric_lipschitz_bound R MX MX setT F L.
  split;first exact:hGlobalBound.1.
  move=>x y _ _.
  change (is_true (NX (F x-F y)<=L*NX (x-y))).
  exact:hGlobalBound.2 x y Logic.I Logic.I.
have hUOpen:@open MX U.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx).
have hRestricted:norm_class_zero NX NX U F.
  exact:(@norm_class_zero_open_restriction R X X NX NX setT U F
    (fun _ _=>Logic.I) hU hContinuous).
pose Z:set X:=[set x|U x /\ U (F x)].
have hZOpen:@open MX Z.
  exact:(@norm_class_zero_open_preimage R X X NX NX hNX hNX U U F
    hRestricted hUOpen).
have hZ:forall x,Z x->norm_domain_interior NX Z x.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX Z x).2
    (open_nbhs_nbhs (conj hZOpen hx)).
have hCU:C `<=` U.
  move=>x hx;apply:(smooth_compact_in_domain K x).
  exact:(@metric_retraction_subset R MX (smooth_compact_carrier K) C r hRetraction x hx).
have hKZ:smooth_compact_carrier K `<=` Z.
  move=>x hx;split;first exact:smooth_compact_in_domain K x hx.
  change (U (F x)).
  have hFx:F x=r x:=@hAgreement x hx.
  rewrite hFx.
  exact:(@hCU (r x)
    (@metric_retraction_range R MX (smooth_compact_carrier K) C r hRetraction x hx)).
have hLipZ:@is_metric_lipschitz R MX MX Z F.
  apply:metric_lipschitz_of_bound.
  exact:(@metric_lipschitz_bound_restrict R MX MX setT Z F L
    (fun _ _=>Logic.I) hRealBound).
have hFixed:forall x,C x->F x=x.
  move=>x hx.
  exact:(eq_trans (@hAgreement x
    (@metric_retraction_subset R MX (smooth_compact_carrier K) C r hRetraction x hx))
    (@metric_retraction_fixed R MX (smooth_compact_carrier K) C r hRetraction x hx)).
exists F,Z;split;first exact:hZ.
split;first exact:hKZ.
split;first by move=>x hx;exact:hx.1.
split;first by move=>x hx;exact:hx.2.
split;first exact:hLipZ.
split;first exact:hAgreement.
by split.
Qed.

(** Source for [current_compact_retraction_index_exists]: the
    retract C of the original compact K is compact, so
    the printed F_(m,C)(U) in Federer 4.1.15, p. 373,
    has its actual original compact index. Compactness is
    derived; no inhabitance of C is assumed. *)
Theorem current_compact_retraction_index_exists:
  exists D:smooth_compact_set hNX U,smooth_compact_carrier D=C.
Proof.
have[F [Z [hZ [hKZ [hZU [hImage [hFLip [hAgreement [hFixed hContinuous]]]]]]]]]:=
  current_compact_retraction_extension_exists.
have hFTopology:continuous (fun x:MX=>(F x:MX)).
  move=>x;exact:(@norm_class_zero_continuous_at R X X NX NX hNX hNX
    setT F x hContinuous Logic.I).
have hImageEqual:(F @` smooth_compact_carrier K:set MX)=C.
  apply:funext=>y;apply:propext;split.
  - move=>[x hx <-];rewrite (@hAgreement x hx).
    exact:(@metric_retraction_range R MX (smooth_compact_carrier K) C r hRetraction x hx).
  - move=>hy;exists y.
    + exact:(@metric_retraction_subset R MX (smooth_compact_carrier K) C r hRetraction y hy).
    + exact:(@hFixed y hy).
have hCompact:@compact MX C.
  rewrite -hImageEqual.
  exact:continuous_compact (continuous_subspaceT hFTopology) (smooth_compact_is_compact K).
have hCU:C `<=` U.
  move=>x hx;apply:(smooth_compact_in_domain K x).
  exact:(@metric_retraction_subset R MX (smooth_compact_carrier K) C r hRetraction x hx).
exists (@Build_smooth_compact_set R X NX hNX U C hCU hCompact).
reflexivity.
Qed.
End CurrentCompactRetractionExtension.
