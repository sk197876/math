(** Federer (1969), 4.1.12, p. 368, used in
    4.1.14, pp. 370–372: a compact flat current
    restricts to any open neighbourhood of its support.
    First localise its compact flat index by the original
    K-intersect-closure law, then apply the same-index
    restriction and identity-inclusion recovery. The old
    K need not lie in the smaller neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct SmoothCompactSet CurrentSpaces CurrentOpenRestriction
  CurrentOpenIdentitySmooth CurrentCompactPushforwardAlgebra
  FlatCurrentsUP CurrentLipschitzCompactImage CurrentFlatOpenRestriction
  CurrentFlatCompactIndexNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatSupportNeighbourhoodRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables U W:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hW:forall x,W x->norm_domain_interior NX W x.
Hypothesis hWU:forall x,W x->U x.
Variable T:@current_space R h2 n U hU m.
Local Notation S := (@current_open_restriction R h2 n m W U hW hU hWU T).
Local Notation hIdentity := (@current_open_identity_smooth R n W hW).
Local Notation CompactS := (@compact (real_norm_metric_space hNX)
  (@current_support R h2 n W hW m S)).
Local Notation Push hCompact := (@current_compact_map_pushforward R h2 n n
  W U hW hU (fun x:X=>x) hWU hIdentity m S hCompact).

(** Source for [flat_current_support_neighbourhood_restriction_indexed]:
    restriction of the original compact flat T has
    a compact flat index in W and its identity
    inclusion recovers T, supporting Federer 4.1.14,
    pp. 370–372. Only spt T must lie in
    W; no flat membership with index spt T,
    normality or finite mass is assumed. *)
Theorem flat_current_support_neighbourhood_restriction_indexed:
  @is_flat_current R h2 n m U hU T->
  @current_support R h2 n U hU m T `<=` W->
  exists L:smooth_compact_set hNX W,
    @is_flat_current_supported_in R h2 n m W hW L S /\
    forall hCompact:CompactS,Push hCompact=T.
Proof.
move=>[K hK] hSupport.
have[L [hLW hFlatL]]:=@flat_current_compact_index_neighbourhood R h2 n m
  U W hU hW K T hK hSupport.
pose LW:=@current_compact_index_in_open R n U W L hLW.
have hSmall:=@flat_current_open_restriction R h2 n m U W hU hW hWU
  L hLW T hFlatL.
exists LW;split;first exact:hSmall.
move=>hCompact.
exact:(@flat_current_neighbourhood_inclusion_recovery R h2 n m U W hU hW hWU
  L hLW T hFlatL hCompact).
Qed.

(** Source for [flat_current_support_neighbourhood_restriction]:
    the actual restriction belongs to the original union
    F_m(W), with literal identity-inclusion recovery for
    every compactness witness, supporting Federer 4.1.14,
    pp. 370–372. A compact index is chosen only
    in the existence proof above. Empty W and
    empty support are retained. *)
Theorem flat_current_support_neighbourhood_restriction:
  @is_flat_current R h2 n m U hU T->
  @current_support R h2 n U hU m T `<=` W->
  @is_flat_current R h2 n m W hW S /\
  forall hCompact:CompactS,Push hCompact=T.
Proof.
move=>hFlat hSupport.
have[L [hL hRecovery]]:=
  flat_current_support_neighbourhood_restriction_indexed hFlat hSupport.
split;last exact:hRecovery.
by exists L.
Qed.
End CurrentFlatSupportNeighbourhoodRestriction.
