(** Federer (1969), 3.4.2(7), p. 314: the dimension induction
    gives compact flat pieces outside the common critical set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals topology.
From Federer Require Import Hom GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP NormMetric
  MetricSubsetBackground FiniteNormMetricPolish SeparableMetricBaseSealed
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalManifoldClassLaws
  CriticalManifoldCompactCover CriticalFlatPiecesUP CriticalFlatCoverUP
  CriticalFlatPieceRestriction CriticalNoncommonCuttingManifold
  CriticalCountableCuttingFamily CriticalCountablePieceAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_outside_flat_cover]: the final dimension
    induction in 3.4.2(7), p. 314. The smaller-dimension induction
    hypothesis is applied only to the actual cutting manifolds
    and their relatively closed intersections with C. The countable
    cover and the compact-manifold pairs are then assembled on
    the original source. Empty complements remain included. *)
Theorem critical_outside_flat_cover (R:realType) m d
    (Z:G (R_n R m) d) gamma k (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C:set (R_n R m)) (p:euclidean_projection_space R m gamma.+1) g:
  critical_manifold_family Z gamma.+1 k S ->
  is_critical_manifold_chart k (grassmann_val Z) S p g ->(m-d<=gamma)%N ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  (forall V:set (R_n R m),critical_manifold_family Z gamma k V ->
    @is_relatively_closed_source (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) V (V `&` C) ->
    exists T G,is_critical_flat_cover hNY Z gamma V (V `&` C) k T G) ->
  exists T G:nat->set (R_n R m),
    (forall j,is_critical_flat_piece hNY Z gamma.+1 S C k (T j) (G j)) /\
    C `\` critical_common_tangent_zero_set hNY (grassmann_val Z) S C k=\bigcup_j G j.
Proof.
move=>hFamily hChart hDimension hCS hC hInduction.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose E:=real_norm_metric_space hNX.
pose B:=critical_common_tangent_zero_set hNY (grassmann_val Z) S C k.
have hk:(1<=k)%N:=hFamily.2.1.
have hFamily1:=@critical_manifold_family_lower_class R m d Z gamma.+1 k 1 S
  (leqnn 1) hk hFamily.
have [D0 [hCount0 hDense]]:=@finite_norm_metric_separable R X NX hNX m
  (@coordinate_basis R m) (@coordinate_basisP R m).
pose Base:=@SeparableMetricBase.value R E D0 hCount0 hDense.
have hBase:=@SeparableMetricBase.laws R E D0 hCount0 hDense.
pose P:=fun V:set E=>critical_manifold_family Z gamma k V /\V `<=` S.
have hLocal a (hc:C a) (hn:~B a):exists V:set E,
    P V /\V `&` C `<=` C `\` B /\exists N:set E,open N /\N a /\C `&` N `<=` V.
  have [V [hV [hVS [hAvoid hN]]]]:=@critical_noncommon_cutting_manifold R m d Z gamma k
    Y NY hNY S C p g a hk hDimension hChart hCS hc hn.
  exists V;split;first by split.
  by split.
have [D [hCount [hD hUnion]]]:=@critical_countable_cutting_family E Base C B P hBase hLocal.
apply:(@critical_countable_flat_piece_assembly R m d Z gamma.+1 Y NY hNY S C (C `\` B)
  k D hFamily1 hCount hUnion).
move=>V hMember.
have [[hV hVS] hAvoid]:=hD V hMember.
have hClosedC:@closed E C:=compact_closed (@metric_hausdorff R E) hC.
have hClosed:@is_relatively_closed_source E V (V `&` C).
  exists C;by split.
have [T [G hCover]]:=hInduction V hV hClosed.
exists T,G;split;last exact:(critical_flat_cover_union hCover).
move=>j;exact:(critical_flat_piece_larger_source (leqnSn gamma) hVS
  (critical_flat_cover_pieces hCover j)).
Qed.
