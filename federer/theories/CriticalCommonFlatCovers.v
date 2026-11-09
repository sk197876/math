(** Federer (1969), 3.4.2(7), p. 313: countable flat covers
    of the common critical set in the two class-induction cases. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  HilbertFormCompactness RealNormUP NormMetric MetricSubsetBackground EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalManifoldClassLaws CriticalManifoldCompactCover
  CriticalFlatPiecesUP CriticalFlatCoverUP CriticalClassOneCommonPiece
  CriticalCommonZeroClosed CriticalHigherCommonPiece.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_class_one_common_flat_cover]: the
    constant choice U_j=S, H_j=B in 3.4.2(7), p. 313.
    The same compact piece works for every original class-one
    function, and its countable union is exactly B. *)
Theorem critical_class_one_common_flat_cover (R:realType) m d
    (Z:G (R_n R m) d) mu (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C:set (R_n R m)) (p:euclidean_projection_space R m mu) g:
  critical_manifold_family Z mu 1 S ->
  is_critical_manifold_chart 1 (grassmann_val Z) S p g ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  exists T G:nat->set (R_n R m),
    (forall j,is_critical_flat_piece hNY Z mu S C 1 (T j) (G j)) /\
    critical_common_tangent_zero_set hNY (grassmann_val Z) S C 1=\bigcup_j G j.
Proof.
move=>hFamily hChart hCS hC.
pose B:=critical_common_tangent_zero_set hNY (grassmann_val Z) S C 1.
have hPiece:=@critical_class_one_common_flat_piece R m d Z mu Y NY hNY S C p g
  hFamily hChart hCS hC.
exists (fun _=>S),(fun _=>B);split;first by move=>j.
apply/seteqP;split;[by move=>x hx;exists 0%N|by move=>x [j _ hx]].
Qed.

(** Source for [critical_higher_common_flat_cover]: the class
    induction on B in 3.4.2(7), p. 313. The lower-class
    induction hypothesis applies to the same original manifold
    with B as its relatively closed zero set. Each resulting
    compact pair lifts to the original higher class by the
    proved derivative-function argument. *)
Theorem critical_higher_common_flat_cover (R:realType) m d
    (Z:G (R_n R m) d) mu k (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C:set (R_n R m)) (p:euclidean_projection_space R m mu) g:
  (1<=k)%N ->critical_manifold_family Z mu k.+1 S ->
  is_critical_manifold_chart k.+1 (grassmann_val Z) S p g ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  (forall B:set (R_n R m),critical_manifold_family Z mu k S ->
    @is_relatively_closed_source (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) S B ->
    exists T G,is_critical_flat_cover hNY Z mu S B k T G) ->
  exists T G:nat->set (R_n R m),
    (forall j,is_critical_flat_piece hNY Z mu S C k.+1 (T j) (G j)) /\
    critical_common_tangent_zero_set hNY (grassmann_val Z) S C k.+1=\bigcup_j G j.
Proof.
move=>hk hFamily hChart hCS hC hInduction.
pose X:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)).
pose B:=critical_common_tangent_zero_set hNY (grassmann_val Z) S C k.+1.
have hPositive:(1<=k.+1)%N by [].
have hB:@compact X B:=@critical_common_zero_chart_compact R m mu k.+1 Y NY hNY
  (grassmann_val Z) S C p g hPositive hChart hCS hC.
have hBS:B `<=` S by move=>x hx;exact:hCS x hx.1.
have hClosed:@is_relatively_closed_source X S B.
  exists B;split;first exact:(compact_closed (@metric_hausdorff R X) hB).
  apply/seteqP;split;[by move=>x hx;split;first exact:hBS x hx|by move=>x [_ hx]].
have hFamilyLower:=@critical_manifold_family_lower_class R m d Z mu k.+1 k S
  hk (leqnSn k) hFamily.
have [T [G hCover]]:=hInduction B hFamilyLower hClosed.
exists T,G;split;last exact:(critical_flat_cover_union hCover).
move=>j;exact:(critical_higher_common_flat_piece hChart (critical_flat_cover_pieces hCover j)).
Qed.
