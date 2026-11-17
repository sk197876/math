(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: the scalar-row Fubini bound holds at every target
    coordinate, by the existing orthogonal volume laws. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanLebesgueDimensions EuclideanCoordinateReindexing ConvexLinearImageHeadSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_linear_image_one_row_sum_volume]: an expanded
    helper for Federer 3.2.45, p. 279. A finite coordinate
    transposition reduces every chosen row to the first-row Fubini
    theorem. All other rows are equal in the three maps. Compact
    convex sources may be empty or have zero volume; the supplied
    row index entails positive target dimension. *)
Theorem convex_linear_image_one_row_sum_volume (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (F G H : {linear R_n R n -> R_n R m.+1}) (i : 'I_m.+1) :
  compact K -> is_inner_convex K ->
  (forall x j, j != i -> G x j = F x j) ->
  (forall x j, j != i -> H x j = F x j) ->
  (forall x, H x i = (F x i+G x i)%R) ->
  @euclidean_lebesgue_measure R m.+1 (H @` K) <=
    euclidean_lebesgue_measure m.+1 (F @` K) + euclidean_lebesgue_measure m.+1 (G @` K).
Proof.
move=> hCompact hConvex hG hH hSum.
pose sigma := tperm (ord0 : 'I_m.+1) i.
have [T hT] := @euclidean_coordinate_reindexing_exists R m.+1 sigma.
have hInjective : injective sigma by exact: perm_inj.
have hTail (j : 'I_m) : sigma (lift ord0 j) != i.
  rewrite -(tpermL (ord0 : 'I_m.+1) i) (inj_eq hInjective).
  by rewrite lift_eqF.
have hTG x : coordinate_tail (linear_comp T G x) = coordinate_tail (linear_comp T F x).
  apply/ffunP=> j; rewrite /coordinate_tail !ffunE !hT.
  exact: hG x _ (hTail j).
have hTH x : coordinate_tail (linear_comp T H x) = coordinate_tail (linear_comp T F x).
  apply/ffunP=> j; rewrite /coordinate_tail !ffunE !hT.
  exact: hH x _ (hTail j).
have hHead x : coordinate_head (linear_comp T H x) =
    (coordinate_head (linear_comp T F x)+coordinate_head (linear_comp T G x))%R.
  by rewrite /coordinate_head !hT /sigma !tpermL hSum.
have h := @convex_linear_image_head_sum_volume R n m K
  (linear_comp T F) (linear_comp T G) (linear_comp T H)
  hCompact hConvex hTG hTH hHead.
have hVolume (L : {linear R_n R n -> R_n R m.+1}) :
    @euclidean_lebesgue_measure R m.+1 ((linear_comp T L) @` K) =
      euclidean_lebesgue_measure m.+1 (L @` K).
  change (euclidean_lebesgue_measure m.+1 ((T \o L) @` K) =
    euclidean_lebesgue_measure m.+1 (L @` K)).
  rewrite -image_comp.
  exact: (@euclidean_coordinate_reindexing_volume R m.+1 sigma T hInjective hT (L @` K)).
by rewrite !hVolume in h.
Qed.
