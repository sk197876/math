(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: projected volume is subadditive in one scalar row
    when all the other rows remain fixed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerConvex ScalarConvexLength EuclideanAffineImageGeometry EuclideanCoordinateSplit
  EuclideanLebesgueDimensions EuclideanHeadSectionIntegral EuclideanScalarSplitImages
  LebesgueScalarMeasure CountablyMeasurableUP ProductMeasure ProductSections FibredScalarImageSection FibredScalarImageSumVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_linear_image_head_sum_volume]: expanded
    support for exponent continuity in Federer 3.2.45, p. 279.
    Fubini, 2.6.2(3), p. 115, and the existing scalar convex
    length law prove subadditivity in the first row. Compactness
    supplies every measurability and finite-fibre hypothesis. No
    rank, positive volume or nonempty interior is required. *)
Theorem convex_linear_image_head_sum_volume (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (F G H : {linear R_n R n -> R_n R m.+1}) :
  compact K -> is_inner_convex K ->
  (forall x, coordinate_tail (G x) = coordinate_tail (F x)) ->
  (forall x, coordinate_tail (H x) = coordinate_tail (F x)) ->
  (forall x, coordinate_head (H x) = (coordinate_head (F x)+coordinate_head (G x))%R) ->
  @euclidean_lebesgue_measure R m.+1 (H @` K) <=
    euclidean_lebesgue_measure m.+1 (F @` K) + euclidean_lebesgue_measure m.+1 (G @` K).
Proof.
move=> hKCompact hKConvex hTailG hTailH hHead.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose b := linear_comp (GRing.Linear.clone _ _ _ _ (@coordinate_tail R m) _) F.
pose f := linear_comp (GRing.Linear.clone _ _ _ _ (@coordinate_head R m) _) F.
pose g := linear_comp (GRing.Linear.clone _ _ _ _ (@coordinate_head R m) _) G.
pose C := fun u : X -> R => (fun x => (b x,u x)) @` K.
pose nu := product_measure (euclidean_lebesgue_is_measure R m) (lebesgue_scalar_is_measure R).
have hCompact (L : {linear R_n R n -> R_n R m.+1}) :
    @compact [the topologicalType of inner_metric_space (@euclidean_inner_productP R m.+1)] (L @` K).
  have h := @euclidean_affine_hom_compact_image R n m.+1 (hom_of_linear L)
    (0%R : inner_metric_space (@euclidean_inner_productP R m.+1)) K hKCompact.
  have hFunction : (fun x : X => 0 + hom_of_linear L x)%R = (L : X -> _).
    apply: funext=> x; by rewrite hom_of_linearE add0r.
  by rewrite hFunction in h.
have hImage (L : {linear R_n R n -> R_n R m.+1}) (u : X -> R) :
    (forall x, (b x,u x) = euclidean_split (L x)) ->
    C u = (@euclidean_split R m) @` (L @` K).
  move=> hCoordinates; rewrite image_comp.
  congr (_ @` K); apply: funext=> x; exact: hCoordinates.
have hCF : C f = (@euclidean_split R m) @` (F @` K).
  apply: hImage=> x; by [].
have hCG : C g = (@euclidean_split R m) @` (G @` K).
  apply: hImage=> x; by rewrite /euclidean_split hTailG.
have hCS : C (fun x => (f x+g x)%R) = (@euclidean_split R m) @` (H @` K).
  apply: hImage=> x; by rewrite /euclidean_split hTailH hHead.
have hSource y : is_inner_convex [set x : R_n R n | K x /\ b x=y].
  move=> x z [hx hX] [hz hZ] t ht0 ht1; split.
  - exact: hKConvex x z hx hz t ht0 ht1.
  - by rewrite linearD !linearZ hX hZ -scalerDl subrK scale1r.
have hFConvex y : @is_inner_convex R R^o (f @` [set x | K x /\ b x=y]).
  exact: linear_image_inner_convex (hSource y).
have hGConvex y : @is_inner_convex R R^o (g @` [set x | K x /\ b x=y]).
  exact: linear_image_inner_convex (hSource y).
have hFCount : measure_countably_measurable nu (C f).
  rewrite hCF; exact: euclidean_scalar_split_compact_countably_measurable (hCompact F).
have hGCount : measure_countably_measurable nu (C g).
  rewrite hCG; exact: euclidean_scalar_split_compact_countably_measurable (hCompact G).
have hSCount : measure_countably_measurable nu (C (fun x => (f x+g x)%R)).
  rewrite hCS; exact: euclidean_scalar_split_compact_countably_measurable (hCompact H).
have hFFinite y : lebesgue_scalar_measure (f @` [set x | K x /\ b x=y]) < +oo.
  rewrite -fibred_scalar_image_vertical_section -/(C f) hCF.
  exact: (@euclidean_scalar_split_compact_fibre_finite R m (F @` K) (hCompact F) y).
have hGFinite y : lebesgue_scalar_measure (g @` [set x | K x /\ b x=y]) < +oo.
  rewrite -fibred_scalar_image_vertical_section -/(C g) hCG.
  exact: (@euclidean_scalar_split_compact_fibre_finite R m (G @` K) (hCompact G) y).
have h := @fibred_scalar_image_sum_volume_bound R [the choiceType of X] [the choiceType of Y]
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) K b f g
  hFCount hGCount hSCount hFConvex hGConvex hFFinite hGFinite.
by rewrite -/(C f) -/(C g) -/(C (fun x => (f x+g x)%R))
  hCF hCG hCS !euclidean_scalar_split_image_mass in h.
Qed.
