(** Federer (1969), 3.2.18, p. 255:
    combine 3.2.4 and 3.2.2 to cover
    a global Lipschitz image, up to
    Hausdorff null mass, by the Borel
    images of its near-isometric pieces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  Hom NormMetric NormMetricScaleContinuity LipschitzUP EuclideanLipschitzClassZero
  EuclideanLebesgueDimensions MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic
  HausdorffMeasure BorelAreaSelection InjectiveDifferentialPieceUP InjectiveDifferentialCover
  InnerOwnNormTopology TopologicalBorel InjectiveBorelImage
  EuclideanMetricCompleteness EuclideanMetricSeparability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_injective_piece_image_cover]:
    the combination of the null image
    deficit in 3.2.4 with the
    near-isometric cover in 3.2.2, as
    invoked in Federer 3.2.18, p. 255.
    The parameter set is the whole space
    and may have infinite source mass. *)
Theorem euclidean_injective_piece_image_cover (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (lambda : R) :
  is_metric_lipschitz setT f -> 1<lambda ->
  exists G, is_injective_differential_cover f lambda G /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
      ((f @` setT) `\` (\bigcup_(E in G) f @` E))=0%E.
Proof.
move=> hLip hLam.
have [B [_ [hB [_ hNull]]]] := euclidean_borel_area_selection hLip
  (measure_measurable_whole (euclidean_lebesgue_is_measure R m)).
have [G hG] := injective_differential_borel_cover_exists
  (euclidean_lipschitz_norm_class_zero hLip) hLam.
exists G; split=> //.
apply: (@measure_null_subset R (inner_metric_space (@euclidean_inner_productP R n))
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
  (@hausdorff_measure_is_measure R _ m) _ _ _ hNull).
move=> y [hy hNot]; split; first exact hy.
move=> [x hx hxy].
have hxL : injective_differential_locus f x.
  rewrite -positive_jacobian_injective_locus; exact (hB x hx).2.
rewrite -hG.2.1 in hxL; have [E hE hxE] := hxL.
apply: hNot; exists E=> //; by exists x.
Qed.

(** Source for [euclidean_injective_piece_image_borel]:
    Borel image pieces in the use of
    3.2.2 and 3.2.4 within Federer
    3.2.18, p. 255. The original
    map is continuous and univalent on
    the actual Borel source piece. *)
Lemma euclidean_injective_piece_image_borel (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (lambda : R)
    (E : set (R_n R m)) :
  is_metric_lipschitz setT f -> is_injective_differential_piece f lambda E ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) (f @` E).
Proof.
move=> [M [hM hBound]] hPiece.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
have hCont : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R X Y f M (ltW hM)).
  by move=> x y; exact: hBound.2 x y I I.
have hBorel : @borel_set X E.
  exact: (inner_own_norm_borel_iff (@euclidean_inner_productP R m) E).2 hPiece.1.
have hInj x y (hx : E x) (hy : E y) (heq : f x=f y) : x=y.
  exact: (hPiece.2.2.1 x y (mem_set hx) (mem_set hy) heq).
exact: (@injective_borel_image_borel R X Y f E (@euclidean_metric_complete R m)
  (@euclidean_metric_separable R m) (@metric_hausdorff R Y) hCont hBorel hInj).
Qed.
