(** Federer (1969), 3.2.15, p. 252:
    the full-target-rank part of each fibre is
    countably (m-n) rectifiable, by 3.2.9 and
    the exact inverse-fibre formulas of 3.2.10. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  LipschitzUP EuclideanLipschitzClassZero CoordinateInverseCoverUP CoordinateInverseCover
  CoordinateInverseFibres EuclideanBlockCoordinates EuclideanSliceDifferentials MappingMultiplicity
  RectifiableSetUP RectifiableElementary CountablyRectifiableUnions EuclideanLipschitzRectifiableImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [coordinate_inverse_fibre_countably_rectifiable]:
    the first inference from 3.2.9 and 3.2.10
    in Federer 3.2.15, p. 252. Every target
    point and the exact fibre subset are retained. *)
Lemma coordinate_inverse_fibre_countably_rectifiable (R : realType) m n
    (f : R_n R m -> R_n R n) (E : set (R_n R m)) :
  is_coordinate_inverse_piece f E -> forall y,
  @is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R m))
    (m-n) (mapping_fibre f E y).
Proof.
move=> [_ [p [_ [u [v [hu [hv hmaps]]]]]]] y.
rewrite (coordinate_inverse_fibre_image hmaps y).
apply: euclidean_lipschitz_image_countably_rectifiable.
have [L [hL hBound]] := euclidean_slice_lipschitz hv y.
exists L; split=> //; split; first exact: hBound.1.
move=> x z hx hz; exact: hBound.2 x z I I.
Qed.

(** Source for [full_rank_fibre_countably_rectifiable]:
    P intersect f inverse {y} is countably m-n
    rectifiable for every y, Federer 3.2.15,
    p. 252. The coordinate cover is obtained
    from continuity, proved here from Lipschitzness. *)
Theorem full_rank_fibre_countably_rectifiable (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) :
  is_metric_lipschitz setT f -> forall y,
  @is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R m))
    (m-n) (mapping_fibre f (surjective_differential_locus f) y).
Proof.
move=> hf y.
have [G [hG [hcover hpieces]]] := coordinate_inverse_cover_class_zero
  (euclidean_lipschitz_norm_class_zero hf).
have hUnion : @is_countably_m_rectifiable R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-n)
    (\bigcup_(E in G) mapping_fibre f E y).
  apply: countably_rectifiable_countable_union hG _=> E hE.
  exact: coordinate_inverse_fibre_countably_rectifiable (hpieces E hE) y.
apply: countably_rectifiable_subset _ hUnion=> x [hx hfx].
have [E hE hxE] := hcover x hx; exists E=> //; by split.
Qed.
