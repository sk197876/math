(** Federer (1969), 3.2.28, pp. 265–267:
    actual compact Stiefel and Grassmann manifolds satisfy
    the measurable finite-mass rectifiability prerequisites
    of the area and coarea theorems. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerMetric OrthogonalMaps ExteriorGrading ExteriorNorm InnerExteriorPositivity AssociatedSubspace
  SymmetricGrading InnerSymmetric InnerSymmetricPositivity EuclideanHomInnerCharts
  EuclideanStiefelSmooth EuclideanStiefelCompact EuclideanOrientedGrassmannSmooth
  EuclideanGrassmannSquare EuclideanGrassmannCompact FiniteInnerSmoothSubmanifoldUP
  FiniteInnerCompactSubmanifold RectifiableSetUP HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stiefel_measure_rectifiable]: the
    actual measurable finite (H^d,d) rectifiability of
    O(n,m), supporting Federer 3.2.28(2),(3),
    pp. 265–266. Finiteness and measurability
    are derived from the proved compact smooth manifold. *)
Theorem euclidean_stiefel_measure_rectifiable (R:realType) m n:
  let X:=inner_metric_space (@euclidean_hom_inner_productP R m n) in
  let d:=(m*(2*n-m-1)%/2)%N in
  let O:set X:=[set g|is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g)] in
  is_measure_m_rectifiable (@hausdorff_measure R X d) d O /\
  measure_measurable (@hausdorff_measure R X d) O.
Proof.
move=>X d O; split.
- apply:(@finite_inner_compact_submanifold_measure_rectifiable R _ _
    (@euclidean_hom_inner_productP R m n) d 1 O O (leqnn 1)).
  + exact:inner_smooth_submanifold_class (@euclidean_stiefel_smooth_submanifold R m n) 1%N.
  + exact:subset_refl.
  + exact:euclidean_stiefel_compact.
- apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X d)
    (@hausdorff_measure_borel_regular R X d)).
  apply:closed_borel_set.
  exact:(compact_closed (@metric_hausdorff R X) (@euclidean_stiefel_compact R m n)).
Qed.

Section GrassmannMeasures.
Variable R:realType.
Variables m n:nat.
Local Notation E:=(exterior_power (R_n R n) m).
Local Notation hE:=(@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).
Local Notation GO:=[set x:E|simple x /\exterior_norm (euclidean_two_nonzero R)
  (@euclidean_inner_productP R n) x= 1].
Local Notation d:=(m*(n-m))%N.

(** Source for [euclidean_oriented_grassmann_measure_rectifiable]:
    the actual oriented Grassmann target has measurable
    finite H^d mass, Federer 3.2.28(2), p. 265.
    Both properties follow from compactness and the
    smooth manifold theorem, without a volume premise. *)
Theorem euclidean_oriented_grassmann_measure_rectifiable:
  (0<m)%N ->(m<=n)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hE) d) d GO /\
  measure_measurable (@hausdorff_measure R (inner_metric_space hE) d) GO.
Proof.
move=>hm hmn; split.
- apply:(@finite_inner_compact_submanifold_measure_rectifiable R E _ hE d 1 GO GO (leqnn 1)).
  + exact:inner_smooth_submanifold_class
      (@euclidean_oriented_grassmann_smooth_submanifold R m n hm hmn) 1%N.
  + exact:subset_refl.
  + exact:euclidean_oriented_grassmann_compact hm.
- apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R (inner_metric_space hE) d)
    (@hausdorff_measure_borel_regular R (inner_metric_space hE) d)).
  apply:closed_borel_set.
  exact:(compact_closed (@metric_hausdorff R (inner_metric_space hE))
    (@euclidean_oriented_grassmann_compact R m n hm)).
Qed.

(** Source for [euclidean_grassmann_measure_rectifiable]:
    the actual unoriented square Grassmann realization
    has measurable finite H^d mass, supporting Federer
    3.2.28(4), p. 267. The printed positive
    degree and m<=n range are retained. *)
Theorem euclidean_grassmann_measure_rectifiable:
  (0<m)%N ->(m<=n)%N ->
  let Y:=inner_metric_space (@symmetric_inner_productP R E _ hE 2) in
  is_measure_m_rectifiable (@hausdorff_measure R Y d) d (@euclidean_grassmann_square_set R n m) /\
  measure_measurable (@hausdorff_measure R Y d) (@euclidean_grassmann_square_set R n m).
Proof.
move=>hm hmn Y; split.
- apply:(@finite_inner_compact_submanifold_measure_rectifiable R _ _
    (@symmetric_inner_productP R E _ hE 2) d 1
    (@euclidean_grassmann_square_set R n m) (@euclidean_grassmann_square_set R n m) (leqnn 1)).
  + exact:inner_smooth_submanifold_class (@euclidean_grassmann_smooth_submanifold R n m hm hmn) 1%N.
  + exact:subset_refl.
  + exact:euclidean_grassmann_compact hm.
- apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R Y d)
    (@hausdorff_measure_borel_regular R Y d)).
  apply:closed_borel_set.
  exact:(compact_closed (@metric_hausdorff R Y) (@euclidean_grassmann_compact R m n hm)).
Qed.
End GrassmannMeasures.
