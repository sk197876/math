(** Federer (1969), 3.2.28(2),(4), pp. 265,267:
    the actual oriented and unoriented Grassmann realizations
    are compact. This supports their measurable finite-mass
    area/coarea applications, independently of the openness proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerMetric OrthogonalMaps ExteriorGrading ExteriorNorm InnerExterior
  InnerExteriorPositivity AssociatedSubspace SymmetricGrading InnerSymmetric InnerSymmetricPositivity
  EuclideanHomInnerCharts EuclideanStiefelCompact EuclideanExteriorWordSmooth
  EuclideanExteriorWordImage FiniteInnerSmoothCompactImage SymmetricSquareGeometry
  SymmetricSquareSmooth EuclideanGrassmannSquare.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_oriented_grassmann_compact]:
    the compact actual Q-image in Federer 3.2.28(2),
    p. 265, from the compact Stiefel set and
    the proved polynomial Q. Positive m is the
    oriented simple-unit realization in the book. *)
Theorem euclidean_oriented_grassmann_compact (R:realType) m n:
  (0<m)%N ->
  @compact [the topologicalType of inner_metric_space
    (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)]
    [set x|simple x /\exterior_norm (euclidean_two_nonzero R)
      (@euclidean_inner_productP R n) x= 1].
Proof.
move=>hm.
rewrite -(@euclidean_exterior_word_image_simple_unit R m n hm).
exact:(@inner_class_map_compact_image R (Hom (R_n R m) (R_n R n))
  (exterior_power (R_n R n) m) (@euclidean_hom_inner_product R m n)
  (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
  (@euclidean_hom_inner_productP R m n)
  (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
  (@euclidean_exterior_word_map R m n) 0%N _
  (@euclidean_exterior_word_smooth R m n (euclidean_two_nonzero R) 0%N)
  (@euclidean_stiefel_compact R m n)).
Qed.

(** Source for [euclidean_grassmann_compact]: the compact
    square realization of G(n,m), Federer 3.2.28(4),
    p. 267, as the continuous image of the
    actual oriented simple-unit manifold. No quotient
    measure or chosen orientation defines this set. *)
Theorem euclidean_grassmann_compact (R:realType) m n:
  (0<m)%N ->
  @compact [the topologicalType of inner_metric_space
    (@symmetric_inner_productP R (exterior_power (R_n R n) m)
      (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
        (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
      (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
        (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m) 2)]
    (@euclidean_grassmann_square_set R n m).
Proof.
move=>hm.
pose E:=exterior_power (R_n R n) m.
pose B:=@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
pose hB:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
rewrite euclidean_grassmann_square_image.
exact:(@inner_class_map_compact_image R E (symmetric_power E 2) B
  (@symmetric_inner_form R E B hB 2) hB (@symmetric_inner_productP R E B hB 2)
  (@inner_projective_square R E) 0%N _ (@inner_projective_square_smooth R E B hB 0%N)
  (@euclidean_oriented_grassmann_compact R m n hm)).
Qed.
