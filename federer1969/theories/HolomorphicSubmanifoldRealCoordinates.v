(** Federer (1969), 3.4.12, p. 339: the original
    complex m-manifold is a real 2m-dimensional analytic manifold
    in the actual paired Euclidean coordinates. The complex
    and real dimensions are compared through original charts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  StandardHermitianCoordinates ComplexEuclideanCoordinates ComplexEuclideanCoordinateTopology
  HolomorphicCoordinateNorm HolomorphicSubmanifoldUP HolomorphicSubmanifoldReal NormAnalyticSubmanifoldUP
  NormAnalyticSubmanifoldLinearCoordinates AnalyticSubmanifoldUP FunctionalHolomorphicSubmanifoldUP FunctionalHolomorphicManifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_submanifold_paired_real_coordinates]: the
    first paragraph of 3.4.12, p. 339. Real dimension equals
    twice complex dimension; the exact original paired-coordinate
    inverse is used, including dimension zero. *)
Theorem holomorphic_submanifold_paired_real_coordinates (R:realType) n m
    (S:set (coordinate_space (ComplexScalars.C R) n)):
  @is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n)
    (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) m S ->
  @is_euclidean_analytic_submanifold R (n+n) (m+m)
    ((@complex_from_real_coordinate_hom R n) @^-1` S).
Proof.
move=>hS.
have hReal:=holomorphic_submanifold_real hS.
have hCoordinates:=@norm_analytic_submanifold_linear_coordinates R
  (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n))
  (R_n R (n+n)) (@holomorphic_coordinate_norm R n) (inner_norm (@euclidean_inner_productP R (n+n)))
  (complex_norm_real (@holomorphic_coordinate_norm_laws R n))
  (inner_norm_real_norm (@euclidean_inner_productP R (n+n)))
  (@complex_real_coordinate_hom R n) (@complex_from_real_coordinate_hom R n)
  (n+n) (@coordinate_basis R (n+n)) (@coordinate_basisP R (n+n)) (m+m) S
  (@complex_real_coordinate_hom_bounded R n) (@complex_from_real_coordinate_hom_bounded R n)
  (@complex_real_coordinatesK R n) (@complex_from_real_coordinatesK R n) hReal.
exact:(@norm_analytic_euclidean_submanifold R (n+n) (m+m)
  ((@complex_from_real_coordinate_hom R n) @^-1` S)).1 hCoordinates.
Qed.
(** Source for [functional_holomorphic_paired_real_coordinates]: the
    original functional holomorphic m-manifold has real dimension 2m,
    extending 3.4.5, p. 321, under 3.4.12, p. 339.
    Its independent complex equations supply the proved original charts. *)
Theorem functional_holomorphic_paired_real_coordinates (R:realType) n m
    (U S:set (coordinate_space (ComplexScalars.C R) n)):
  @is_functional_holomorphic_submanifold R n m U S ->
  @is_euclidean_analytic_submanifold R (n+n) (m+m)
    ((@complex_from_real_coordinate_hom R n) @^-1` S).
Proof. move=>h;exact:holomorphic_submanifold_paired_real_coordinates (functional_holomorphic_submanifold_holomorphic h). Qed.
