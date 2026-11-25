(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    independent laws for the original regular part,
    retaining the original ambient domain and dimension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric HolomorphicSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_regular_locus]: the regular
    part in 3.4.10, p. 337, consists
    exactly of points with a genuine m-dimensional
    holomorphic manifold neighbourhood in the original domain. *)
Definition is_holomorphic_regular_locus (R:realType) n m
    (U S L:set (coordinate_space (ComplexScalars.C R) n)):Prop:=
  forall a,L a <->S a /\exists V:set (coordinate_space (ComplexScalars.C R) n),
    @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) V /\
    V a /\V `<=` U /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) m (S `&` V).
