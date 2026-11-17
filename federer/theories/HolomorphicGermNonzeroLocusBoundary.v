(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), pp. 333–335:
    an original holomorphic inequality gives a functional
    stratum whose relative boundary lies in the
    original zero variety. The actual formula and
    domain are retained; no component bound is assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness HolomorphicUP FunctionalHolomorphicSubmanifoldUP FunctionalHolomorphicFullDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_nonzero_locus_functional_boundary]:
    the original R={y:|y|<epsilon,Phi(y)!=0}
    is a full-dimensional functional holomorphic submanifold;
    its boundary inside the ball lies in Phi=0,
    3.4.12, p. 339, extending 3.4.8(11), p. 333. *)
Theorem holomorphic_nonzero_locus_functional_boundary (R:realType) n (U:set (coordinate_space (ComplexScalars.C R) n))
    (phi:coordinate_space (ComplexScalars.C R) n->ComplexScalars.C R^o):
  @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) U ->
  @is_holomorphic R (coordinate_space (ComplexScalars.C R) n) (ComplexScalars.C R)^o (@holomorphic_coordinate_norm R n)
    (@complex_modulus R) (complex_norm_real (@holomorphic_coordinate_norm_laws R n))
    (@complex_modulus_real_norm R) U phi ->
  @is_functional_holomorphic_submanifold R n n U [set x|U x /\phi x<>0] /\
  U `&` @closure (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n)))
    [set x|U x /\phi x<>0] `<=` [set x|U x /\phi x<>0] `|` [set x|U x /\phi x=0].
Proof.
move=>hU hPhi;split.
- apply/(functional_holomorphic_full_dimension U _);split;first exact:hU.
  exists phi;split;first exact:hPhi.
  by move=>x.
- move=>x [hx _];case:(pselect (phi x=0))=>hZero;[right|left];by split.
Qed.
