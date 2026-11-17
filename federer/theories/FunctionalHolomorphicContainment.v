(** Federer (1969), 3.4.5, p. 321,
    used in corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333:
    every functional holomorphic submanifold lies in its
    actual defining domain. The original membership
    equation already includes this containment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FunctionalHolomorphicSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_domain_containment]:
    the domain clause of the original functional
    holomorphic manifold definition, 3.4.5, p. 321,
    retained in the successive-stratum assembly of
    3.4.12, p. 339, extending 3.4.8(11), p. 333. *)
Lemma functional_holomorphic_domain_containment (R:realType) n m (U S:set (coordinate_space (ComplexScalars.C R) n)):
  @is_functional_holomorphic_submanifold R n m U S ->S `<=` U.
Proof.
move=>[_ [_ [f [g [_ [_ [hEquation _]]]]]]] x hx.
exact:((hEquation x).1 hx).1.
Qed.
