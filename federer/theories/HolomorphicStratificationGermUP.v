(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333:
    the finite irreducible reduction uses each component
    with every original holomorphic starting set. Keep the
    given actual representative as an existence invariant;
    all resulting strata must lie inside it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP FiniteHolomorphicVarietyUP HolomorphicFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section GermStatement.
Variable R:realType.
Variables n m:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).

(** Source for [holomorphic_stratification_for_germ]:
    the uniform component existence statement in the
    ordered reduction of 3.4.12, p. 339, extending 3.4.8(11), p. 333.
    These independent requirements assume no component
    decomposition or finite-component conclusion. *)
Definition holomorphic_stratification_for_germ (alpha:@set_germ_space T 0):Prop:=
  forall U H U0 S0:set X,U 0 ->@is_finite_holomorphic_variety R X NX hNX U H ->
    @set_germ T 0 H=alpha ->U0 0 ->@is_finite_holomorphic_variety R X NX hNX U0 S0 ->
    exists mu,exists V S G:'I_mu->set X,
      @is_holomorphic_finite_stratification R n alpha (@set_germ T 0 S0) m U0 S0 mu V S G /\
      forall i,S i `<=` H.
End GermStatement.
