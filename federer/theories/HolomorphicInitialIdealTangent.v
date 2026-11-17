(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    the entire original leading ideal lies in the
    actual tangent-cone vanishing ideal. The original generator
    family and the opaque least-ideal law prove this
    inclusion without presupposing an analytic tangent cone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP RealNormUP NormMetric HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRepresentatives SetGermUP HolomorphicGermVanishingUP HolomorphicGermVanishingSealed
  HolomorphicGermVanishingRepresentative HolomorphicGermVanishingIdeal CommutativeIdealUP TangentConeUP
  HolomorphicInitialPolynomialGermUP HolomorphicInitialIdealSealed HolomorphicInitialTangentVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_initial_ideal_tangent_inclusion]:
    the leading ideal is contained in the ideal
    of the actual tangent cone, 3.4.12, p. 339, extending 3.4.11, p. 338.
    This statement uses only original set germs and
    their independently specified vanishing ideals. *)
Theorem holomorphic_initial_ideal_tangent_inclusion (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (S:set X):
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  let I:=@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 S) in
  @HolomorphicInitialIdeal.value R X NX hNX I `<=`
    @HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0)).
Proof.
move=>T I.
apply:(generated_commutative_ideal_minimal (@HolomorphicInitialIdeal.laws R X NX hNX I)
  (@holomorphic_set_ideal_ring_laws R X NX hNX 0 (@set_germ T 0 (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0)))).
move=>beta [alpha [hAlpha [k [P [f [hInitial [hValues <-]]]]]]].
apply/(@holomorphic_set_ideal_representative_equation R X NX hNX 0 f (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0)).
exists setT;split;first exact:openT.
split;first done.
move=>v hTangent _;rewrite hValues.
exact:(@holomorphic_initial_polynomial_tangent_vanishes R X NX hNX S alpha k P hAlpha hInitial v hTangent).
Qed.
