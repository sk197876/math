(** Federer (1969), 3.4.12, p. 339: the
    original vanishing subset is an actual ideal of the
    holomorphic germ ring. The proof uses only the sealed
    representative equations and local vanishing laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric GermVanishingUP HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP HolomorphicGermOperationsUP HolomorphicGermSealed
  HolomorphicGermRingLaws HolomorphicGermRing SetGermUP SetGermLaws CommutativeIdealUP
  HolomorphicGermVanishingUP GermVanishingLaws HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Ideal.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:restricted_space (ComplexScalars.embed R) X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Local Notation P:=(@holomorphic_representative_type R X NX hNX a).
Local Notation value:=(@holomorphic_representative_value R X NX hNX a).
Local Notation germ:=(@holomorphic_germ R X NX hNX a).
Local Notation sgerm:=(@set_germ T a).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX a).

(** Source for [holomorphic_set_ideal_ring_laws]: ideal
    gamma_a(S) is an ideal, 3.4.12, p. 339.
    Every representative and neighbourhood required by its
    definition is discharged by the actual functional laws. *)
Theorem holomorphic_set_ideal_ring_laws (sigma:set_germ_space (a:T)):
  @is_commutative_ideal A (ideal sigma).
Proof.
have [S <-]:=@set_germ_has_representative T a sigma.
constructor.
- change (ideal (sgerm S) (@holomorphic_germ_zero R X NX hNX a)).
  apply/(holomorphic_set_ideal_representative_equation _ S).
  exact:(@vanishes_near_zero T [the comNzRingType of (ComplexScalars.C R : Type)] a S).
- move=>alpha beta hAlpha hBeta.
  have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
  have [g hg]:=@holomorphic_germ_has_representative R X NX hNX a beta.
  rewrite -hf -hg in hAlpha hBeta *.
  change (ideal (sgerm S) (@HolomorphicGerms.add R X NX hNX a (germ f) (germ g))).
  rewrite (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
  apply/(holomorphic_set_ideal_representative_equation _ S).
  exact:(@vanishes_near_add T [the comNzRingType of (ComplexScalars.C R : Type)] a S (value f) (value g)
    ((holomorphic_set_ideal_representative_equation f S).1 hAlpha)
    ((holomorphic_set_ideal_representative_equation g S).1 hBeta)).
- move=>alpha hAlpha;have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
  rewrite -hf in hAlpha *.
  change (ideal (sgerm S) (@HolomorphicGerms.opp R X NX hNX a (germ f))).
  rewrite (@holomorphic_germ_negate_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
  apply/(holomorphic_set_ideal_representative_equation _ S).
  exact:(@vanishes_near_opp T [the comNzRingType of (ComplexScalars.C R : Type)] a S (value f)
    ((holomorphic_set_ideal_representative_equation f S).1 hAlpha)).
- move=>alpha beta hBeta.
  have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
  have [g hg]:=@holomorphic_germ_has_representative R X NX hNX a beta.
  rewrite -hf -hg in hBeta *.
  change (ideal (sgerm S) (@HolomorphicGerms.mul R X NX hNX a (germ f) (germ g))).
  rewrite (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
  apply/(holomorphic_set_ideal_representative_equation _ S).
  exact:(@vanishes_near_mul T [the comNzRingType of (ComplexScalars.C R : Type)] a S (value f) (value g)
    ((holomorphic_set_ideal_representative_equation g S).1 hBeta)).
Qed.
End Ideal.
