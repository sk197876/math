(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.9, p. 337:
    the whole-space regression uses its actual vanishing
    ideal. Connect the existing local-vanishing and local
    equality laws of 3.4.5, pp. 319–320. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicGermArithmeticRepresentatives ScalarRestriction ComplexScalarSealed RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRing HolomorphicGermRingLaws LocalGermUP LocalGermSealed SetGermUP
  CommutativeIdealUP HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative HolomorphicGermVanishingIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_whole_germ_ideal_zero]: the original
    whole-space ideal is the zero ideal, connecting
    the original depth convention of 3.4.8(2), p. 326,
    to the full-dimensional 3.4.9 regression. The proof
    applies the existing representative laws directly. *)
Theorem holomorphic_whole_germ_ideal_zero (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:
  @HolomorphicSetIdeal.value R X NX hNX a
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a setT)=
    [set alpha:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]|alpha=0].
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@holomorphic_representative_type R X NX hNX a.
pose value:=@holomorphic_representative_value R X NX hNX a.
apply/seteqP;split=>alpha.
- have [f <-]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
  move/(holomorphic_set_ideal_representative_equation f setT)=>[U [hU [ha hZero]]].
  change (holomorphic_germ f=holomorphic_germ (@holomorphic_constant_representative R X NX hNX a 0)).
  apply/(local_germ_equality (@LocalGerms.laws T (ComplexScalars.C R) P value a)).
  exists U;split;first exact:hU.
  split;first exact:ha.
  move=>x hx;exact:hZero x Logic.I hx.
- move=>->;exact:commutative_ideal_zero (holomorphic_set_ideal_ring_laws _).
Qed.
