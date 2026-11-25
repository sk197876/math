(** Federer (1969), 3.4.12, p. 339: the original
    condition I equals ideal(var I) survives the actual unitary
    change of coordinates. Reuse the proved vanishing-ideal transport
    and generator-independent ideal/variety recovery. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm LinearBasis UnitaryGroup UnitaryComplexMapSealed
  HolomorphicGermRing HolomorphicGermVanishingSealed HolomorphicIdealVarietyGermSealed
  HolomorphicIdealVarietyVanishingLaws HolomorphicRotatedGermIdeal HolomorphicRotatedVanishingIdeal
  CommutativeIdealUP SetGermUP SetGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [given_holomorphic_vanishing_ideal_variety_recovery]:
    an ideal already arising by original local vanishing equals
    ideal(var I), extending 3.4.5, p. 320, under 3.4.12,
    p. 339. Apply the existing recovery theorem directly. *)
Lemma given_holomorphic_vanishing_ideal_variety_recovery (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])
    (hI:is_finitely_generated_commutative_ideal I)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  I = @HolomorphicSetIdeal.value R X NX hNX a sigma ->
  I = @HolomorphicSetIdeal.value R X NX hNX a (@HolomorphicIdealVarietyGerm.value R X NX hNX a I hI).
Proof.
move=>hEqual;move:hI;rewrite hEqual=>hI.
exact:esym (@vanishing_ideal_variety_recovery R X NX hNX a sigma hI).
Qed.
Section Recovery.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable N:nat.
Variable e:'I_N->restricted_space (ComplexScalars.embed R) X.
Variable he:is_basis e.
Local Notation NX:=(inner_norm (hermitian_real_inner_product hH)).
Local Notation hNX:=(complex_norm_real (hermitian_complex_norm hH)).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
(** Source for [holomorphic_rotated_ideal_variety_recovery]: the
    original recovery hypothesis on I transfers to I_g,
    supporting the nonempty-germ conclusion of 3.4.12, p. 339,
    extending 3.4.8(10), pp. 332–333. No rotated recovery
    hypothesis is added to the original theorem. *)
Theorem holomorphic_rotated_ideal_variety_recovery (I:set G)
    (g:@unitary_group R X H hH N e he)
    (hI:is_finitely_generated_commutative_ideal I)
    (hIg:is_finitely_generated_commutative_ideal (@holomorphic_rotated_germ_ideal R X H hH N e he I g)):
  I = @HolomorphicSetIdeal.value R X NX hNX 0 (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 I hI) ->
  @holomorphic_rotated_germ_ideal R X H hH N e he I g =
    @HolomorphicSetIdeal.value R X NX hNX 0
      (@HolomorphicIdealVarietyGerm.value R X NX hNX 0
        (@holomorphic_rotated_germ_ideal R X H hH N e he I g) hIg).
Proof.
move=>hRecovered.
have [S hS]:=@set_germ_has_representative T 0 (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 I hI).
rewrite -hS in hRecovered.
have hRotated:@holomorphic_rotated_germ_ideal R X H hH N e he I g =
    @HolomorphicSetIdeal.value R X NX hNX 0
      (@set_germ T 0 ((@UnitaryComplexMap.value R X H hH N e he g) @^-1` S)).
  rewrite hRecovered;exact:(@holomorphic_rotated_vanishing_ideal R X H hH N e he g S).
exact:(@given_holomorphic_vanishing_ideal_variety_recovery R X NX hNX 0 _ hIg _ hRotated).
Qed.
End Recovery.
