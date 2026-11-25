(** Federer (1969), 3.4.12, p. 339: actual unitary
    pullback transports an original vanishing ideal to the ideal
    of the inverse-image set. Apply the existing representative
    pullback laws and actual unitary inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm LinearBasis
  NormDifferentialUP NormBoundedLinearTopology UnitaryGroup UnitaryComplexMapSealed UnitaryComplexInverse
  HolomorphicLinear HolomorphicGermRing HolomorphicGermVanishingSealed SetGermUP
  HolomorphicUnitaryPullback HolomorphicRotatedGermIdeal HolomorphicPullbackVanishingIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Rotation.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Variable N:nat.
Variable e:'I_N->XR.
Variable he:is_basis e.
Local Notation U:=(@unitary_group R X H hH N e he).
Local Notation NX:=(inner_norm (hermitian_real_inner_product hH)).
Local Notation hNX:=(complex_norm_real (hermitian_complex_norm hH)).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
(** Source for [holomorphic_rotated_vanishing_ideal]: the original
    vanishing-ideal property transfers through the actual unitary
    coordinate change, extending 3.4.8(10), pp. 332–333, under
    3.4.12, p. 339. Every representative is retained. *)
Theorem holomorphic_rotated_vanishing_ideal (g:U) (S:set X):
  @holomorphic_rotated_germ_ideal R X H hH N e he
    (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 S)) g =
  @HolomorphicSetIdeal.value R X NX hNX 0
    (@set_germ T 0 ((@UnitaryComplexMap.value R X H hH N e he g) @^-1` S)).
Proof.
pose u:=@UnitaryComplexMap.value R X H hH N e he g.
pose M:=@holomorphic_unitary_germ_map R X H hH N e he g.
have [h [hLeft hRight]]:=@unitary_complex_inverse_exists R X H hH N e he g.
pose v:=@UnitaryComplexMap.value R X H hH N e he h.
have hBound (q:U):@norm_bounded_linear R XR XR NX NX
    (complex_hom_real (@UnitaryComplexMap.value R X H hH N e he q)).
  exists 1;split;first exact:ler01.
  move=>x;rewrite complex_hom_real_values (@UnitaryComplexMap.laws R X H hH N e he)
    (@unitary_element_norm R X H hH N e he) mul1r;exact:lexx.
have hU:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX (complex_hom_real u) (hBound g).
have hV:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX (complex_hom_real v) (hBound h).
have hTransport:=@holomorphic_pullback_vanishing_ideal_membership R X NX hNX 0 u v M
  (@holomorphic_unitary_germ_map_specification R X H hH N e he g)
  hU hV (linear0 u) (linear0 v) hLeft hRight S.
pose I:=@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 S).
apply/seteqP;split=>beta.
- move/(@holomorphic_rotated_germ_ideal_membership R X H hH N e he I g beta)=>[alpha [hAlpha hMap]].
  rewrite -hMap;exact:(hTransport alpha).1 hAlpha.
- move=>hBeta.
  have [alpha hMap]:=@holomorphic_unitary_germ_map_onto R X H hH N e he g beta.
  apply/(@holomorphic_rotated_germ_ideal_membership R X H hH N e he I g beta).
  exists alpha;split;last exact:hMap.
  apply:(hTransport alpha).2;by rewrite hMap.
Qed.
End Rotation.
