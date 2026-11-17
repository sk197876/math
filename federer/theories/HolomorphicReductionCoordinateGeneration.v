(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 329: the original whole holomorphic quotient is generated
    by its original complex prefix and suffix coordinates. Apply the field-independent
    tower assembly to actual adjacent quotient-image steps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP LinearBasis
  FiniteCoordinates HolomorphicCoordinateNorm HolomorphicGermRing HolomorphicPrefixGermMap
  HolomorphicCoordinateGermsSealed HolomorphicFullPrefixGerms HolomorphicCoordinateSubringFamilySealed HolomorphicReductionLociUP
  HolomorphicReductionPrefixImageStep CommutativeIdealUP CommutativeQuotientUP
  CommutativeSubringUP CommutativeSubringRealisationUP RingScalarRestriction RingSubmoduleUP GeneratedPrefixTowerCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_reduction_original_coordinate_generators]: the
    actual original quotient retains its original coordinate generators, 3.4.12,
    p. 339. The directional witnesses are exactly the original
    B-tail tests. No faithful coefficient action or finite
    quotient conclusion is supplied as an additional premise. *)
Theorem holomorphic_reduction_original_coordinate_generators (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X (ComplexScalars.C R)^o)
    (hDual:forall i k,omega i (e k)=if i==k then 1 else 0)
    (I:set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)) (C:comNzRingType)
    (pi:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)]->C})
    m (hMN:(m<=n)%N):
  is_commutative_ideal I ->~I 1 ->is_commutative_ideal_quotient I pi ->
  (forall j:'I_n,(m<=j)%N ->exists alpha,I alpha /\
    @HolomorphicCoordinateSubringFamily.value R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 alpha /\
    has_nonzero_holomorphic_directional_jet hNX alpha (e j)) ->
  is_generated_commutative_subring
    (fun y:C=>(exists a:@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) m)
      (@holomorphic_coordinate_norm R m) (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0,
      y=pi (@holomorphic_prefix_germ_map R X NX (complex_norm_real hNX) n e he omega m hMN a)) \/
      exists j:'I_n,(m<=j)%N /\y=pi (@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j)) setT.
Proof.
move=>hI hProper hPi hAllB.
pose A:=fun p=>[the comNzRingType of (@holomorphic_germ_ring R
  (coordinate_space (ComplexScalars.C R) p) (@holomorphic_coordinate_norm R p)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R p)) 0)].
pose E:=fun p (hPN:(p<=n)%N)=>@holomorphic_prefix_germ_map R X NX (complex_norm_real hNX) n e he omega p hPN.
pose F:=fun p (hPN:(p<=n)%N)=>GRing.RMorphism.clone (A p) C (pi \o E p hPN) _.
apply:(@generated_prefix_tower_coordinates n m hMN A C F (fun j=>pi (@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j))).
- move=>j hJ D inclusion hImage.
  have [scalar [coordinate [hScalar [hCoordinate [_ hGenerated]]]]]:=
    @holomorphic_reduction_prefix_image_step R X NX hNX n e he omega hDual I hI hProper
      C pi hPi j D inclusion hImage (hAllB j hJ).
  exists scalar,coordinate;split;first exact:hScalar.
  by split;[exact:hCoordinate|exact:hGenerated].
- move=>c;have [alpha hAlpha]:=commutative_quotient_surjective hPi c.
  have [beta hBeta]:=@holomorphic_full_prefix_germ_map_surjective R X NX (complex_norm_real hNX)
    n e he omega hDual alpha.
  exists beta;change (pi (E n (leqnn n) beta)=c).
  by rewrite /E hBeta hAlpha.
Qed.
