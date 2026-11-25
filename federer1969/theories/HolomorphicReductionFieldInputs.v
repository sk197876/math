(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    pp. 329–330: the actual complex coordinate quotient is integral
    over its original prefix, its fraction extension is finite,
    and the original suffix classes generate it. Reuse the
    existing finite-module, integrality and fraction-field arguments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP LinearBasis FiniteCoordinates
  HolomorphicCoordinateNorm HolomorphicGermRing HolomorphicGermNoetherian HolomorphicPrefixGermMap
  HolomorphicCoordinateGermsSealed HolomorphicCoordinateSubringFamilySealed HolomorphicReductionLociUP
  HolomorphicReductionFiniteQuotient HolomorphicReductionCoordinateGeneration CommutativeIdealUP CommutativeQuotientUP
  CommutativeSubringUP RingScalarRestriction RingSubmoduleUP IntegralRingElementUP NoetherianFiniteAlgebraIntegrality
  FractionFieldUP CoefficientFractionFieldUP FiniteFractionFieldModule FractionFieldCoordinateGenerators
  GeneratedRingTailEnumeration OrdinalCoordinateTail HolomorphicScalarsSealed CommutativePolynomialSealed
  StandardHermitianCoordinates FiniteFieldPrimitiveComplexDirectionsNull GrassmannAbbreviations EuclideanInnerProduct
  EuclideanLebesgueDimensions InnerNorm InnerMetric HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Fields.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Variable I:set G.
Variable hI:is_commutative_ideal I.
Variable hProper:~I 1.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Variable hPi:is_commutative_ideal_quotient I pi.
Variable m:nat.
Variable hMN:(m<=n)%N.
Variable hAllB:forall j:'I_n,(m<=j)%N ->exists alpha,I alpha /\
  @HolomorphicCoordinateSubringFamily.value R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 alpha /\
  has_nonzero_holomorphic_directional_jet hNX alpha (e j).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m) (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)].
Local Notation E:=(@holomorphic_prefix_germ_map R X NX (complex_norm_real hNX) n e he omega m hMN).
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o E) _).
Local Notation gamma:=(fun i:'I_n=>@HolomorphicCoordinateGerms.value R X NX hNX n e he omega i).
Local Notation suffix:=(fun i:'I_(n-m)=>pi (gamma (ordinal_coordinate_tail_index hMN i))).

(** Source for [holomorphic_reduction_quotient_integral]: the original
    quotient is integral over its original prefix image,
    3.4.12, p. 339. *)
Theorem holomorphic_reduction_quotient_integral:forall c:C,is_integral_ring_element scalar c.
Proof.
have hFinite:=@holomorphic_reduction_finite_original_quotient R X NX hNX n e he omega hDual
  I C pi m hMN hI hProper hPi hAllB.
have hNoetherian:=@finite_holomorphic_germ_ring_noetherian R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m) (@holomorphic_coordinate_norm_laws R m) m
  (@coordinate_basis (ComplexScalars.C R) m) 0 (@coordinate_basisP (ComplexScalars.C R) m).
exact:(@noetherian_finite_algebra_integral A C scalar hNoetherian hFinite).
Qed.

Variable L:fieldType.
Variable inclusion:{rmorphism C->L}.
Variable hFraction:is_commutative_fraction_field inclusion.
Variable M:fieldType.
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Variable hCoefficient:is_coefficient_fraction_field (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi.

(** Source for [holomorphic_reduction_fraction_field_finite]: the actual
    original fraction field is finite over its original prefix field,
    3.4.12, p. 339. *)
Theorem holomorphic_reduction_fraction_field_finite:
  is_finitely_generated_ring_submodule (setT:set [the lmodType M of ring_restricted_space phi L^o]).
Proof.
have hFinite:=@holomorphic_reduction_finite_original_quotient R X NX hNX n e he omega hDual
  I C pi m hMN hI hProper hPi hAllB.
apply:(@finite_algebra_fraction_field_module A C M L scalar inclusion eta phi hFraction _ hFinite).
exact:coefficient_fraction_scalar_triangle hCoefficient.
Qed.

(** Source for [holomorphic_reduction_fraction_coordinate_generators]:
    the original remaining coordinate classes generate the fraction
    extension, 3.4.12, p. 339. *)
Theorem holomorphic_reduction_fraction_coordinate_generators:
  is_generated_commutative_subring
    (fun y:L=>(exists i:'I_(n-m),y=inclusion (suffix i)) \/exists a:M,y=phi a) setT.
Proof.
have hOriginal:=@holomorphic_reduction_original_coordinate_generators R X NX hNX n e he omega hDual
  I C pi m hMN hI hProper hPi hAllB.
have hIndexed:=@generated_ring_tail_enumeration C n (fun j=>pi (gamma j)) m hMN
  (fun y:C=>exists a:A,y=scalar a) hOriginal.
apply:(@fraction_field_original_coordinate_generators A C M L scalar inclusion eta phi
  (n-m)%N suffix hFraction _ holomorphic_reduction_fraction_field_finite hIndexed).
exact:coefficient_fraction_scalar_triangle hCoefficient.
Qed.

(** Source for [holomorphic_reduction_primitive_suffix_nullity]: both
    original complex primitive-direction nullities for the actual
    quotient and its original suffix, 3.4.12, p. 339.
    The paired real coordinate chart has dimension 2(n-m). *)
Theorem holomorphic_reduction_primitive_suffix_nullity:
  let complexScalar:=GRing.RMorphism.clone (ComplexScalars.C R) M (eta \o
    (@HolomorphicScalars.map R (coordinate_space (ComplexScalars.C R) m)
      (@holomorphic_coordinate_norm R m) (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)) _ in
  let bad:=fun v:R_n R ((n-m)+(n-m))=>~is_generated_commutative_subring
    (fun y:L=>y=\sum_i phi (complexScalar ((complex_from_real_coordinates v) i))*inclusion (suffix i) \/
      exists a:M,y=phi a) setT in
  @euclidean_lebesgue_measure R ((n-m)+(n-m)) bad=0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((n-m)+(n-m)))) ((n-m)+(n-m)-1)
    [set v|bad v /\inner_norm (@euclidean_inner_productP R ((n-m)+(n-m))) v= 1]=0%:E.
Proof.
move=>complexScalar bad.
exact:(@finite_field_primitive_complex_directions_null R M L complexScalar phi (n-m)%N
  (fun i=>inclusion (suffix i)) (CommutativePolynomial.space M) (CommutativePolynomial.embed M)
  (CommutativePolynomial.variable M) (@CommutativePolynomial.coefficient M) (CommutativePolynomial.laws M)
  holomorphic_reduction_fraction_field_finite holomorphic_reduction_fraction_coordinate_generators).
Qed.
End Fields.
