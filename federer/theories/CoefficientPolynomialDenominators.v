(** Federer (1969), 3.4.8(8), p. 330:
    polynomial coefficients in the original M
    admit an original common denominator with
    nonzero image. Reuse polynomial denominator
    clearing on the faithful image, then
    lift through the original surjective coefficient map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringRealisationSealed CommutativeQuotientUP CommutativeRingImageQuotient
  CommutativePolynomialUP CommutativePolynomialSealed PolynomialCoefficientMapUP
  PolynomialCoefficientMapSealed PolynomialCoefficientDivision PolynomialClearDenominators
  PolynomialCoefficientSurjection CoefficientFractionFieldUP CoefficientImageFractionField.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [coefficient_polynomial_original_denominator]:
    the original coefficient polynomial over M
    becomes an original Q_m polynomial after
    multiplication by an original coefficient whose
    image is nonzero, 3.4.8(8), p. 330.
    The original Q_m map may have a
    kernel; only its faithful image is
    supplied to the existing fraction theorem. *)
Theorem coefficient_polynomial_original_denominator (A B:comNzRingType) (L M:fieldType) (P:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedM:{rmorphism M->P}) (variableM:P) (target:P->nat->M)
  (hA:is_commutative_polynomial_ring embedA variableA source)
  (hM:is_commutative_polynomial_ring embedM variableM target)
  (original:{rmorphism A->L}) (eta:{rmorphism A->M}) (phi:{rmorphism M->L})
  (map:{rmorphism B->P}):
  is_coefficient_fraction_field original eta phi ->
  is_polynomial_coefficient_map source target eta map ->forall H:P,
  exists (delta:A) (G:B),eta delta<>0 /\map G = embedM (eta delta)*H.
Proof.
move=>hCoefficient hMap H.
pose S:set M:=fun y=>exists a:A,y = eta a.
have hS:is_commutative_subring S:=commutative_ring_image_subring eta.
pose D:=@CommutativeSubringRealisation.space M S hS.
pose inclusion:=@CommutativeSubringRealisation.inclusion M S hS.
have hImage:=@CommutativeSubringRealisation.laws M S hS.
have [rho [hRho hQuotient]]:=@commutative_ring_image_quotient A M D eta inclusion hImage.
have hField:=@coefficient_image_fraction_field A D L M original eta phi inclusion hCoefficient hImage.
have hDomain:=@subring_realisation_field_domain D M S inclusion hImage.
pose PD:=CommutativePolynomial.space D.
pose embedD:=CommutativePolynomial.embed D.
pose variableD:=CommutativePolynomial.variable D.
pose coefficientD:=@CommutativePolynomial.coefficient D.
have hD:=CommutativePolynomial.laws D.
pose middle:=@PolynomialCoefficientMap.map A B D PD embedA variableA source
  embedD variableD coefficientD hA hD rho.
have hMiddle:=@PolynomialCoefficientMap.laws A B D PD embedA variableA source
  embedD variableD coefficientD hA hD rho.
pose outer:=@PolynomialCoefficientMap.map D PD M P embedD variableD coefficientD
  embedM variableM target hD hM inclusion.
have hOuter:=@PolynomialCoefficientMap.laws D PD M P embedD variableD coefficientD
  embedM variableM target hD hM inclusion.
have [d [G [hNonzero hG]]]:=@polynomial_clear_denominators D PD M P
  embedD variableD coefficientD embedM variableM target hD hM inclusion hField hDomain outer hOuter H.
have [delta hDelta]:=commutative_quotient_surjective hQuotient d.
have [G0 hG0]:=@polynomial_coefficient_map_surjective A B D PD embedA variableA source
  embedD variableD coefficientD hA hD rho middle (commutative_quotient_surjective hQuotient) hMiddle G.
have hComposition Q:map Q = outer (middle Q).
  apply:(@polynomial_coefficients_unique M P embedM variableM target hM)=>i.
  by rewrite hMap hOuter hMiddle hRho.
exists delta,G0;split.
- move=>hZero;apply:hNonzero;apply:(commutative_subring_inclusion_injective hImage).
  by rewrite -hDelta hRho hZero rmorph0.
- by rewrite hComposition hG0 hG -hDelta hRho.
Qed.
