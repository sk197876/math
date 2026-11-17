(** Federer (1969), 3.4.8(10), p. 331:
    every germ outside the original prime
    ideal has an inverse represented by
    a bounded original polynomial divided by
    an original coefficient. Apply the already
    proved bounded representative theorem to that inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP CommutativeSubringUP CommutativeQuotientUP
  CommutativePolynomialUP CommutativePolynomialMonicUP CommutativePolynomialEvaluationUP
  FractionFieldUP CoefficientFractionFieldUP PolynomialScalarComposition PrimitiveFieldBoundedRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [primitive_quotient_inverse_original_denominator]:
    sigma times a bounded original polynomial
    equals a nonzero original coefficient modulo
    I_g, 3.4.8(10), p. 331. The
    actual fraction-field inverse and previously
    proved original representatives give this relation. *)
Theorem primitive_quotient_inverse_original_denominator (A P G C:comNzRingType) (L M:fieldType)
  (embed:{rmorphism A->P}) (variable:P) (coefficient:P->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (hDomain:is_commutative_integral_domain A)
  (E:{rmorphism A->G}) (gamma:G) (J:{rmorphism P->G})
  (I:set G) (pi:{rmorphism G->C}) (inclusion:{rmorphism C->L})
  (eta:{rmorphism A->M}) (phi:{rmorphism M->L}) (W:P) k:
  is_commutative_ideal_quotient I pi ->is_commutative_fraction_field inclusion ->
  is_coefficient_fraction_field
    (GRing.RMorphism.clone A L (inclusion \o pi \o E) _) eta phi ->
  is_commutative_polynomial_evaluation embed variable E gamma J ->
  is_generated_commutative_subring
    (fun y:L=>y = inclusion (pi gamma) \/exists a:M,y = phi a) setT ->
  is_monic_polynomial coefficient W k ->I (J W) ->forall sigma:G,~I sigma ->
  exists (delta:A) (T:P),eta delta<>0 /\
    (forall i,(k<=i)%N ->coefficient T i = 0) /\I (sigma*J T-E delta).
Proof.
move=>hPi hFraction hCoefficient hJ hGenerated hW hIn sigma hOutside.
pose scalar:{rmorphism A->C}:=GRing.RMorphism.clone A C (pi \o E) _.
pose chi:{rmorphism A->L}:=GRing.RMorphism.clone A L (inclusion \o scalar) _.
pose EJ:{rmorphism P->C}:=GRing.RMorphism.clone P C (pi \o J) _.
pose EL:{rmorphism P->L}:=GRing.RMorphism.clone P L (inclusion \o EJ) _.
have hEJ:=@polynomial_evaluation_after_ring_map A P G C embed variable E gamma J pi hJ.
have hEL:=@polynomial_evaluation_after_ring_map A P C L embed variable scalar (pi gamma) EJ inclusion hEJ.
have hZero:EL W = 0.
  change (inclusion (pi (J W)) = 0).
  by rewrite (commutative_quotient_kernel hPi _).2 // rmorph0.
have hCoefficientOriginal:is_coefficient_fraction_field chi eta phi.
  constructor.
  - move=>a;change (phi (eta a) = inclusion (pi (E a))).
    exact:coefficient_fraction_scalar_triangle hCoefficient a.
  - move=>y;have [a [b [hB hValue]]]:=coefficient_fraction_representation hCoefficient y.
    exists a,b;split;[exact:hB|exact:hValue].
have hNonzero:inclusion (pi sigma)!=0.
  apply/eqP=>hZeroSigma;apply:hOutside;apply:(commutative_quotient_kernel hPi _).1.
  apply:(fraction_field_embedding_injective hFraction);by rewrite hZeroSigma rmorph0.
have [delta [T [hDelta [hSupport hValue]]]]:=@primitive_field_original_bounded_representative
  A P L M embed variable coefficient hP hDomain chi eta phi (inclusion (pi gamma)) EL W k
  hCoefficientOriginal hEL hGenerated hW hZero (inclusion (pi sigma))^-1.
have hProduct:inclusion (pi sigma)*EL T = chi delta.
  by rewrite -hValue mulrCA (mulfV hNonzero) mulr1.
exists delta,T;split;first exact:hDelta.
split;first exact:hSupport.
apply:(commutative_quotient_kernel hPi _).1.
apply:(fraction_field_embedding_injective hFraction).
rewrite rmorph0 !rmorphB !rmorphM.
change (inclusion (pi sigma)*EL T-chi delta = 0).
by rewrite hProduct subrr.
Qed.
