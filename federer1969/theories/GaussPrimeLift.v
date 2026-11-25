(** Federer (1969), 3.4.7, p. 325: a primitive
    factor prime over the fraction field is prime
    over the original coefficients. Actual quotient integrality
    supplies the original factor, rather than assuming it. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP FractionFieldUP
  CommutativePolynomialUP CommutativePolynomialDegreeUP PolynomialCoefficientMapUP
  GaussDivisorIntegrality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_primitive_prime_lift]: a primitive
    original polynomial whose fraction image is prime
    is an actual original prime, supporting Gauss's
    lemma in 3.4.7, p. 325. *)
Theorem gauss_primitive_prime_lift (A B:comNzRingType) (K:fieldType) (D:comNzRingType)
    (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
    (embedK:{rmorphism K->D}) (variableK:D) (target:D->nat->K)
    (hSource:is_commutative_polynomial_ring embedA variableA source)
    (hTarget:is_commutative_polynomial_ring embedK variableK target)
    (phi:{rmorphism A->K}) (hField:is_commutative_fraction_field phi)
    (hUFD:is_unique_factorization_commutative_domain A)
    (M:{rmorphism B->D}) (hMap:is_polynomial_coefficient_map source target phi M) (F:B):
  is_primitive_polynomial source (@is_commutative_prime_element A) (@commutative_divides A) F ->
  is_commutative_prime_element (M F) ->is_commutative_prime_element F.
Proof.
move=>hPrimitive hPrime.
have hInjective:injective M.
  move=>P Q hEqual;apply:(@polynomial_coefficients_unique A B embedA variableA source hSource)=>i.
  apply:(fraction_field_embedding_injective hField).
  rewrite -(hMap P i) -(hMap Q i);by rewrite hEqual.
have hLift (P:B):commutative_divides (M F) (M P) ->commutative_divides F P.
  move=>[L hL].
  have [R hR]:=@gauss_divisor_integrality A B K D embedA variableA source embedK variableK target
    hSource hTarget phi hField hUFD M hMap F P L hPrimitive hL.
  exists R;apply:hInjective;rewrite rmorphM -hR;exact:hL.
split.
- move=>hZero;apply:hPrime.1;by rewrite hZero rmorph0.
- split.
  + move=>[u hu];apply:hPrime.2.1;exists (M u);by rewrite -rmorphM hu rmorph1.
  + move=>P Q [R hProduct].
    have hImage:commutative_divides (M F) (M P*M Q).
      exists (M R);by rewrite -!rmorphM -hProduct.
    case:(hPrime.2.2 (M P) (M Q) hImage)=>h.
    * left;exact:hLift P h.
    * right;exact:hLift Q h.
Qed.
