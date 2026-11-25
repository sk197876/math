(** Federer (1969), 3.4.7, p. 325: the scalar
    integrality step of Gauss's lemma. A fraction multiplying
    primitive coefficients into original coefficients belongs to the
    original ring. Actual denominator cancellation proves the claim. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP FractionFieldUP GaussDenominatorDivisibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_scalar_integrality]: a scalar fraction
    carrying primitive original coefficients to original coefficients
    is integral, supporting the Gauss lemma in 3.4.7,
    p. 325. No reduced-fraction or gcd hypothesis is added. *)
Theorem gauss_scalar_integrality (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) (hField:is_commutative_fraction_field embed)
    (hUFD:is_unique_factorization_commutative_domain A)
    (f g:nat->A) (s:K):
  (forall p,is_commutative_prime_element p ->exists i,~commutative_divides p (f i)) ->
  (forall i,embed (g i) = s*embed (f i)) ->
  exists c:A,s = embed c.
Proof.
move=>hPrimitive hEquation.
have [a [b [hb hFraction]]]:=fraction_field_fraction_representation hField s.
have hInjective:=fraction_field_embedding_injective hField.
have hDen:embed b!=0.
  apply/eqP=>hZero;apply:hb;apply:hInjective;by rewrite rmorph0.
have hIntegralEquation i:b*g i = a*f i.
  apply:hInjective.
  rewrite !rmorphM hEquation hFraction mulrA.
  by rewrite (mulrC (embed b) (embed a/embed b)) divfK.
have [c hC]:=@gauss_denominator_divides_numerator A hUFD f g a b
  hPrimitive hb hIntegralEquation.
exists c;by rewrite hFraction hC rmorphM mulfK.
Qed.
