(** Federer (1969), 3.4.7, p. 325: two primitive
    original coefficient families that differ by a nonzero
    fraction differ by an original unit. This supports
    the normalization in the Gauss argument. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP FractionFieldUP GaussScalarIntegrality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [gauss_primitive_scalar_unit]: a scalar
    fraction relating two primitive original coefficient families
    is an original unit, supporting 3.4.7, p. 325. *)
Theorem gauss_primitive_scalar_unit (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) (hField:is_commutative_fraction_field embed)
    (hUFD:is_unique_factorization_commutative_domain A)
    (f g:nat->A) (s:K):
  (forall p,is_commutative_prime_element p ->exists i,~commutative_divides p (f i)) ->
  (forall p,is_commutative_prime_element p ->exists i,~commutative_divides p (g i)) ->
  s!=0 ->(forall i,embed (g i) = s*embed (f i)) ->
  exists c:A,is_commutative_unit c /\s = embed c.
Proof.
move=>hF hG hs hEquation.
have [c hc]:=@gauss_scalar_integrality A K embed hField hUFD f g s hF hEquation.
have hReverse i:embed (f i) = s^-1*embed (g i).
  by rewrite hEquation mulrA mulVf // mul1r.
have [d hd]:=@gauss_scalar_integrality A K embed hField hUFD g f s^-1 hG hReverse.
exists c;split;last exact:hc.
exists d;apply:(fraction_field_embedding_injective hField).
rewrite rmorphM rmorph1 -hc -hd;exact:mulVf hs.
Qed.
