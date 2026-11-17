(** Federer (1969), 3.4.7, p. 325: clearing actual
    polynomial denominators in the coefficient fraction field.
    The resulting original polynomial is proved to exist
    through the abstract coefficient laws. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP FractionFieldUP
  CommutativePolynomialUP CommutativePolynomialFiniteSums PolynomialCoefficientDivision
  PolynomialCoefficientMapUP FiniteFractionDenominators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_clear_denominators]: every fraction
    polynomial becomes an original polynomial after multiplication
    by an original nonzero scalar, supporting Gauss's
    lemma in 3.4.7, p. 325. *)
Theorem polynomial_clear_denominators (A B:comNzRingType) (K:fieldType) (D:comNzRingType)
    (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
    (embedK:{rmorphism K->D}) (variableK:D) (target:D->nat->K)
    (hSource:is_commutative_polynomial_ring embedA variableA source)
    (hTarget:is_commutative_polynomial_ring embedK variableK target)
    (phi:{rmorphism A->K}) (hField:is_commutative_fraction_field phi)
    (hDomain:is_commutative_integral_domain A)
    (M:{rmorphism B->D}) (hMap:is_polynomial_coefficient_map source target phi M) (H:D):
  exists (d:A) (G:B),d<>0 /\M G = embedK (phi d)*H.
Proof.
have [N hN]:=@polynomial_coefficients_finite K D embedK variableK target hTarget H.
have [d [hd hD]]:=@finite_fraction_denominators A K phi hField hDomain N (target H).
have hChoices:forall i,exists a:A,phi d*target H i = phi a.
  move=>i;case:(ltnP i N)=>hi;first exact:hD i hi.
  exists 0;by rewrite hN // mulr0 rmorph0.
pose f i:=projT1 (cid (hChoices i)).
have hF i:phi d*target H i = phi (f i):=projT2 (cid (hChoices i)).
have hFinite:exists N,forall i,(N<=i)%N ->f i = 0.
  exists N=>i hi;apply:(fraction_field_embedding_injective hField).
  by rewrite -hF hN // mulr0 rmorph0.
have [G hG]:=@polynomial_interpolation_exists A B embedA variableA source hSource f hFinite.
exists d,G;split;first exact:hd.
apply:(@polynomial_coefficients_unique K D embedK variableK target hTarget)=>i.
by rewrite hMap hG (@polynomial_coefficient_scalar_multiply K D embedK variableK target hTarget) hF.
Qed.
