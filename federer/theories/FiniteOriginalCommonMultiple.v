(** Federer (1969), 3.4.8(10), p. 331:
    replace the finitely many original nonzero
    coefficient denominators by one common
    multiple. Reuse the earlier finite-fraction
    denominator theorem; reflect its equations
    through the original faithful coefficient map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeDomainUP FractionFieldUP FiniteFractionDenominators
  WeierstrassFiniteFamilyExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_original_nonzero_common_multiple]:
    the common nonzero delta replacing all
    delta_j in 3.4.8(10), p. 331.
    Existing common-denominator equations for their
    inverses give original ring multipliers.
    The empty family is retained. *)
Theorem finite_original_nonzero_common_multiple (A:comNzRingType) (M:fieldType)
  (eta:{rmorphism A->M}) (hField:is_commutative_fraction_field eta)
  (hDomain:is_commutative_integral_domain A) N (d:'I_N->A):
  (forall i,eta (d i)<>0) ->exists delta:A,eta delta<>0 /\
    forall i:'I_N,exists a:A,delta = a*d i.
Proof.
move=>hNonzero.
have [f hF]:=@weierstrass_finite_family_extension M N (fun i=>(eta (d i))^-1) 0.
have [delta [hDelta hRepresentatives]]:=@finite_fraction_denominators A M eta hField hDomain N f.
have hInjective:=fraction_field_embedding_injective hField.
exists delta;split.
- move=>hZero;apply:hDelta;apply:hInjective;by rewrite hZero rmorph0.
- move=>i;have [a hA]:=hRepresentatives (i:nat) (ltn_ord i).
  have hEquation:=congr1 (fun z:M=>z*eta (d i)) hA.
  have hImageNonzero:eta (d i)!=0 by apply/eqP;exact:hNonzero i.
  rewrite (hF i) -mulrA (mulVf hImageNonzero) mulr1 in hEquation.
  exists a;apply:hInjective;by rewrite rmorphM.
Qed.
