(** Federer (1969), 3.4.7, p. 325: actual finite
    denominator clearing supporting the Gauss argument. The
    original coefficient domain and its independent fraction laws
    suffice; no gcd or reduced denominator is chosen. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation FractionFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_fraction_denominators]: finitely many
    actual fractions admit one original nonzero denominator,
    supporting the polynomial comparison in 3.4.7, p. 325. *)
Theorem finite_fraction_denominators (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) (hField:is_commutative_fraction_field embed)
    (hDomain:is_commutative_integral_domain A) N (f:nat->K):
  exists d:A,d<>0 /\forall i,(i<N)%N ->exists a:A,embed d*f i = embed a.
Proof.
elim:N=>[|N [d [hd hD]]].
- exists 1;split;first by apply/eqP;exact:oner_neq0.
  by move=>i;rewrite ltn0.
- have [a [b [hb hB]]]:=fraction_field_fraction_representation hField (f N).
  have hInjective:=fraction_field_embedding_injective hField.
  have hEmbeddedB:embed b!=0.
    apply/eqP=>hZero;apply:hb;apply:hInjective;by rewrite rmorph0.
  exists (d*b);split.
  + exact:(@commutative_domain_product_nonzero A hDomain d b hd hb).
  + move=>i hi;case:(ltnP i N)=>hI.
    * have [c hc]:=hD i hI;exists (b*c).
      by rewrite !rmorphM mulrAC hc mulrC.
    * have hIN:i = N by apply/eqP;rewrite eqn_leq hI -ltnS hi.
      rewrite hIN;exists (d*a).
      rewrite !rmorphM hB -mulrA (mulrC (embed b) (embed a/embed b)).
      by rewrite divfK.
Qed.
