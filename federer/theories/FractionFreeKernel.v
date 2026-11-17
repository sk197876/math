(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328, and the finite original coefficient module in (8),
    p. 329. Clear original denominators in a finite free cover.
    Only the existing abstract fraction-field laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets ring.
From Federer Require Import FractionFieldUP CommutativeDomainUP CommutativeDomainCancellation
  RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [fraction_free_coordinates]: the original coefficient
    embedding in finite coordinates, supporting the coefficient module
    of Federer 3.4.8(8), p. 329 and the auxiliary claim in (5), p. 328. *)
Definition fraction_free_coordinates (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) n (a:{ffun 'I_n->A^o}):{ffun 'I_n->K^o}:=
  [ffun i=>embed (a i)].

(** Source for [fraction_free_kernel]: original denominator relations
    defining the fraction-field span of a finite free-cover kernel,
    supporting Federer 3.4.8(8), p. 329 and (5), p. 328.
    Its definition assumes no separation or dimension conclusion. *)
Definition fraction_free_kernel (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) (V:lmodType A) n
    (f:{linear {ffun 'I_n->A^o}->V}) (v:{ffun 'I_n->K^o}):Prop:=
  exists d:A,exists a:{ffun 'I_n->A^o},
    d<>0 /\f a = 0 /\forall i,embed d*v i = embed (a i).

(** Source for [fraction_free_kernel_submodule]: the original
    denominator relations form a field subspace, supporting the finite
    coefficient argument of Federer 3.4.8(8), p. 329 and (5), p. 328.
    The proof clears denominators rather than introducing a localization. *)
Theorem fraction_free_kernel_submodule (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) (V:lmodType A) n
    (f:{linear {ffun 'I_n->A^o}->V}):
  is_commutative_fraction_field embed ->is_commutative_integral_domain A ->
  is_ring_submodule (@fraction_free_kernel A K embed V n f).
Proof.
move=>hField hDomain.
have hInjective:=fraction_field_embedding_injective hField.
have hEmbeddedNonzero (a:A):a<>0 ->embed a!=0.
  move=>hA;apply/eqP=>hZero;apply:hA;apply:hInjective;by rewrite hZero rmorph0.
constructor.
- exists 1,0;split;first by apply/eqP;exact:oner_neq0.
  split;first exact:linear0.
  move=>i;by rewrite !ffunE !rmorph0 mulr0.
- move=>v w [d [a [hd [ha hA]]]] [e [b [he [hb hB]]]].
  exists (d*e),(e*:a+d*:b);split.
  + exact:(@commutative_domain_product_nonzero A hDomain d e hd he).
  + split.
    * by rewrite linearD !linearZ /= ha hb !scaler0 add0r.
    *
    move=>i;rewrite !ffunE !rmorphD !rmorphM mulrDr.
    change (embed d*embed e*v i+embed d*embed e*w i =
      embed e*embed (a i)+embed d*embed (b i)).
    congr (_+_).
    -- by rewrite [embed d*embed e]mulrC -mulrA hA.
    -- by rewrite -mulrA hB.
- move=>v [d [a [hd [ha hA]]]].
  exists d,(-a);split=>//;split;first by rewrite linearN ha oppr0.
  move=>i;rewrite !ffunE rmorphN mulrN hA;reflexivity.
- move=>c v [d [a [hd [ha hA]]]].
  have [p [q [hq hC]]]:=fraction_field_fraction_representation hField c.
  have hQ:=hEmbeddedNonzero q hq.
  have hQC:embed q*c = embed p.
    by rewrite hC mulrCA divff // mulr1.
  exists (q*d),(p*:a);split.
  + exact:(@commutative_domain_product_nonzero A hDomain q d hq hd).
  + split;first by rewrite linearZ /= ha scaler0.
    move=>i;rewrite !ffunE !rmorphM.
    change (embed q*embed d*(c*v i) = embed p*embed (a i)).
    have hRearr:embed q*embed d*(c*v i) = (embed q*c)*(embed d*v i) by ring.
    by rewrite hRearr hQC hA.
Qed.

(** Source for [fraction_free_kernel_detects_torsion]: a lift of a
    non-torsion original vector has nonzero fraction-kernel class,
    supporting the finite coefficient module of Federer 3.4.8(8),
    p. 329 and the auxiliary assertion in (5), p. 328. *)
Lemma fraction_free_kernel_detects_torsion (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}) (V:lmodType A) n
    (f:{linear {ffun 'I_n->A^o}->V}) (b:{ffun 'I_n->A^o}):
  is_commutative_fraction_field embed ->
  (forall a:A,a*:(f b) = 0 ->a = 0) ->
  ~fraction_free_kernel embed f (fraction_free_coordinates embed b).
Proof.
move=>hField hTorsion [d [a [hd [ha hA]]]].
have hVector:d*:b = a.
  apply/ffunP=>i;apply:(fraction_field_embedding_injective hField).
  have hh:=hA i;move:hh;by rewrite /fraction_free_coordinates !ffunE rmorphM.
have hZero:d*:(f b) = 0 by rewrite -linearZ hVector ha.
exact:hd (hTorsion d hZero).
Qed.
