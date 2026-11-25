(** Federer (1969), 3.4.8(8), p. 329:
    extend the original subring embedding to its
    fraction field. The existing independent fraction
    representation proves existence; no private fraction
    carrier or quotient pair is inspected. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import FractionFieldUP FractionFieldExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Extension.
Variable A:comNzRingType.
Variables L K:fieldType.
Variable embed:{rmorphism A->L}.
Hypothesis hField:is_commutative_fraction_field embed.
Variable f:{rmorphism A->K}.
Hypothesis hFaithful:injective f.

(** Source for [fraction_extension_denominator]: faithful
    original embeddings preserve nonzero denominators,
    supporting the subfield M in 3.4.8(8), p. 329. *)
Lemma fraction_extension_denominator (F:fieldType) (i:{rmorphism A->F}):
  injective i ->forall a:A,a<>0 ->i a!=0.
Proof.
move=>hInjective a hA;apply/eqP=>hZero;apply:hA.
apply:hInjective;by rewrite rmorph0.
Qed.

(** Source for [fraction_extension_ratio_independent]: the
    two original faithful embeddings preserve equality
    of fractions, supporting M in 3.4.8(8),
    p. 329. Reuse cross multiplication in fields. *)
Lemma fraction_extension_ratio_independent (a b c d:A):
  b<>0 ->d<>0 ->embed a/embed b = embed c/embed d ->f a/f b = f c/f d.
Proof.
move=>hB hD hEqual.
have hEmbed:=fraction_extension_denominator (fraction_field_embedding_injective hField).
have hF:=fraction_extension_denominator hFaithful.
have hCross:embed (a*d) = embed (c*b).
  apply/eqP;rewrite !rmorphM -(@eqr_div L (embed a) (embed b) (embed c) (embed d) (hEmbed b hB) (hEmbed d hD));by apply/eqP.
have hOriginal:=fraction_field_embedding_injective hField hCross.
by apply/eqP;rewrite eqr_div ?hF // -!rmorphM hOriginal.
Qed.

(** Source for [fraction_extension_pair_exists]: every
    element has original numerator and nonzero denominator,
    as already specified by the fraction-field interface
    of 3.4.7, p. 325; used in 3.4.8(8), p. 329. *)
Lemma fraction_extension_pair_exists (x:L):
  exists p:A*A,p.2<>0 /\x = embed p.1/embed p.2.
Proof.
have [a [b [hB hX]]]:=fraction_field_fraction_representation hField x.
by exists (a,b).
Qed.

(** Source for [fraction_extension_witness]: private
    selection of original coefficients for the
    extension used in 3.4.8(8), p. 329. *)
Definition fraction_extension_witness (x:L):K:=
  let p:=projT1 (cid (fraction_extension_pair_exists x)) in f p.1/f p.2.

(** Source for [fraction_extension_witness_ratio]: the
    private map preserves every original fraction,
    supporting M inside L in 3.4.8(8), p. 329. *)
Lemma fraction_extension_witness_ratio (a b:A):b<>0 ->
  fraction_extension_witness (embed a/embed b) = f a/f b.
Proof.
move=>hB;rewrite /fraction_extension_witness.
case:(cid (fraction_extension_pair_exists (embed a/embed b)))=>[[c d] [hD hEqual]] /=.
exact:(fraction_extension_ratio_independent hD hB (esym hEqual)).
Qed.

(** Source for [fraction_extension_witness_additive]: the
    extension preserves original field addition,
    supporting M in 3.4.8(8), p. 329. *)
Lemma fraction_extension_witness_additive:nmod_morphism fraction_extension_witness.
Proof.
split.
- have hOneA:(1:A)<>0 by apply/eqP;exact:oner_neq0.
  have h:=@fraction_extension_witness_ratio 0 1 hOneA.
  by rewrite !rmorph0 !mul0r in h.
move=>x y.
have [a [b [hB ->]]]:=fraction_field_fraction_representation hField x.
have [c [d [hD ->]]]:=fraction_field_fraction_representation hField y.
have hEmbed:=fraction_extension_denominator (fraction_field_embedding_injective hField).
have hF:=fraction_extension_denominator hFaithful.
have hBD:b*d<>0.
  move=>hZero;have hProduct:=congr1 f hZero.
  move/eqP:hProduct;by rewrite rmorphM rmorph0 mulf_eq0 (negbTE (hF b hB)) (negbTE (hF d hD)).
have hSum:embed a/embed b+embed c/embed d = embed (a*d+c*b)/embed (b*d).
  by rewrite rmorphD !rmorphM -addf_div ?hEmbed //.
by rewrite hSum !fraction_extension_witness_ratio // rmorphD !rmorphM -addf_div ?hF //.
Qed.
HB.instance Definition _:=GRing.isNmodMorphism.Build L K
  fraction_extension_witness fraction_extension_witness_additive.

(** Source for [fraction_extension_witness_multiplicative]:
    the extension preserves original field multiplication
    and one, supporting 3.4.8(8), p. 329. *)
Lemma fraction_extension_witness_multiplicative:monoid_morphism fraction_extension_witness.
Proof.
split.
- have hOneA:(1:A)<>0 by apply/eqP;exact:oner_neq0.
  have h:=@fraction_extension_witness_ratio 1 1 hOneA.
  by rewrite !rmorph1 !divr1 in h.
move=>x y.
have [a [b [hB ->]]]:=fraction_field_fraction_representation hField x.
have [c [d [hD ->]]]:=fraction_field_fraction_representation hField y.
have hF:=fraction_extension_denominator hFaithful.
have hBD:b*d<>0.
  move=>hZero;have hProduct:=congr1 f hZero.
  move/eqP:hProduct;by rewrite rmorphM rmorph0 mulf_eq0 (negbTE (hF b hB)) (negbTE (hF d hD)).
have hProduct:embed a/embed b*(embed c/embed d) = embed (a*c)/embed (b*d).
  by rewrite !rmorphM mulf_div.
by rewrite hProduct !fraction_extension_witness_ratio // !rmorphM mulf_div.
Qed.
HB.instance Definition _:=GRing.isMonoidMorphism.Build L K
  fraction_extension_witness fraction_extension_witness_multiplicative.

(** Source for [fraction_extension_ring_morphism]: the
    private map is an actual field embedding,
    supporting M in 3.4.8(8), p. 329. *)
Definition fraction_extension_ring_morphism:{rmorphism L->K}:=
  GRing.RMorphism.clone L K fraction_extension_witness _.

(** Source for [fraction_field_extension_exists]: the
    original faithful coefficient map extends to
    fractions, supporting the subfield M of L
    in 3.4.8(8), p. 329. *)
Theorem fraction_field_extension_exists:exists extend:{rmorphism L->K},
  is_fraction_field_extension embed f extend.
Proof.
exists fraction_extension_ring_morphism;move=>a.
change (fraction_extension_witness (embed a) = f a).
have hOneA:(1:A)<>0 by apply/eqP;exact:oner_neq0.
have h:=@fraction_extension_witness_ratio a 1 hOneA.
by rewrite !rmorph1 !divr1 in h.
Qed.
End Extension.
