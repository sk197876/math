(** Federer (1969), 3.4.8(8), p. 329:
    the extension to fractions is unique, and its
    image is exactly the original scalar fractions.
    Prove these consequences through public field laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import FractionFieldUP FractionFieldExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable A:comNzRingType.
Variables L K:fieldType.
Variable embed:{rmorphism A->L}.
Hypothesis hField:is_commutative_fraction_field embed.
Variable f:{rmorphism A->K}.

(** Source for [fraction_field_extension_fraction]: the
    original coefficient map extends by the usual
    fraction equation, supporting M inside L in
    3.4.8(8), pp. 329–330. *)
Lemma fraction_field_extension_fraction (extend:{rmorphism L->K}):
  is_fraction_field_extension embed f extend ->forall a b:A,
    extend (embed a/embed b) = f a/f b.
Proof. by move=>hExtend a b;rewrite fmorph_div !hExtend. Qed.

(** Source for [fraction_field_extension_unique]: the
    original coefficient map determines its fraction
    extension uniquely, supporting the subfield M
    in 3.4.8(8), p. 329. *)
Theorem fraction_field_extension_unique (E F:{rmorphism L->K}):
  is_fraction_field_extension embed f E ->is_fraction_field_extension embed f F ->
    forall x:L,E x = F x.
Proof.
move=>hE hF x.
have [a [b [hB ->]]]:=fraction_field_fraction_representation hField x.
by rewrite !fmorph_div !hE !hF.
Qed.

(** Source for [fraction_field_extension_image]: the
    image consists exactly of original coefficient
    fractions with nonzero denominators, as used to
    clear denominators in 3.4.8(8), p. 330. *)
Theorem fraction_field_extension_image (extend:{rmorphism L->K}):
  is_fraction_field_extension embed f extend ->forall y:K,
    (exists x:L,extend x = y) <->exists a b:A,b<>0 /\y = f a/f b.
Proof.
move=>hExtend y;split.
- move=>[x <-].
  have [a [b [hB ->]]]:=fraction_field_fraction_representation hField x.
  exists a,b;split;first exact:hB.
  by rewrite fmorph_div !hExtend.
- move=>[a [b [hB ->]]];exists (embed a/embed b).
  by rewrite fmorph_div !hExtend.
Qed.
End Laws.
