(** Federer (1969), 3.2.10, p. 248: the sections of
    u(B) are the projected fibres p(B intersect f inverse y).
    These supporting set identities hold for every subset B
    of a coordinate piece and every target point. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates MappingMultiplicity ProductSections CoordinateInverseFibres.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [coordinate_image_vertical_section]: the middle
    slice domain in the integral calculation of Federer
    3.2.10, p. 248, exactly equals the projected restricted
    fibre. This is a pointwise set identity, with no
    measurability or almost-everywhere qualification. *)
Lemma coordinate_image_vertical_section (R:realType) m n k
    (f:R_n R m->R_n R n) (p:R_n R m->R_n R k)
    (u:R_n R m->R_n R (n+k)) (B:set (R_n R m)):
  (forall x,B x ->u x=euclidean_block_join (f x,p x)) ->forall y,
  product_vertical_section ((@euclidean_block_join R n k) @^-1` (u @` B)) y=
    p @` mapping_fibre f B y.
Proof.
move=>h y; apply/seteqP; split=>z.
- move=>[x hx hU].
  have hEq:(f x,p x)=(y,z).
    have hParts:=congr1 (@euclidean_block_split R n k) hU.
    by rewrite (h x hx) !euclidean_block_joinK in hParts.
  exists x; first exact (conj hx (congr1 fst hEq)).
  exact (congr1 snd hEq).
- move=>[x [hx hFx] hP]; exists x; first exact hx.
  by rewrite (h x hx) hFx hP.
Qed.

(** Source for [coordinate_image_slice_mass_set]: the last
    image set in Federer 3.2.10, p. 248, is the
    original restricted fibre. This supporting version uses the
    actual vertical section of u(B), for direct Fubini application. *)
Lemma coordinate_image_slice_mass_set (R:realType) m n k
    (f:R_n R m->R_n R n) (p:R_n R m->R_n R k)
    (u:R_n R m->R_n R (n+k)) (v:R_n R (n+k)->R_n R m)
    (B:set (R_n R m)):
  (forall x,B x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->forall y,
  (fun z=>v (euclidean_block_join (y,z))) @`
    product_vertical_section ((@euclidean_block_join R n k) @^-1` (u @` B)) y=
    mapping_fibre f B y.
Proof.
move=>h y.
have hU x:B x ->u x=euclidean_block_join (f x,p x) by move=>hx; exact (h x hx).1.
by rewrite (coordinate_image_vertical_section hU) -(coordinate_inverse_fibre_image h).
Qed.
