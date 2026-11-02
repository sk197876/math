(** Federer (1969), 3.2.10, p. 248: exact fibre
    images and their inverse coordinate restrictions. These
    are pointwise statements, valid for every target point
    and every subset of a coordinate inverse piece. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_inverse_fibre_point]: the exact
    inverse formula at the start of the proof of Federer
    3.2.10, p. 248. This supporting pointwise law requires
    only the printed coordinate and left-inverse identities. *)
Lemma coordinate_inverse_fibre_point (R:realType) m n k
    (f:R_n R m->R_n R n) (E:set (R_n R m))
    (p:R_n R m->R_n R k) (u:R_n R m->R_n R (n+k))
    (v:R_n R (n+k)->R_n R m):
  (forall x,E x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  forall y x,mapping_fibre f E y x ->v (euclidean_block_join (y,p x))=x.
Proof.
move=>h y x [hx hfx]; have [hu hv]:=h x hx.
by rewrite -hfx -hu.
Qed.

(** Source for [coordinate_inverse_fibre_stacked_image]: the
    first set equality in the proof of Federer 3.2.10,
    p. 248: u sends the fibre exactly to its first-fixed
    coordinate product. No measurability or exceptional set is needed. *)
Lemma coordinate_inverse_fibre_stacked_image (R:realType) m n k
    (f:R_n R m->R_n R n) (E:set (R_n R m))
    (p:R_n R m->R_n R k) (u:R_n R m->R_n R (n+k))
    (v:R_n R (n+k)->R_n R m):
  (forall x,E x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  forall y,u @` mapping_fibre f E y=
    (fun z=>euclidean_block_join (y,z)) @` (p @` mapping_fibre f E y).
Proof.
move=>h y; apply/seteqP; split=>t.
- move=>[x [hx hfx] <-]; exists (p x); first by exists x; first split.
  by rewrite (h x hx).1 hfx.
- move=>[z [x [hx hfx] <-] <-]; exists x; first by split.
  by rewrite (h x hx).1 hfx.
Qed.

(** Source for [coordinate_inverse_fibre_image]: the exact
    set identity in the statement of Federer 3.2.10,
    p. 248. Every y is retained, including empty fibres.
    Apply this to E or any subset of E by restriction. *)
Theorem coordinate_inverse_fibre_image (R:realType) m n k
    (f:R_n R m->R_n R n) (E:set (R_n R m))
    (p:R_n R m->R_n R k) (u:R_n R m->R_n R (n+k))
    (v:R_n R (n+k)->R_n R m):
  (forall x,E x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  forall y,mapping_fibre f E y=
    (fun z=>v (euclidean_block_join (y,z))) @` (p @` mapping_fibre f E y).
Proof.
move=>h y; apply/seteqP; split=>t.
- move=>ht; exists (p t); first by exists t.
  exact (coordinate_inverse_fibre_point h ht).
- move=>[z [x hx <-] <-].
  by rewrite (coordinate_inverse_fibre_point h hx).
Qed.

(** Source for [coordinate_inverse_fibre_slice_injective]: the
    univalence assertion for v_y in Federer 3.2.10,
    p. 248. The restriction's domain is precisely the
    projected source fibre; no global univalence is asserted. *)
Lemma coordinate_inverse_fibre_slice_injective (R:realType) m n k
    (f:R_n R m->R_n R n) (E:set (R_n R m))
    (p:R_n R m->R_n R k) (u:R_n R m->R_n R (n+k))
    (v:R_n R (n+k)->R_n R m):
  (forall x,E x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  forall y z w,(p @` mapping_fibre f E y) z ->
    (p @` mapping_fibre f E y) w ->
    v (euclidean_block_join (y,z))=v (euclidean_block_join (y,w)) ->z=w.
Proof.
move=>h y z w [x hx <-] [t ht <-] he.
have hxt:x=t.
  by rewrite (coordinate_inverse_fibre_point h hx)
    (coordinate_inverse_fibre_point h ht) in he.
by rewrite hxt.
Qed.
