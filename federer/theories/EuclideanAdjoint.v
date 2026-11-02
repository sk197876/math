(** Federer (1969), 3.1.21, p. 234: dual coordinate
    changes in the normal bundle, using the sealed adjoint
    of 1.7.4, p. 30. No adjoint implementation is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP AdjointUP Adjoint AdjointLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Adjoint.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).

(** Source for [euclidean_adjoint]: the abstractly specified
    adjoint from Federer 1.7.4, p. 30, used for normal
    bundle coordinates in 3.1.21, p. 234. The finite
    basis supplies existence through the existing opaque seal. *)
Definition euclidean_adjoint (L:Hom X X) : Hom X X :=
  hom_of_linear (@inner_adjoint R X X B B hB hB n (@coordinate_basis R n)
    (@coordinate_basisP R n) (hom_as_linear L)).

(** Source for [euclidean_adjoint_pairing]: the adjoint pairing
    law supporting normal coordinate changes in Federer 3.1.21,
    p. 234, directly from the laws of 1.7.4, p. 30. *)
Lemma euclidean_adjoint_pairing L x y : B x (euclidean_adjoint L y)=B (L x) y.
Proof.
exact (@inner_adjointP R X X B B hB hB n (@coordinate_basis R n)
  (@coordinate_basisP R n) (hom_as_linear L) x y).
Qed.

(** Source for [euclidean_adjoint_linear]: adjoints depend
    linearly on operators, supporting class-(k-1) normal bundle
    charts in Federer 3.1.21, p. 234. The proof uses
    the defining pairing alone. *)
Lemma euclidean_adjoint_linear : linear euclidean_adjoint.
Proof.
move=>c L M; apply: hom_ext=>y; apply: (inner_vectors_ext hB)=>x.
rewrite (euclidean_adjoint_pairing (c*:L+M)) (bilDr (inner_bilinear hB))
  (bilZr (inner_bilinear hB)) !euclidean_adjoint_pairing.
change (B (c*:L x+M x) y=c*B (L x) y+B (M x) y).
by rewrite (bilDl (inner_bilinear hB)) (bilZl (inner_bilinear hB)).
Qed.

(** Source for [euclidean_adjoint_inverse]: inverse operators
    have mutually inverse adjoints, supporting the inverse normal
    chart in Federer 3.1.21, p. 234, by the
    composition law of 1.7.4, p. 30. *)
Lemma euclidean_adjoint_inverse (L M:Hom X X) : cancel L M ->
  cancel (euclidean_adjoint M) (euclidean_adjoint L).
Proof.
move=>hML y; apply: (inner_vectors_ext hB)=>x.
by rewrite !euclidean_adjoint_pairing hML.
Qed.
End Adjoint.
