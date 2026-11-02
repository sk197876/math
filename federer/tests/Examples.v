(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector TensorProduct TensorMaps TensorSpan.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** A non-degeneracy example in free spaces on arbitrary index types.
    Taking A = B = nat gives an example with infinitely many basis vectors. *)
Section Coordinates.
Variable K : fieldType.
Variables A B : choiceType.
Variables (i : A) (j : B).
Local Notation FA := (GRing.Lmodule.clone K (free_vector K A) _).
Local Notation FB := (GRing.Lmodule.clone K (free_vector K B) _).

(** Source for [coordinate_pairing]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition coordinate_pairing (u : free_vector K A) (v : free_vector K B) : K^o :=
  u i * v j.

(** Source for [coordinate_pairing_bilinear]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma coordinate_pairing_bilinear : bilinear coordinate_pairing.
Proof.
split.
  move=> v a u u'; rewrite /coordinate_pairing free_addE free_scaleE.
  by rewrite mulrDl /GRing.scale /= mulrA.
move=> u a v v'; rewrite /coordinate_pairing free_addE free_scaleE.
by rewrite mulrDr /GRing.scale /= mulrCA.
Qed.

(** Source for [tensor_coordinate]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition tensor_coordinate :
    {linear tensor_space FA FB -> K^o} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift coordinate_pairing_bilinear) _.

(** Source for [tensor_coordinateE]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma tensor_coordinateE u v :
  tensor_coordinate (tensor_inj u v) = u i * v j.
Proof. exact: tensor_liftE. Qed.

(** Source for [tensor_coordinate_delta]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma tensor_coordinate_delta :
  tensor_coordinate (tensor_inj (delta K i) (delta K j)) = 1.
Proof. by rewrite tensor_coordinateE !deltaE !eqxx mulr1. Qed.

(** Source for [pure_delta_nonzero]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Theorem pure_delta_nonzero : tensor_inj (delta K i) (delta K j) != 0.
Proof.
apply/eqP=> h.
have e := tensor_coordinate_delta.
rewrite h linear0 in e.
by move: e; apply/eqP; rewrite eq_sym oner_eq0.
Qed.
End Coordinates.

Section InfiniteIndexExample.
Variable K : fieldType.
Local Notation FN :=
  (GRing.Lmodule.clone K (free_vector K (Choice.clone nat _)) _).

(** Source for [nat_basis_tensor_nonzero]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Local regression example for this passage; the
    example itself is not stated in the book. *)
Example nat_basis_tensor_nonzero (m n : nat) :
  tensor_inj (delta K m) (delta K n) != 0.
Proof. exact: pure_delta_nonzero. Qed.

(** Source for [swap_back]: Federer (1969), 1.1.2, p. 10, final paragraph
    and dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Local regression example for this passage; the example itself is not
    stated in the book. *)
Example swap_back (t : tensor_space FN FN) :
  tensor_swap _ _ (tensor_swap _ _ t) = t.
Proof. exact: tensor_swapK. Qed.
End InfiniteIndexExample.
