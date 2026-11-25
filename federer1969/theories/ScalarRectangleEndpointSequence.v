(** Federer (1969), 4.1.23, p. 380:
    choose the original finite sequence of
    scalar interval endpoints from the first
    coordinate block. Its dimension and every
    endpoint are the literal original coordinates,
    including the empty scalar product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  OrientedRectangleDomain ScalarSegmentFactors ScalarRectangleBoxCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [scalar_rectangle_endpoint_sequence]:
    the scalar factor R in
    Federer 4.1.23, p. 380,
    uses the first m actual
    coordinate intervals in their original order. *)
Definition scalar_rectangle_endpoint_sequence (R : realType) m
    (a b : R_n R m) : seq (R*R) :=
  [seq (a i,b i) | i <- enum 'I_m].

(** Source for [scalar_rectangle_endpoint_sequence_dimension]:
    the original scalar factor has
    exactly m dimensions, supporting
    the product construction of Federer
    4.1.23, p. 380. *)
Lemma scalar_rectangle_endpoint_sequence_dimension (R : realType) m
    (a b : R_n R m) :
  oriented_rectangle_dimension (@scalar_segment_factors R
    (scalar_rectangle_endpoint_sequence a b))=m.
Proof.
by rewrite scalar_rectangle_dimension /scalar_rectangle_endpoint_sequence
  size_map size_enum_ord.
Qed.

(** Source for [scalar_rectangle_endpoint_sequence_values]:
    each endpoint pair of the
    chosen original scalar rectangle is
    the corresponding original coordinate pair,
    Federer 4.1.23, p. 380. *)
Lemma scalar_rectangle_endpoint_sequence_values (R : realType) m
    (a b : R_n R m) (i : 'I_m) :
  nth (0,0) (scalar_rectangle_endpoint_sequence a b) (val i)=(a i,b i).
Proof.
have hIndex : (val i<size (enum 'I_m))%N by rewrite size_enum_ord; exact: ltn_ord i.
rewrite /scalar_rectangle_endpoint_sequence
  (@nth_map 'I_m i (R*R)%type (0,0) (fun k => (a k,b k))
    (val i) (enum 'I_m) hIndex) nth_ord_enum.
reflexivity.
Qed.

(** Source for [scalar_rectangle_endpoint_sequence_ordered]:
    strict box endpoints give the
    original ordered scalar rectangle required
    by the product-density identity in
    Federer 4.1.23, p. 380. *)
Lemma scalar_rectangle_endpoint_sequence_ordered (R : realType) m
    (a b : R_n R m) :
  (forall i, a i<b i) ->
  @scalar_rectangle_ordered R (scalar_rectangle_endpoint_sequence a b).
Proof.
move=> hOrder; apply/allP=> p.
rewrite /scalar_rectangle_endpoint_sequence=> /mapP [i _ ->].
exact: hOrder.
Qed.
