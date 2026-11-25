(** Federer (1969), 2.2.6, p. 63: continuity in the product of discrete
    coordinate spaces. The criterion here uses eventual coordinate equality,
    the neighborhood formulation for discrete factors. Source context and
    encoding: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceProductTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [positive_sequence_coordinate_neighborhood]:
    supporting lemma for Federer 2.2.6, p. 63: prescribing a
    single discrete coordinate gives a neighborhood of a point. *)
Lemma positive_sequence_coordinate_neighborhood (R : realType)
    (x : positive_sequence_space R) i :
  nbhs x [set y | positive_sequence_coordinates y i = positive_sequence_coordinates x i].
Proof.
apply: filterS (positive_sequence_prefix_neighborhood x i.+1)=> y hy.
exact: esym (hy i (ltnSn i)).
Qed.

(** Source for [positive_sequence_coordinate_continuous]: Federer 2.2.6, p.
    63, product continuity criterion, stated using local constancy of each
    positive-integer coordinate. *)
Theorem positive_sequence_coordinate_continuous (R : realType) (T : topologicalType)
    (f : T -> positive_sequence_space R) :
  continuous f <-> forall x i,
    nbhs x [set y | positive_sequence_coordinates (f y) i = positive_sequence_coordinates (f x) i].
Proof.
split.
- move=> hf x i; exact: hf x _ (positive_sequence_coordinate_neighborhood (f x) i).
- move=> hf x U hu.
  have [N hN] := proj1 (positive_sequence_product_neighborhoods (f x) U) hu.
  have hp n : nbhs x [set y | positive_sequence_prefix (f x) n (f y)].
    elim: n=> [|n hn].
    + apply: filterS filterT=> y _ i; by rewrite ltn0.
    + apply: filterS (filterI hn (hf x n))=> y [hy he] i hi.
      case: (ltngtP i n)=> hin.
      * exact: hy i hin.
      * by move: hi; rewrite ltnS leqNgt hin.
      * rewrite hin; exact: esym he.
  apply: filterS (hp N)=> y hy; exact: hN (f y) hy.
Qed.
