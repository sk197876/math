(** Federer (1969), 2.10.39, printed p. 199: the subdivision has k_1 ...
    k_(m-1) small boxes. The supporting finite-product count below permits
    arbitrary counts on all sides, including count one on each unsplit side
    and the empty coordinate product. Source context: RectangularGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import RectangularGridUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [rectangular_grid_cardinality]: supporting
    number of cells in 2.10.39, p. 199.
    The finite Cartesian product of the cell-index
    ordinals has cardinality the product of their counts. *)
Lemma rectangular_grid_cardinality n (count : 'I_n -> nat) :
  #|rectangular_grid_indices count|=\prod_(i<n) count i.
Proof.
rewrite /rectangular_grid_indices card_dep_ffun foldrE big_map /=.
rewrite -big_enum; apply: eq_bigr=> i _; exact: card_ord.
Qed.
