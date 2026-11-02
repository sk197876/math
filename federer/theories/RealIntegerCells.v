(** Federer (1969), 2.2.15, p. 71: the Borel sets {x : j/i <= f(x) <
    (j+1)/i}, with j an integer and i positive. Natural index k represents
    i=k+1. These cells support the printed simple-function approximation.
    Only scalar integer/order arithmetic and the local Borel laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint boolp
  classical_sets reals topology num_normedtype.
From Federer Require Import RealMetricBackground BorelFunctionUP BorelFunctionBasic
  TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_integer_cell]: direct displayed Borel
    cell in Federer 2.2.15, p. 71, using positive
    i=k+1 and all signed integer j. *)
Definition real_integer_cell (R : realType) (X : Type) (f : X -> R) k (j : int) : set X :=
  [set x | j%:~R / (k.+1)%:R <= f x /\ f x < (j+1)%:~R / (k.+1)%:R].

(** Source for [real_integer_cell_scaled]: supporting arithmetic
    equivalence for the cells in Federer 2.2.15, p. 71.
    Multiplying by the positive i identifies the cell with the
    unit interval from j through j+1, excluding its upper endpoint. *)
Lemma real_integer_cell_scaled (R : realType) (X : Type) (f : X -> R) k j x :
  real_integer_cell f k j x <-> (range1 (j%:~R : R)) (f x * (k.+1)%:R).
Proof.
rewrite /real_integer_cell /range1 /mkset intrD.
rewrite ler_pdivrMr ?ltr0n // ltr_pdivlMr ?ltr0n //.
by split=> [/andP|]; first by []; move=> h; exact/andP.
Qed.

(** Source for [real_integer_cell_unique]: supporting disjointness
    of the integer cells in Federer 2.2.15, p. 71.
    It ensures that the printed weighted characteristic sum has
    at most one nonzero summand at each point. *)
Lemma real_integer_cell_unique (R : realType) (X : Type) (f : X -> R) k j l x :
  real_integer_cell f k j x -> real_integer_cell f k l x -> j = l.
Proof.
move=> hj hl; apply: range1z_inj (proj1 (real_integer_cell_scaled f k j x) hj) _.
exact: proj1 (real_integer_cell_scaled f k l x) hl.
Qed.

(** Source for [real_integer_cell_borel]: direct Borelness
    of the displayed cells in Federer 2.2.15, p. 71.
    A cell is the inverse image of the intersection of a
    closed lower ray and an open upper ray. *)
Lemma real_integer_cell_borel (R : realType) (X : topologicalType)
    (f : X -> real_line_metric R) k j :
  is_borel_function f -> borel_set (real_integer_cell f k j).
Proof.
move=> hf; apply: (@borel_function_preimage X [the topologicalType of real_line_metric R]
  f hf [set y | j%:~R / (k.+1)%:R <= y /\ y < (j+1)%:~R / (k.+1)%:R]).
apply: (borel_family_binary_intersection (borel_sets_family [the topologicalType of real_line_metric R])).
- apply: closed_borel_set; exact: closed_ge.
- apply: open_borel_set; exact: open_lt.
Qed.
