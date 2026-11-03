(** Federer (1969), 3.2.41, printed p. 277, last finite-family
    display: the paired strict cuts sum into opposite halfspaces
    of the original actual vector sum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_sum_lower_coordinate_cuts]: supporting lower
    separated pair in Federer 3.2.41, p. 277. Original pair
    membership and the actual coordinate addition are retained. *)
Lemma vector_sum_lower_coordinate_cuts (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t u:R):
  vector_set_sum (A `&` [set x|x k<t]) (B `&` [set x|x k<u]) `<=`
    (vector_set_sum A B `&` [set x|x k<t+u]).
Proof.
move=> z /vector_set_sum_membership [x [y [[hx hLow] [[hy hLow'] ->]]]].
split; first exact:vector_set_sum_contains hx hy.
change (is_true ((x+y) k<t+u)).
rewrite ffunE; exact:ltrD hLow hLow'.
Qed.

(** Source for [vector_sum_upper_coordinate_cuts]: supporting upper
    separated pair in Federer 3.2.41, p. 277. Together with
    the lower pair, it gives the genuine measurable separator. *)
Lemma vector_sum_upper_coordinate_cuts (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t u:R):
  vector_set_sum (A `&` [set x|t<x k]) (B `&` [set x|u<x k]) `<=`
    (vector_set_sum A B `&` [set x|t+u<x k]).
Proof.
move=> z /vector_set_sum_membership [x [y [[hx hHigh] [[hy hHigh'] ->]]]].
split; first exact:vector_set_sum_contains hx hy.
change (is_true (t+u<(x+y) k)).
rewrite ffunE; exact:ltrD hHigh hHigh'.
Qed.
