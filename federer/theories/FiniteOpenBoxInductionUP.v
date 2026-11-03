(** Federer (1969), 3.2.41, printed p. 277: the strong
    induction hypothesis covers every original pair of smaller
    finite disjoint box families. This predicate abbreviates that
    induction argument; it is not an asserted theorem or an axiom. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  FiniteDisjointOpenBoxFamilyUP EuclideanVolumeRootSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_open_box_smaller_pair_bounds]: supporting
    induction hypothesis for card(G)+card(H) in Federer 3.2.41,
    p. 277. Strict decrease is explicit, and the original unions
    must be nonempty. All endpoint and set data remain arbitrary. *)
Definition finite_open_box_smaller_pair_bounds (R:realType) n N:Prop:=
  forall (I J:finType) (a b:I->R_n R n) (c d:J->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (H:J->set (inner_metric_space (@euclidean_inner_productP R n))),
    (#|I|+#|J|<N)%N ->
    is_finite_disjoint_open_box_family a b G ->
    is_finite_disjoint_open_box_family c d H ->
    (\bigcup_i G i) !=set0 ->(\bigcup_j H j) !=set0 ->
    euclidean_volume_root_sum_bound (\bigcup_i G i) (\bigcup_j H j).
