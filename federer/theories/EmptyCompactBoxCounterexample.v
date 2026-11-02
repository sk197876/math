(** Federer (1969), 2.10.38, printed pp. 198–199: the unqualified
    compact-source statement cannot supply endpoints when the source is
    empty and the ambient dimension positive. The formal theorem must
    explicitly require nonemptiness in this case. This is a local
    qualification, not a correction listed in Federer's working erratum,
    which has no entry for pp. 198–199. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [empty_compact_enclosing_box_endpoint_counterexample]: local
    qualification of 2.10.38, p. 198.
    The empty set is compact but admits no
    source endpoint family in positive dimension.
    No box or side-length assertion can remove
    this obstruction to the printed existential statement. *)
Theorem empty_compact_enclosing_box_endpoint_counterexample (R : realType) (n : nat) :
  (0<n)%N ->
  compact (@set0 (inner_metric_space (@euclidean_inner_productP R n))) /\
  ~ exists a b : 'I_n -> inner_metric_space (@euclidean_inner_productP R n),
    forall i, set0 (a i) /\ set0 (b i).
Proof.
move=> hn; split; first exact: compact0.
by move=> [a [b h]]; have [] := (h (Ordinal hn)).1.
Qed.
