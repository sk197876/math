(** General topology supporting the separable-range reduction in Federer
    (1969), 2.3.8, p. 78. Source context: ClosedLinearSpanUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [metric_subset_pair_inclusion_continuous]: supporting
    continuity of product inclusion for Federer 2.3.8, p. 78;
    no linearity or closedness of the subsets is needed. *)
Lemma metric_subset_pair_inclusion_continuous (R : realType)
    (T U : metricType R) (A : set T) (B : set U) :
  continuous (fun p : metric_subset A * metric_subset B => ((val p.1 : T), (val p.2 : U))).
Proof.
move=> [x y] W [[C D] [hC hD] hCD].
exists ((fun a : metric_subset A => C (val a)), (fun b : metric_subset B => D (val b))).
- split.
  + exact: (@metric_subset_inclusion_continuous R T A x C hC).
  + exact: (@metric_subset_inclusion_continuous R U B y D hD).
- move=> [a b] [ha hb]; apply: hCD; by split.
Qed.

(** Source for [continuous_binary_operation_on_subsets]: supporting
    restriction of a continuous binary operation to subspaces for Federer
    2.3.8, p. 78 *)
Lemma continuous_binary_operation_on_subsets (R : realType)
    (T U : metricType R) (W : topologicalType) (A : set T) (B : set U)
    (b : T*U -> W) : continuous b ->
  continuous (fun p : metric_subset A * metric_subset B => b (val p.1,val p.2)).
Proof.
move=> hb p V hV.
exact: (@metric_subset_pair_inclusion_continuous R T U A B p _ (hb _ V hV)).
Qed.
