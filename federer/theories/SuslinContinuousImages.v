(** Federer (1969), 2.2.10, p. 65: a continuous image in a Hausdorff space
    of a Suslin subset of a complete separable metric space is Suslin. The
    source map is defined on the actual subspace S; no extension to its
    ambient space is required. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace CompleteMetricUP SuslinSetUP ClosedSetProjection
  SuslinSequenceImages SuslinParametrisation MetricSubsetBackground MetricSubsetCorestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_suslin_subspace_image]: direct
    continuous-image assertion in Federer 2.2.10, p. 65.
    Parametrise nonempty S by N and compose; handle empty S
    by the empty closed witness. The Hausdorff target condition
    is retained for the closed-graph argument. *)
Theorem continuous_suslin_subspace_image (R : realType) (T : metricType R)
    (Y : topologicalType) (S : set T) (f : metric_subset S -> Y) :
  is_complete_metric_space T ->
  (exists D : set T, countable D /\ dense D) ->
  is_suslin_set R S -> hausdorff_space Y -> continuous f ->
  is_suslin_set R (f @` setT).
Proof.
move=> hT hsep hS hY hf; case: (pselect (S !=set0))=> [hn|hn].
- have [h [hh he]] := @nonempty_suslin_sequence_parametrisation R T S hT hsep hS hn.
  have hhS n : S (h n) by rewrite -he; exists n.
  pose g := metric_subset_corestriction hhS.
  have hg : continuous g := @metric_subset_corestriction_continuous R T
    [the topologicalType of positive_sequence_space R] S h hhS hh.
  have hfg : continuous (fun n => f (g n)).
    move=> n; exact: continuous_comp (hg n) (hf (g n)).
  have him : (fun n => f (g n)) @` setT = f @` setT.
    apply/seteqP; split.
    + move=> y [n _ <-]; by exists (g n).
    + move=> y [a _ <-].
      have ha : S (val a) := set_valP a.
      have ha' : (h @` setT) (val a) by rewrite he.
      have [n _ hna] := ha'.
      have hga : g n = a by apply: val_inj; exact hna.
      exists n=> //; by rewrite hga.
  rewrite -him; exact: continuous_sequence_image_suslin hY hfg.
- have he : f @` setT = set0.
    apply/seteqP; split=> [y [a _ <-]|y []].
    exfalso; apply: hn; exists (val a); exact: set_valP.
  rewrite he; exact: empty_set_suslin.
Qed.
