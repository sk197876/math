(** Federer (1969), 2.3.8, pp. 78–79: the genuine vector space of
    total-domain members, needed for literal convex-hull statements. This is
    explicitly a subcollection of Federer's corrected set of partial
    functions (erratum p. 1, book p. 78 line 7). Source context:
    MeasurableNormedFunctionUP.v. The functions import supplies only
    pointwise algebra on ordinary maps, as already used in Hom.v. *)
From mathcomp Require Import all_boot all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric PartialFunctionBasic
  MeasureUP MeasurableNormedFunctionUP MeasurableNormedBasic MeasurableTotalNormedArithmetic InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TotalSpace.
Variable R : realType.
Variable X : choiceType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).
Local Notation F := (GRing.Lmodule.clone R (X -> M) _).
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.

(** Source for [total_measurable_normed_set]: total-domain subcollection
    used to interpret the convex-hull passage of Federer 2.3.8, p. 79, after
    his p. 78 erratum *)
Definition total_measurable_normed_set : set F :=
  [set f | is_measurable_normed_function mu (partial_function_total f)].

(** Source for [total_measurable_normed_subspace]: vector-space laws for the
    total-domain subcollection in Federer 2.3.8, pp. 78–79 *)
Definition total_measurable_normed_subspace : subspace F.
Proof.
refine (@Subspace R F total_measurable_normed_set _ _ _).
- exact (@measurable_normed_total_constant R X V N hN mu hm 0).
- move=> f g hf hg; exact (@measurable_normed_total_add R X V N hN mu hm f g hf hg).
- move=> c f hf; exact (@measurable_normed_total_scale R X V N hN mu hm c f hf).
Defined.

(** Source for [total_measurable_normed_convex]: supporting convexity of the
    ambient total-domain space for the convex-hull assertion in Federer
    2.3.8, p. 79 *)
Lemma total_measurable_normed_convex : is_inner_convex total_measurable_normed_set.
Proof.
move=> f g hf hg c _ _.
exact: (subspace_add (subspace_scale (s:=total_measurable_normed_subspace) (1-c) hf)
  (subspace_scale (s:=total_measurable_normed_subspace) c hg)).
Qed.
End TotalSpace.
