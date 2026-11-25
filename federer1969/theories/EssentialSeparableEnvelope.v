(** Federer (1969), 2.3.8, p. 78: essential separability permits one common
    closed separable linear target. The countable version also supports
    2.3.9, pp. 79–80. Source context and partial-domain convention:
    MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric MetricSubsetBackground
  PartialFunctionUP MeasureUP MeasureAlmostBasic MeasurableNormedFunctionUP
  ClosedLinearSpanUP SeparableLinearEnvelope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [essential_range_enlarge]: supporting enlargement
    of the separable target for Federer 2.3.8, p. 78:
    replacing the target set by a superset preserves its null
    exceptional preimage. *)
Lemma essential_range_enlarge (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y)
    (A B : set Y) : A `<=` B -> mu (partial_function_preimage f (~` A)) = 0 ->
  mu (partial_function_preimage f (~` B)) = 0.
Proof.
move=> hi hz; apply: (@measure_null_subset R X mu hm _ _ _ hz).
move=> x [y [hy hn]]; exists y; split=> // ha; apply: hn; exact: hi.
Qed.

(** Source for [essential_separable_sequence_envelope]: supporting common
    closed separable linear subspace in Federer 2.3.8, p. 78, and 2.3.9, pp.
    79–80 Each function retains its own null exception and its original
    partial domain. *)
Theorem essential_separable_sequence_envelope (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  (forall n, is_essentially_separable_normed_function mu (f n)) ->
  exists Z : subspace V,
    closed (fun y : real_norm_metric_space hN => Z y) /\
    (exists D : set (metric_subset (fun y : real_norm_metric_space hN => Z y)),
      countable D /\ dense D) /\
    forall n, mu (partial_function_preimage (f n) [set y | ~ Z y]) = 0.
Proof.
move=> hf.
pose Z n := projT1 (cid (hf n)).
have hZ n := projT2 (cid (hf n)).
pose A n : set (real_norm_metric_space hN) := fun y => Z n y.
have hs n : exists D : set (metric_subset (A n)), countable D /\ dense D := (hZ n).1.
have [W [hc [hi hd]]] := @countable_separable_sets_linear_envelope R V N hN A hs.
exists W; split=> //; split=> // n.
apply: (@essential_range_enlarge R X (real_norm_metric_space hN) mu hm (f n) (A n)
  (fun y : real_norm_metric_space hN => W y) _ (hZ n).2).
move=> y hy; apply: hi; by exists n.
Qed.

(** Source for [essential_separable_pair_envelope]: binary case used for
    additive closure in Federer 2.3.8, p. 78 *)
Lemma essential_separable_pair_envelope (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_essentially_separable_normed_function mu f -> is_essentially_separable_normed_function mu g ->
  exists Z : subspace V,
    closed (fun y : real_norm_metric_space hN => Z y) /\
    (exists D : set (metric_subset (fun y : real_norm_metric_space hN => Z y)), countable D /\ dense D) /\
    mu (partial_function_preimage f [set y | ~ Z y]) = 0 /\
    mu (partial_function_preimage g [set y | ~ Z y]) = 0.
Proof.
move=> hf hg.
have hs n : is_essentially_separable_normed_function mu (if n is 0%N then f else g).
  by case: n=> [|n].
have [Z [hc [hd hz]]] := @essential_separable_sequence_envelope R X V N hN mu hm
  (fun n => if n is 0%N then f else g) hs.
exists Z; split=> //; split=> //; split; [exact: hz 0%N|exact: hz 1%N].
Qed.
