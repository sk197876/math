(** Federer (1969), 2.3.8, p. 78: the extended pseudometric laws and
    translation invariance on A(mu,Y). Source context and domain correction:
    MeasurableNormedFunctionUP.v. Algebraic identities that change partial
    domains are used only after proving almost equality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  PartialNormedIdentities MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedDifference
  MeasurableNormSuperlevels MeasureGauge MeasureGaugeComparison MeasureGaugeTriangle
  MeasureDifferenceZero MeasureNullModification MeasureConvergenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Laws.
Variable R : realType.
Variable X : choiceType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.

(** Source for [measure_normed_distance_nonnegative]: nonnegative
    distance in Federer 2.3.8, p. 78; no measurable-function
    hypothesis is necessary for this inequality. *)
Lemma measure_normed_distance_nonnegative (f g : partial_function X M) :
  0 <= measure_normed_distance mu N f g.
Proof. exact: measure_gauge_nonnegative. Qed.

(** Source for [measure_normed_distance_symmetric]: symmetry of
    the pseudodistance in Federer 2.3.8, p. 78. The
    exact common domain makes this independent of measurability. *)
Lemma measure_normed_distance_symmetric (f g : partial_function X M) :
  measure_normed_distance mu N f g = measure_normed_distance mu N g f.
Proof.
apply: measure_gauge_superlevel_invariance=> r.
by rewrite (partial_norm_difference_symmetric_superlevel hN.1).
Qed.

(** Source for [measure_normed_distance_zero_iff]: direct zero- distance
    criterion in Federer 2.3.8, p. 78 Undefined points are included among
    the almost-equality exceptions. *)
Lemma measure_normed_distance_zero_iff (f g : partial_function X M) :
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  (measure_normed_distance mu N f g = 0 <-> measure_almost_equal mu f g).
Proof.
move=> hf hg.
have hd := @measurable_normed_function_subtract R X V N hN mu hm f g hf hg.
exact (@measure_difference_gauge_zero_iff R X V N hN mu hm f g
  (measurable_function_domain hf.1) (measurable_function_domain hg.1)
  (@measurable_norm_superlevel R X V N hN mu hm _ hd.1)).
Qed.

(** Source for [measure_normed_distance_self]: zero self-distance
    in Federer 2.3.8, p. 78, for every member of A(mu,Y). *)
Lemma measure_normed_distance_self (f : partial_function X M) :
  is_measurable_normed_function mu f -> measure_normed_distance mu N f f = 0.
Proof.
move=> hf; apply: (proj2 (measure_normed_distance_zero_iff hf hf)).
apply: (proj2 (@measure_almost_equal_self R X M mu f)).
exact: measurable_function_domain hf.1.
Qed.

(** Source for [measure_normed_distance_triangle]: full triangle
    law for the pseudodistance in Federer 2.3.8, p. 78.
    The intermediate function's missing domain is a null exception,
    so the telescoping identity suffices almost everywhere. *)
Lemma measure_normed_distance_triangle (f g h : partial_function X M) :
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  is_measurable_normed_function mu h ->
  measure_normed_distance mu N f h <= measure_normed_distance mu N f g + measure_normed_distance mu N g h.
Proof.
move=> hf hg hh.
have hfg := @measurable_normed_function_subtract R X V N hN mu hm f g hf hg.
have hgh := @measurable_normed_function_subtract R X V N hN mu hm g h hg hh.
have hd1 := @measure_almost_everywhere_and R X mu hm _ _
  (measurable_function_domain hf.1) (measurable_function_domain hg.1).
have hd := @measure_almost_everywhere_and R X mu hm _ _ hd1 (measurable_function_domain hh.1).
have ha : measure_almost_equal mu
    (partial_vector_add (partial_vector_subtract f g) (partial_vector_subtract g h))
    (partial_vector_subtract f h).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd).
  move=> x [[hfx hgx] hhx]; exact: partial_difference_telescope_agreement hfx hgx hhx.
have he := @measure_gauge_almost_invariance R X M mu hm N _ _ ha.
rewrite /measure_normed_distance -he.
exact (@measure_gauge_triangle R X V mu hm N hN.1 _ _
  (@measurable_norm_superlevel R X V N hN mu hm _ hfg.1)
  (@measurable_norm_superlevel R X V N hN mu hm _ hgh.1)).
Qed.

(** Source for [measure_normed_distance_translation]: direct
    translation invariance in Federer 2.3.8, p. 78.
    Translation by a member of A(mu,Y) may shrink the domains,
    but only by a null set. *)
Lemma measure_normed_distance_translation (f g h : partial_function X M) :
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  is_measurable_normed_function mu h ->
  measure_normed_distance mu N (partial_vector_add f h) (partial_vector_add g h) =
    measure_normed_distance mu N f g.
Proof.
move=> hf hg hh.
have hd1 := @measure_almost_everywhere_and R X mu hm _ _
  (measurable_function_domain hf.1) (measurable_function_domain hg.1).
have hd := @measure_almost_everywhere_and R X mu hm _ _ hd1 (measurable_function_domain hh.1).
apply: (@measure_gauge_almost_invariance R X M mu hm N).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd).
move=> x [[hfx hgx] hhx]; exact: partial_difference_translation_agreement hfx hgx hhx.
Qed.
End Laws.
