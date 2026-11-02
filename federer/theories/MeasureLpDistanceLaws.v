(** Federer (1969), 2.4.12, pp. 86–88: distance consequences of the finite-p
    seminorm, used in completeness and extension of the vector integral.
    Telescoping identities hold on common conull domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic PartialNormedIdentities
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasurableNormedArithmetic MeasurableNormedDifference MeasureLpConvergence MeasureLpTriangle MeasureLpNormAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_distance_symmetric]: supporting symmetry
    of the finite-p difference seminorm in Federer 2.4.12, p. 87. *)
Lemma measure_lp_distance_symmetric (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  measure_lp_distance mu N p f g = measure_lp_distance mu N p g f.
Proof.
move=> hp hf hg.
have hfg := @measurable_normed_function_subtract R X V N hN mu hm f g hf hg.
have hgf := @measurable_normed_function_subtract R X V N hN mu hm g f hg hf.
apply: (@measure_lp_norm_almost_norm_equal R X V N hN mu hm p _ _ hp hfg.1 hgf.1).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _
    (measurable_function_domain hf.1) (measurable_function_domain hg.1))).
move=> x [[u hu] [v hv]]; exists (u-v)%R,(v-u)%R; split.
- apply/partial_vector_subtract_graph; exists u,v; by split=> //; split.
- split.
  + apply/partial_vector_subtract_graph; exists v,u; by split=> //; split.
  + by rewrite (real_seminorm_subtract hN.1).
Qed.

(** Source for [measure_lp_distance_triangle]: supporting full
    distance triangle inequality for Federer 2.4.12, pp. 87–88,
    allowing infinite individual distances and retaining partial domains. *)
Lemma measure_lp_distance_triangle (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g h : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  is_measurable_normed_function mu h ->
  measure_lp_distance mu N p f h <= measure_lp_distance mu N p f g + measure_lp_distance mu N p g h.
Proof.
move=> hp hf hg hh.
have hfg := @measurable_normed_function_subtract R X V N hN mu hm f g hf hg.
have hgh := @measurable_normed_function_subtract R X V N hN mu hm g h hg hh.
have hfh := @measurable_normed_function_subtract R X V N hN mu hm f h hf hh.
have hsum := @measurable_normed_function_add R X V N hN mu hm _ _ hfg hgh.
have hd1 := @measure_almost_everywhere_and R X mu hm _ _
  (measurable_function_domain hf.1) (measurable_function_domain hg.1).
have hd := @measure_almost_everywhere_and R X mu hm _ _ hd1 (measurable_function_domain hh.1).
have ha : measure_almost_equal mu
    (partial_vector_add (partial_vector_subtract f g) (partial_vector_subtract g h))
    (partial_vector_subtract f h).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd).
  move=> x [[hfx hgx] hhx]; exact: partial_difference_telescope_agreement hfx hgx hhx.
have he := @measure_lp_norm_almost_equal R X V N hN mu hm p _ _ hp hsum.1 hfh.1 ha.
rewrite /measure_lp_distance -he.
exact (@measure_lp_norm_triangle R X V N hN mu hm p _ _ hp hfg hgh).
Qed.
