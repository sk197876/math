(** Federer (1969), 2.4.12, pp. 86-87: the finite-p seminorm on total-domain
    members of A. Federer's erratum p. 1, book p. 86 bottom, replaces A by
    its total-domain subspace for this assertion; the definitions of A and
    Lp retain partial domains. All consequences below use the abstract Lp
    norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient SubspaceCarrier ExtendedSeminormUP
  PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableNormedFunctionUP MeasurableNormedArithmetic MeasurableTotalNormedArithmetic TotalMeasurableFunctionSpace
  MeasureLpNorm MeasureLpNormScale MeasureLpNormAlmostEquality MeasureLpTriangle.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section TotalLp.
Variable R : realType.
Variable X : choiceType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Variable p : R.
Hypothesis hp : (1 <= p)%R.
Local Notation M := (real_norm_metric_space hN).
Local Notation A := (@total_measurable_normed_subspace R X V N hN mu hm).

(** Source for [total_lp_norm_scale]: supporting identification of
    pointwise scalar multiplication with the partial-function operation
    in Federer 2.4.12, pp. 86-87, after the total-domain
    erratum correction. Zero scalars and infinite norms are included. *)
Lemma total_lp_norm_scale (c : R) (f : X -> M) :
  is_measurable_normed_function mu (partial_function_total f) ->
  measure_lp_norm mu N p (partial_function_total (fun x => (c *: f x)%R)) =
    `|c|%:E * measure_lp_norm mu N p (partial_function_total f).
Proof.
move=> hf.
have hs := @measurable_normed_function_scale R X V N hN mu hm c _ hf.
have ht := @measurable_normed_total_scale R X V N hN mu hm c f hf.
have he : measure_almost_equal mu (partial_vector_scale c (partial_function_total f))
    (partial_function_total (fun x => (c *: f x)%R)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (c *: f x)%R; split=> //.
  apply/partial_vector_scale_graph; exists (f x); by split.
rewrite -(@measure_lp_norm_almost_equal R X V N hN mu hm p _ _ hp hs.1 ht.1 he).
exact (@measure_lp_norm_scale R X V N hN mu hm p c _ hp hf.1).
Qed.

(** Source for [total_lp_norm_triangle]: supporting pointwise total
    sum identification for the seminorm assertion of Federer 2.4.12,
    p. 87, with the erratum's total-domain convention. *)
Lemma total_lp_norm_triangle (f g : X -> M) :
  is_measurable_normed_function mu (partial_function_total f) ->
  is_measurable_normed_function mu (partial_function_total g) ->
  measure_lp_norm mu N p (partial_function_total (fun x => (f x+g x)%R)) <=
    measure_lp_norm mu N p (partial_function_total f) + measure_lp_norm mu N p (partial_function_total g).
Proof.
move=> hf hg.
have hs := @measurable_normed_function_add R X V N hN mu hm _ _ hf hg.
have ht := @measurable_normed_total_add R X V N hN mu hm f g hf hg.
have he : measure_almost_equal mu (partial_vector_add (partial_function_total f) (partial_function_total g))
    (partial_function_total (fun x => (f x+g x)%R)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (f x+g x)%R; split=> //.
  apply/partial_vector_add_graph; exists (f x),(g x); by split=> //; split.
rewrite -(@measure_lp_norm_almost_equal R X V N hN mu hm p _ _ hp hs.1 ht.1 he).
exact (@measure_lp_norm_triangle R X V N hN mu hm p _ _ hp hf hg).
Qed.

(** Source for [total_measurable_lp_norm]: the finite-p norm
    restricted to the actual vector space required by Federer's erratum
    p. 1, book p. 86 bottom, for 2.4.12. *)
Definition total_measurable_lp_norm (f : subspace_space A) :=
  measure_lp_norm mu N p (partial_function_total (subspace_val f)).

(** Source for [total_measurable_lp_norm_seminorm]: the complete corrected
    finite-p seminorm assertion in Federer 2.4.12, pp. 86-87 All three
    abstract seminorm laws hold, including infinite values and the
    convention zero times infinity equals zero. *)
Theorem total_measurable_lp_norm_seminorm : is_extended_seminorm total_measurable_lp_norm.
Proof.
constructor.
- move=> f; exact (@measure_lp_norm_nonnegative R X V N hN mu p _ hm hp (subspace_valP f).1).
- move=> c f; rewrite /total_measurable_lp_norm linearZ.
  exact (total_lp_norm_scale c (subspace_valP f)).
- move=> f g; rewrite /total_measurable_lp_norm linearD.
  exact (total_lp_norm_triangle (subspace_valP f) (subspace_valP g)).
Qed.
End TotalLp.
