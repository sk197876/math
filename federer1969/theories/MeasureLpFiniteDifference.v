(** Federer (1969), 2.4.12, p. 87: finite-norm membership of the Cauchy
    limit. We use addition closure and almost equality, keeping the book's
    partial domains; the total-domain correction in the erratum concerns the
    separate vector-space assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasurableNormedArithmetic MeasurableNormedDifference MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureLpNorm MeasureLpNormScale MeasureLpNormAlmostEquality MeasureLpSumMembership MeasureLpConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_lp_distance_finite_norm]: supporting
    membership step for Federer 2.4.12, p. 87. If f
    has finite norm and f-g has finite norm, then g has finite
    norm. Addition closure proves this also at p=1, before a
    separate triangle-inequality statement is needed. *)
Lemma finite_lp_distance_finite_norm (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  measure_lp_norm mu N p f < +oo -> measure_lp_distance mu N p f g < +oo ->
  measure_lp_norm mu N p g < +oo.
Proof.
move=> hp hf hg hfn hdn.
pose d := partial_vector_subtract f g.
pose z := partial_vector_scale (-1)%R d.
have hd := @measurable_normed_function_subtract R X V N hN mu hm f g hf hg.
have hz := @measurable_normed_function_scale R X V N hN mu hm (-1)%R d hd.
have hzn : measure_lp_norm mu N p z < +oo.
  rewrite /z (@measure_lp_norm_scale R X V N hN mu hm p (-1)%R d hp hd.1) normrN1 mul1e.
  exact hdn.
have hflp : is_measure_lp_function mu p f.
  split=> //; split=> //; split=> //.
  exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p f hp hf.1 hfn).
have hzlp : is_measure_lp_function mu p z.
  split=> //; split=> //; split=> //.
  exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p z hp hz.1 hzn).
have hs := @measure_lp_function_add R X V N hN mu hm p f z hflp hzlp.
have he : measure_almost_equal mu (partial_vector_add f z) g.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _
      (measurable_function_domain hf.1) (measurable_function_domain hg.1))).
  move=> x [[a ha] [b hb]]; exists b; split=> //.
  apply/partial_vector_add_graph; exists a,(-(a-b))%R; split=> //; split.
  - apply/partial_vector_scale_graph; exists (a-b)%R; split.
    + apply/partial_vector_subtract_graph; exists a,b; by split=> //; split.
    + by rewrite scaleN1r.
  - by rewrite opprB addrC subrK.
have hn := @measure_lp_norm_almost_equal R X V N hN mu hm p _ g hp hs.2.1.1 hg.1 he.
by rewrite -hn; exact hs.2.2.1.
Qed.

(** Source for [lp_norm_limit_finite]: supporting finite-norm
    conclusion for the limit in Federer 2.4.12, p. 87.
    A single sufficiently late term and its finite error suffice. *)
Lemma lp_norm_limit_finite (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (forall n, is_measurable_normed_function mu (f n)) ->
  is_measurable_normed_function mu g -> (forall n, measure_lp_norm mu N p (f n) < +oo) ->
  converges_in_lp_norm mu N p f g -> measure_lp_norm mu N p g < +oo.
Proof.
move=> hp hf hg hfn hc; have [K hK] := hc 1%R ltr01.
apply: (@finite_lp_distance_finite_norm R X V N hN mu hm p (f K) g hp (hf K) hg (hfn K)).
exact: lt_trans (hK K (leqnn K)) (ltry (1%R)).
Qed.
