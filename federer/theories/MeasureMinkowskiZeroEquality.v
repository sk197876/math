(** Federer (1969), 2.4.15, p. 89: degenerate zero-norm cases of the general
    equality criterion. Vanishing Lp norm gives almost-everywhere zero, and
    the coefficients zero and one then satisfy the printed condition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MinkowskiEqualityUP MeasureLpNorm MeasureLpZero MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_zero_left_equality_condition]: zero
    first-factor case of the norm-proportion condition in
    Federer 2.4.15, p. 89. The coefficients
    are zero and one, including when both norms vanish. *)
Lemma minkowski_zero_left_equality_condition (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N p f = 0 -> measure_almost_everywhere mu (partial_function_domain g) ->
  is_minkowski_equality_condition N mu f g.
Proof.
move=> hp hf hn hg.
have hz := @zero_lp_norm_almost_zero R X V N hN mu hm p f hp hf hn.
exists 0%R,1%R; split=> //; split=> //; split; first by rewrite add0r.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hz hg)).
move=> x [[u [hu hu0]] [v hv]]; exists u,v; split=> //; split=> //.
have hu0' : (0%R : V)=u := hu0.
by rewrite -hu0' add0r (real_seminorm_zero hN.1) mul0r mul1r.
Qed.

(** Source for [minkowski_zero_right_equality_condition]: zero
    second-factor case of the norm-proportion condition in
    Federer 2.4.15, p. 89. The coefficients
    are one and zero. *)
Lemma minkowski_zero_right_equality_condition (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> measure_almost_everywhere mu (partial_function_domain f) ->
  is_measure_measurable_function mu g -> measure_lp_norm mu N p g = 0 ->
  is_minkowski_equality_condition N mu f g.
Proof.
move=> hp hf hg hn.
have hz := @zero_lp_norm_almost_zero R X V N hN mu hm p g hp hg hn.
exists 1%R,0%R; split=> //; split=> //; split; first by rewrite addr0.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hf hz)).
move=> x [[u hu] [v [hv hv0]]]; exists u,v; split=> //; split=> //.
have hv0' : (0%R : V)=v := hv0.
by rewrite -hv0' addr0 (real_seminorm_zero hN.1) mul0r mul1r.
Qed.
