(** Federer (1969), 2.4.14, p. 88: degenerate zero-norm cases of Holder's
    inequality. These supporting integral identities preserve the common
    partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialNormProduct MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAlmostEquality MeasureDensityNullSets MeasureLpZero MeasureLpNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [norm_product_almost_zero_left]: supporting
    vanishing-product case in Federer 2.4.14, p. 88.
    The first factor vanishes almost everywhere and the second
    has a conull domain; no norm bound on it is required. *)
Lemma norm_product_almost_zero_left (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X V) (g : partial_function X W) :
  measure_almost_equal mu f (partial_function_total (fun _ : X => (0%R : V))) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  is_measure_integral mu (partial_norm_product N M f g) 0.
Proof.
move=> hf hg.
apply: (@measure_integral_almost_equal R X mu hm _ _ 0 (@measure_extended_zero_integral R X mu hm)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hf hg)).
move=> x [[a [ha ha0]] [b hb]]; exists 0; split=> //.
apply/(@partial_norm_product_graph R X V W N M hN hM).
exists a,b; split=> //; split=> //.
have ha0' : (0%R : V)=a := ha0.
by rewrite -ha0' (real_seminorm_zero hN.1) mul0r.
Qed.

(** Source for [norm_product_almost_zero_right]: the symmetric
    vanishing-product case supporting Federer 2.4.14, p. 88;
    no values are supplied outside the original domains. *)
Lemma norm_product_almost_zero_right (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X V) (g : partial_function X W) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_equal mu g (partial_function_total (fun _ : X => (0%R : W))) ->
  is_measure_integral mu (partial_norm_product N M f g) 0.
Proof.
move=> hf hg.
apply: (@measure_integral_almost_equal R X mu hm _ _ 0 (@measure_extended_zero_integral R X mu hm)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hf hg)).
move=> x [[a ha] [b [hb hb0]]]; exists 0; split=> //.
apply/(@partial_norm_product_graph R X V W N M hN hM).
exists a,b; split=> //; split=> //.
have hb0' : (0%R : W)=b := hb0.
by rewrite -hb0' (real_seminorm_zero hM.1) mulr0.
Qed.
