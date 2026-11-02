(** Federer (1969), proof of 2.4.6, p. 84: the finite test sum built from
    positive weights and measurable sets. Disjointness is unnecessary for
    this integral identity; it is used separately for pointwise domination
    by the sequence. Source context: ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic
  CharacteristicFunctionUP MeasureStepIntegralIdentification MeasureIntegralUP
  MeasureUpperIntegralScale MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence
  MeasureCharacteristicIntegral MeasureFiniteRealSumIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_scale_embedding_graph]: supporting
    graph identity for a weighted characteristic function in
    Federer 2.4.6, p. 84. *)
Lemma real_total_scale_embedding_graph (R : realType) (X : Type)
    (c : R) (u : X -> real_line_metric R) x y :
  partial_function_graph (partial_extended_function_scale c
    (partial_real_function_embed (partial_function_total u))) x y <->
  partial_function_graph (partial_real_function_embed
    (partial_function_total (fun x => ((c*u x)%R : real_line_metric R)))) x y.
Proof.
split.
- move=> [z [[r [hr erz]] ezy]]; exists (c*u x)%R; split=> //.
  by rewrite -(hr : u x = r) in erz; rewrite -erz -EFinM in ezy.
- move=> [r [hr ery]]; exists (u x)%:E; split; first by exists (u x); split.
  by rewrite -EFinM hr ery.
Qed.

(** Source for [measure_positive_characteristic_integral]: the
    single weighted term used in Federer 2.4.6, p. 84;
    its measure and integral may be infinite. *)
Lemma measure_positive_characteristic_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) (c : R) :
  is_characteristic_function A s -> measure_measurable mu A -> (0 < c)%R ->
  is_measure_integral mu (partial_real_function_embed
    (partial_function_total (fun x => ((c*s x)%R : real_line_metric R)))) (c%:E*mu A).
Proof.
move=> hs hA hc.
have hi := @measure_integral_positive_scale R X mu hm c _ (mu A) hc
  (@measure_characteristic_integral R X mu hm A s hs hA).
exact: measure_integral_graph_equivalent (real_total_scale_embedding_graph c s) hi.
Qed.

(** Source for [measure_finite_positive_characteristic_integral]: integral
    identity for the finite simple test function in Federer 2.4.6, p. 84 *)
Lemma measure_finite_positive_characteristic_integral (R : realType) (X : choiceType) (I : eqType)
    (mu : set X -> \bar R) (hm : is_measure mu) (s : seq I)
    (A : I -> set X) (v : I -> X -> real_line_metric R) (c : I -> R) :
  (forall i, i \in s -> is_characteristic_function (A i) (v i)) ->
  (forall i, i \in s -> measure_measurable mu (A i)) ->
  (forall i, i \in s -> (0 < c i)%R) ->
  is_measure_integral mu (partial_real_function_embed
    (partial_function_total (fun x => ((\sum_(i <- s) c i*v i x)%R : real_line_metric R))))
    (\sum_(i <- s) (c i)%:E*mu (A i)).
Proof.
move=> hv hA hc; apply: (@measure_finite_real_sum_integral R X I mu hm s
  (fun i x => ((c i*v i x)%R : real_line_metric R)) (fun i => (c i)%:E*mu (A i))).
- move=> i hi; apply: mule_ge0; first by rewrite lee_fin; exact: ltW (hc i hi).
  exact: measure_nonnegative.
- move=> i hi; exact (@measure_positive_characteristic_integral R X mu hm (A i) (v i) (c i)
    (hv i hi) (hA i hi) (hc i hi)).
Qed.
