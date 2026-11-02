(** Federer (1969), 2.10.46, p. 203, last paragraph: cover a rectangle by
    fixing a first-factor ball and covering its second factor at a smaller
    scale. This supporting lemma extracts the finite positive ball-volume
    coefficient using the abstract covering laws. Generator admissibility
    and its geometric cost bound remain separate proved inputs. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricProductRectangles MetricRectangleSliceMeasure
  MeasureUP MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleWeightedBound MetricScaleCutoffCost CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectangle_scale_second_factor_bound]: supporting
    second-factor covering step in 2.10.46, p. 203.
    The target remains at its prescribed cutoff; the second
    factor passes to its full Caratheodory measure. *)
Theorem rectangle_scale_second_factor_bound (R : realType) (P X Y : metricType R)
    (first : P -> X) (second : P -> Y) (S : set X)
    (J K : choiceType) (W : J -> set P) (w : J -> \bar R)
    (T : K -> set Y) (c : K -> \bar R) (u : K -> J)
    (delta eta : \bar R) (nu : set P -> \bar R) (mu : set Y -> \bar R) (a : R) :
  is_metric_scale_envelope W w delta nu -> (forall j, 0<=w j) ->
  is_caratheodory_limit T c mu -> 0<eta -> (0<a)%R ->
  (forall j, W (u j)=metric_product_rectangle first second S (T j)) ->
  (forall j, extended_metric_diameter (T j)<=eta -> extended_metric_diameter (W (u j))<=delta) ->
  (forall j, extended_metric_diameter (T j)<=eta -> w (u j)<=a%:E*c j) ->
  forall V, nu (metric_product_rectangle first second S V)<=a%:E*mu V.
Proof.
move=> hn hw hm heta ha hu hd hc V.
pose zeta := metric_scale_envelope T c eta.
have hz := metric_scale_envelope_specification T c eta.
have hnmeasure := metric_scale_envelope_is_measure hn hw.
have hslice := @metric_rectangle_second_slice_is_measure R P X Y first second S nu hnmeasure.
have hb : nu (metric_product_rectangle first second S V)<=a%:E*zeta V.
  apply: (@measure_bounded_by_scaled_metric_envelope R Y K T c eta zeta
    (fun B=>nu (metric_product_rectangle first second S B)) a hz hslice ha)=> j hj.
  rewrite -(hu j).
  exact: le_trans (@metric_scale_generator_bound R P J W w delta nu (u j) hn (hw _) (hd j hj)) (hc j hj).
apply: le_trans hb _; apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW ha.
exact (@caratheodory_limit_upper R Y K T c mu hm V eta zeta heta hz).
Qed.
