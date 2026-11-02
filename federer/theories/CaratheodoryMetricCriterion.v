(** Federer (1969), 2.3.2(9), p. 75: Caratheodory's metric criterion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableSeparationUP MeasurableMetricCriterion MeasurableIdentityCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_separated_identity_iff]: supporting
    identity-map specialization of (8) used to obtain Federer
    2.3.2(9), p. 75. Intersecting two separated sets with
    an arbitrary test set preserves their uniform separation. *)
Lemma metric_separated_identity_iff (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_measure_image_separated mu (partial_function_total (fun x : X => x)) <->
  is_metric_separated_measure mu.
Proof.
split.
- move=> hs A B hab.
  have h := hs (A `|` B) A B hab.
  rewrite !partial_function_total_preimage /= in h.
  have hA : (A `|` B) `&` A = A by apply/seteqP; split=> x; [by move=> [_ hx]|by move=> hx; split; [left|]].
  have hB : (A `|` B) `&` B = B by apply/seteqP; split=> x; [by move=> [_ hx]|by move=> hx; split; [right|]].
  by rewrite hA hB in h.
- move=> hs T A B [delta [hp hab]].
  rewrite !partial_function_total_preimage /=.
  have hsep : metric_sets_positively_separated (T `&` A) (T `&` B).
    exists delta; split=> // x [_ hx] y [_ hy]; exact: hab x hx y hy.
  apply: le_trans (hs _ _ hsep) _.
  apply: (@measure_mono R X mu hm)=> x [[hx _]|[hx _]]; exact hx.
Qed.

(** Source for [caratheodory_metric_open_measurability_iff]: direct
    Caratheodory criterion (9) of Federer 2.3.2, p. 75 No separability or
    finiteness of the measure or metric space is required. *)
Theorem caratheodory_metric_open_measurability_iff (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  (forall U, open U -> measure_measurable mu U) <-> is_metric_separated_measure mu.
Proof.
have hd : measure_almost_everywhere mu
    (partial_function_domain (partial_function_total (fun x : X => x))).
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
rewrite -(@measurable_identity_iff_open_sets R X mu hm).
rewrite (@measurable_metric_image_separation_iff R X X mu hm _ hd).
exact: metric_separated_identity_iff hm.
Qed.
