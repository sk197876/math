(** Normed-space topology supporting the pseudodistance in Federer (1969),
    2.3.8, p. 78. Source context: NormMetricContinuity.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_product_maps]: supporting general-
    topology rule for subtraction in Federer 2.3.8, p. 78:
    the product of two continuous maps is continuous. *)
Lemma continuous_product_maps (T U Y Z : topologicalType) (f : T -> Y) (g : U -> Z) :
  continuous f -> continuous g -> continuous (fun p : T*U => (f p.1,g p.2)).
Proof.
move=> hf hg [x y] W [[A B] [hA hB] hAB].
exists ((fun a => A (f a)), (fun b => B (g b))).
- split; [exact: hf x A hA|exact: hg y B hB].
- move=> [a b] [ha hb]; apply: hAB; by split.
Qed.

(** Source for [real_norm_metric_subtract_continuous]: continuity of the
    subtraction map used for the measurable pseudodistance in Federer 2.3.8,
    p. 78 *)
Lemma real_norm_metric_subtract_continuous (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) :
  continuous (fun p : real_norm_metric_space hN * real_norm_metric_space hN =>
    (p.1-p.2 : real_norm_metric_space hN)).
Proof.
have hneg : continuous (fun x : real_norm_metric_space hN => (-x : real_norm_metric_space hN)).
  have -> : (fun x : real_norm_metric_space hN => -x) = (fun x => (-1 : R) *: x).
    by apply: funext=> x; rewrite scaleN1r.
  exact: real_norm_metric_scale_continuous.
have hid : continuous (fun x : real_norm_metric_space hN => x) by move=> x W hw.
have hp := @continuous_product_maps
  [the topologicalType of real_norm_metric_space hN]
  [the topologicalType of real_norm_metric_space hN]
  [the topologicalType of real_norm_metric_space hN]
  [the topologicalType of real_norm_metric_space hN] (fun x => x) (fun x => -x) hid hneg.
move=> p W hw.
exact: (hp p _ (@real_norm_metric_add_continuous R V N hN (p.1,-p.2) W hw)).
Qed.
