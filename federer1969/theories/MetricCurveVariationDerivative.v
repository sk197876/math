(** Federer (1969), 2.9.22, pp. 167–168: extend the variation conclusions of
    2.9.19(1), pp. 163–165. These arc-length identities are metric
    statements and require no vector or reflexivity hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  RealCurveDerivativeUP RealCurveDerivativeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.


(** Source for [metric_signed_variation_arc_length_increment]: supporting
    metric form of the signed-variation conclusion in Federer 2.9.22, pp.
    167–168, extending 2.9.19(1), pp. 163–165. The signed arc-length
    increment identity includes both orientations and retains the actual
    punctured limit. *)
Lemma metric_signed_variation_arc_length_increment (R : realType) (Y : metricType R)
    (g : R -> Y) : curve_locally_finite_variation g ->
  forall a b : R, signed_curve_variation g a b=(arc_length g b-arc_length g a)%:E.
Proof.
move=> hg a b; rewrite /signed_curve_variation; case: ifPn=> hab.
- symmetry; exact (@arc_length_increment R Y g hg a b hab).
- have hba : b<=a by rewrite leNgt; apply/negP=> hlt; have hab' := ltW hlt; by rewrite hab' in hab.
  rewrite -(@arc_length_increment R Y g hg b a hba) -EFinN.
  congr (_%:E); ring.
Qed.


(** Source for [metric_signed_variation_difference_quotient]: supporting
    metric form of the signed-variation conclusion in Federer 2.9.22, pp.
    167–168, extending 2.9.19(1), pp. 163–165. The signed arc-length
    increment identity includes both orientations and retains the actual
    punctured limit. *)
Lemma metric_signed_variation_difference_quotient (R : realType) (Y : metricType R)
    (g : R -> Y) : curve_locally_finite_variation g ->
  forall x h : R, fine (signed_curve_variation g x (x+h))/h=
    (arc_length g (x+h)-arc_length g x)/h.
Proof. by move=> hg x h; rewrite (metric_signed_variation_arc_length_increment hg). Qed.


(** Source for [metric_curve_variation_derivative_iff]: supporting metric
    form of the signed-variation conclusion in Federer 2.9.22, pp. 167–168,
    extending 2.9.19(1), pp. 163–165. The signed arc-length increment
    identity includes both orientations and retains the actual punctured
    limit. *)
Lemma metric_curve_variation_derivative_iff (R : realType) (Y : metricType R)
    (g : R -> Y) (x v : R) : curve_locally_finite_variation g ->
  (has_real_curve_derivative (arc_length g) x v <->
   punctured_real_limit (fun h => fine (signed_curve_variation g x (x+h))/h) v).
Proof.
move=> hg; split=> hl.
- apply: (@punctured_real_limit_congr R
    (fun h => (arc_length g (x+h)-arc_length g x)/h)); last exact hl.
  by move=> h _; rewrite (metric_signed_variation_difference_quotient hg).
- apply: (@punctured_real_limit_congr R
    (fun h => fine (signed_curve_variation g x (x+h))/h)); last exact hl.
  by move=> h _; rewrite (metric_signed_variation_difference_quotient hg).
Qed.
