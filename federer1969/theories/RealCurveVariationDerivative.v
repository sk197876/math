(** Federer (1969), 2.9.19, pp. 163–164: condition (1) identifies the
    derivative of the signed variation increment with the absolute
    derivative of g. The supporting identity uses s from 2.5.16, p. 109. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  RealCurveDerivativeUP RealCurveDerivativeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [signed_variation_arc_length_increment]: supporting identity
    V_a^b g=s(b)-s(a) used in Federer 2.9.19, p. 164, from 2.5.16, p. 109,
    including the printed negative orientation for a>b. Both orientations
    remain finite under locally finite variation; no infinite subtraction is
    used. *)
Lemma signed_variation_arc_length_increment (R : realType)
    (g : R -> real_line_metric R) : curve_locally_finite_variation g ->
  forall a b : R, signed_curve_variation g a b=(arc_length g b-arc_length g a)%:E.
Proof.
move=> hg a b; rewrite /signed_curve_variation; case: ifPn=> hab.
- symmetry; exact (@arc_length_increment R [the metricType R of real_line_metric R] g hg a b hab).
- have hba : b<=a by rewrite leNgt; apply/negP=> hlt; have hab' := ltW hlt; by rewrite hab' in hab.
  rewrite -(@arc_length_increment R [the metricType R of real_line_metric R] g hg b a hba) -EFinN.
  congr (_%:E); ring.
Qed.

(** Source for [signed_variation_difference_quotient]: the quotient
    V_x^(x+h)g/h in condition (1) of Federer 2.9.19, p. 163, equals the
    ordinary difference quotient of s. The identity is algebraic even at
    h=0; the limiting statement still excludes zero. *)
Lemma signed_variation_difference_quotient (R : realType)
    (g : R -> real_line_metric R) : curve_locally_finite_variation g ->
  forall x h : R, fine (signed_curve_variation g x (x+h))/h=
    (arc_length g (x+h)-arc_length g x)/h.
Proof. by move=> hg x h; rewrite (signed_variation_arc_length_increment hg). Qed.

(** Source for [real_curve_variation_derivative_iff]: supporting
    reformulation of condition (1) of Federer 2.9.19, p. 163, as
    s'(x)=|g'(x)| in its proof, pp. 164–165. This equivalence concerns any
    candidate finite variation-derivative value; its absolute- derivative
    value will be established by the theorem. *)
Lemma real_curve_variation_derivative_iff (R : realType)
    (g : R -> real_line_metric R) (x v : R) : curve_locally_finite_variation g ->
  (has_real_curve_derivative (arc_length g) x v <->
   punctured_real_limit (fun h => fine (signed_curve_variation g x (x+h))/h) v).
Proof.
move=> hg; split=> hl.
- apply: (@punctured_real_limit_congr R
    (fun h => (arc_length g (x+h)-arc_length g x)/h)); last exact hl.
  by move=> h _; rewrite (signed_variation_difference_quotient hg).
- apply: (@punctured_real_limit_congr R
    (fun h => fine (signed_curve_variation g x (x+h))/h)); last exact hl.
  by move=> h _; rewrite (signed_variation_difference_quotient hg).
Qed.
