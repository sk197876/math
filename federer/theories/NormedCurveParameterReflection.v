(** Federer (1969), 3.2.46, p. 281: reversal of a genuine
    Lipschitz curve, using the actual scalar and vector chain
    rules of 2.9.22, p. 168. The following derivative laws
    preserve the original two-sided derivative graphs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra ring.
From Federer Require Import RealNormUP RealCurveDerivativeUP
  NormedCurveDerivativeUP NormedCurveChainRule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_reflection_actual_derivative]: the
    parameter c-t has actual derivative -1, supporting reversal
    in Federer 3.2.46, p. 281, by 2.9.22, p. 168. *)
Lemma scalar_reflection_actual_derivative (R : realType) (c t : R) :
  has_real_curve_derivative (fun s=>c-s) t (-1).
Proof.
move=> e he; exists 1; split; first exact: ltr01.
move=> h /andP [hh hSmall].
have hne : h != 0 by rewrite -normr_gt0.
have hZero : (c-(t+h)-(c-t))/h-(-1) = 0 by field; rewrite (negbTE hne).
by rewrite hZero normr0.
Qed.

(** Source for [normed_curve_parameter_reflection]: the
    derivative of t |-> C(c-t) is -C'(c-t), supporting the
    symmetry of the distance in Federer 3.2.46, p. 281.
    This is a consequence of the proved norm chain rule. *)
Lemma normed_curve_parameter_reflection (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (C : R -> E) (c t : R) v :
  has_normed_curve_derivative N C (c-t) v ->
  has_normed_curve_derivative N (fun s=>C (c-s)) t (-v).
Proof.
move=> hC.
have h := @normed_curve_derivative_compose R E N hN C
  (fun s=>c-s) t (-1) v (scalar_reflection_actual_derivative c t) hC.
by rewrite scaleN1r in h.
Qed.

(** Source for [normed_curve_reflection_derivative_iff]: reversal
    preserves exactly the actual derivative domain, supporting
    equality of the two curve integrals in Federer 3.2.46,
    p. 281. Apply the same reversal twice, rather than assigning
    values at nondifferentiability points. *)
Lemma normed_curve_reflection_derivative_iff (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (C : R -> E) (c t : R) v :
  has_normed_curve_derivative N (fun s=>C (c-s)) t v <->
  has_normed_curve_derivative N C (c-t) (-v).
Proof.
have hInv s : c-(c-s)=s by ring.
split=> hC.
- have hAt : has_normed_curve_derivative N (fun s=>C (c-s)) (c-(c-t)) v.
    by rewrite hInv.
  have h := @normed_curve_parameter_reflection R E N hN (fun s=>C (c-s)) c (c-t) v hAt.
  have he : (fun s=>C (c-(c-s))) = C by apply: funext=> s; rewrite hInv.
  by rewrite he in h.
- have h := @normed_curve_parameter_reflection R E N hN C c t (-v) hC.
  by rewrite opprK in h.
Qed.
