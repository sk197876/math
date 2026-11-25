(** Federer (1969), 3.2.7, p. 246:
    elementary scalar derivative algebra for the explicit
    oscillatory example. Use only actual derivatives and
    this project's already proved normed chain rule. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealNormUP RealCurveDerivativeUP RealCurveDerivativeLaws PuncturedRealLinearLimits
  NormedCurveDerivativeUP NormedCurveChainRule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_curve_derivative_scale]: supporting
    scalar multiplication rule for the third example
    of Federer 3.2.7, p. 246. It follows
    directly from the actual punctured quotient limits. *)
Lemma real_curve_derivative_scale (R:realType) (f:R->R) (a v c:R):
  has_real_curve_derivative f a v ->
  has_real_curve_derivative (fun x=>c*f x) a (c*v).
Proof.
move=>hD.
apply:(@punctured_real_limit_congr R (fun h=>c*((f (a+h)-f a)/h))).
- move=>h _; ring.
- exact (punctured_real_limit_scale c hD).
Qed.

(** Source for [real_curve_derivative_compose]: supporting
    chain rule for the square-root parameter and sine
    argument in Federer 3.2.7, p. 246.
    The zero inner derivative is included and no
    nonzero-increment division is added as a hypothesis. *)
Lemma real_curve_derivative_compose (R:realType) (f g:R->R) (a v w:R):
  has_real_curve_derivative f a v -> has_real_curve_derivative g (f a) w ->
  has_real_curve_derivative (fun x=>g (f x)) a (v*w).
Proof.
move=>hF hG.
have hN:has_normed_curve_derivative (fun t:R^o=>`|t|) g (f a) w.
  exact ((scalar_normed_curve_derivative g (f a) w).2 hG).
have hC:=@normed_curve_derivative_compose R R^o (fun t=>`|t|) (@scalar_absolute_value_norm R)
  g f a v w hF hN.
change (has_normed_curve_derivative (fun t:R^o=>`|t|) (fun x=>g (f x)) a (v*w)) in hC.
exact ((scalar_normed_curve_derivative _ _ _).1 hC).
Qed.
