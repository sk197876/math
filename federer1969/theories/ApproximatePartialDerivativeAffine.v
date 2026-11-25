(** Federer (1969), 3.1.2, p. 212: affine examples of the approximate
    partial derivative. The scalar increment quotient is constant off zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  RealNormUP NormMetric RealMetricBackground LebesgueScalarMeasure
  ScalarLebesgueBallContext PartialFunctionUP CenteredNullSetDensity
  ApproximatePartialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [approximate_partial_derivative_affine]: supporting
    affine case of ap D_i f(a), Federer 3.1.2, p. 212. It equals L(e_i)
    for f(x)=L(x)+c, with arbitrary normed target. *)
Theorem approximate_partial_derivative_affine (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (L : Hom (R_n R n) Y) (c : Y) a i :
  has_approximate_partial_derivative hNY setT (fun x=>L x+c) a i (L (@coordinate_basis R n i)).
Proof.
split=> //.
apply: (@centered_almost_constant_approximate_limit R
  [the metricType R of real_line_metric R]
  [the topologicalType of real_norm_metric_space hNY] (@lebesgue_scalar_measure R)
  (approximate_partial_quotient hNY setT (fun x=>L x+c) a i)
  [set 0] 0 (L (@coordinate_basis R n i))
  (lebesgue_scalar_is_measure R) _ (lebesgue_scalar_singleton 0)).
- move=> x r hr; split; first exact: scalar_lebesgue_positive_ball.
  by rewrite scalar_lebesgue_closed_ball ?ltW // fin_numE.
- move=> t hn; have ht : t!=0 by apply/eqP=> h; apply: hn; exact h.
  split; first by split.
  change (t^-1*:(L (a+t*:(@coordinate_basis R n i))+c-(L a+c))=
    L (@coordinate_basis R n i)).
  rewrite (linearD L a (t*:(@coordinate_basis R n i)))
    (linearZ_LR (hom_as_linear L) t (@coordinate_basis R n i)) /=
    opprD addrACA subrr addr0 addrAC subrr add0r.
  by rewrite scalerA mulVf // scale1r.
Qed.
