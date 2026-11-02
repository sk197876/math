(** Regression examples for the inverse-function argument in Federer
    (1969), 3.1.1, p. 210, including its corrected iteration sign. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import TensorUP Hom RealNormUP NormMetric CompleteMetricUP
  NormDifferentialUP NormDifferentialLinear NormClassOneUP NormClassOneLaws
  NormLocalHomeomorphismUP NormClassOneInverseFunction InverseFunctionIteration
  InverseFunctionIterationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [affine_translation_local_inverse_regression]:
    supporting regression for the translations in Federer 3.1.1,
    p. 210. The theorem applies at any point of an affine translation
    on any complete normed space, including a zero-dimensional one. *)
Example affine_translation_local_inverse_regression (R : realType)
    (X : lmodType R) (N : X -> R) (hN : is_real_norm N)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (a b : X) :
  is_norm_local_homeomorphism hN hN (fun _ => True) (fun x => x+b) a.
Proof.
pose L : Hom X X := hom_of_linear (linear_id X).
have hL : forall v, L v=v by move=> v.
have hdiff : forall x, has_norm_differential N N (fun _ => True)
    (fun z => z+b) x L.
  move=> x; constructor.
  - exists 1; split; first exact: ltr01.
    by move=> h _.
  - exists 1; split; first exact: ler01.
    by move=> v; rewrite hL mul1r.
  - move=> e he; exists 1; split; first exact: ltr01.
    move=> h _ _; rewrite hL [x+h+b]addrAC [(x+b)+h-(x+b)]addrAC subrr add0r subrr
      (real_seminorm_zero hN.1).
    exact: mulr_ge0 (ltW he) (real_seminorm_nonnegative hN.1 h).
have hf : is_norm_class_one_field N N (fun _ => True) (fun x => x+b) (fun _ => L).
  constructor.
  - apply: (norm_everywhere_differentiable_class_zero hN)=> x _; exact: hdiff.
  - by move=> x _; exact: hdiff.
  - move=> x _ e he; exists 1; split; first exact: ltr01.
    move=> h _ _ v; rewrite subrr hom_zeroE (real_seminorm_zero hN.1).
    exact: mulr_ge0 (ltW he) (real_seminorm_nonnegative hN.1 v).
apply: (@norm_class_one_inverse_function R X X N N hN hN hcomplete
  (fun _ => True) (fun x => x+b) (fun _ => L) a L hf I).
- exists 1; split; first exact: ler01.
  by move=> v; rewrite hL mul1r.
- by move=> v; rewrite !hL.
- by move=> v; rewrite !hL.
Qed.

(** Source for [inverse_iteration_corrected_sign_regression]:
    Federer 3.1.1, p. 210 line 26, as corrected by the erratum, p. 4.
    For g(t)=t/2 and y=1 the first difference after u1 is negative:
    u2-u1=-1/2. This distinguishes the corrected order from the printed
    reversed difference without unfolding the private sequence witness. *)
Example inverse_iteration_corrected_sign_regression (R : realType) :
  let u := @inverse_function_iteration R R^o (fun t => t/2) 1 in
  u 2%N-u 1%N = -(1/2).
Proof.
move=> u.
have hu : @is_inverse_function_iteration R R^o (fun t => t/2) 1 u :=
  @inverse_function_iteration_specification R R^o (fun t => t/2) 1.
rewrite (inverse_iteration_step hu) (inverse_iteration_step hu)
  (inverse_iteration_zero hu) mul0r subr0.
by lra.
Qed.
