(** Federer (1969), 3.2.13, p. 250: the
    signed derivative in the Gamma recurrence is
    summable after positive-ray completion. Its integral
    is the difference s Gamma(s)-Gamma(s+1),
    using only the proved defining Gamma integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EulerGammaUP EulerGamma EulerGammaMeasurable EulerGammaFinite
  EulerGammaPrimitiveDifferential LebesgueScalarMeasure MeasureUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureSubsetIntegral PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension SummableRealFunctionUP SummableRealArithmetic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euler_gamma_completed_integral]: the
    defining Gamma integral represented by its prescribed
    zero-completed real integrand, Federer 3.2.13, p. 250.
    This is a graph adapter, not a second Gamma definition. *)
Lemma euler_gamma_completed_integral (R:realType) (s:R) (hs:(0<s)%R):
  is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand (gamma_positive_completion s))
    (euler_gamma hs)%:E.
Proof.
apply:measure_integral_graph_equivalent _ (euler_gamma_integral hs)=>x z.
rewrite -(@gamma_positive_completion_subset_graph R s x z) real_total_integrand_graph.
by [].
Qed.

(** Source for [gamma_completed_derivative]: the positive-ray
    completion of the derivative of x^s exp(-x),
    supporting Gamma recurrence in Federer 3.2.13, p. 250.
    Its value outside the ray is explicitly zero. *)
Definition gamma_completed_derivative (R:realType) (s x:R):R:=
  (s*gamma_positive_completion s x-gamma_positive_completion (s+1) x)%R.

(** Source for [gamma_completed_derivative_on]: agreement
    with the actual derivative on the integration
    domain, Federer 3.2.13, p. 250. *)
Lemma gamma_completed_derivative_on (R:realType) (s x:R):
  (0<x)%R ->gamma_completed_derivative s x=euler_gamma_primitive_derivative s x.
Proof.
move=>hx; by rewrite /gamma_completed_derivative /gamma_positive_completion hx.
Qed.

(** Source for [gamma_completed_derivative_off]: zero completion
    outside the defining positive ray in the
    Gamma recurrence, Federer 3.2.13, p. 250. *)
Lemma gamma_completed_derivative_off (R:realType) (s x:R):
  ~ (0<x)%R ->gamma_completed_derivative s x=0%R.
Proof.
move=>hx; have hNot:(0<x)%R=false by apply/negP.
by rewrite /gamma_completed_derivative /gamma_positive_completion hNot mulr0 subrr.
Qed.

(** Source for [euler_gamma_completed_derivative_integral]: finite
    signed integral of the Gamma recurrence derivative,
    Federer 3.2.13, p. 250. No
    recurrence identity or vanishing endpoint is used
    in this arithmetic consequence of the defining integrals. *)
Lemma euler_gamma_completed_derivative_integral (R:realType) (s:R)
    (hs:(0<s)%R) (hs1:(0<s+1)%R):
  is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand (gamma_completed_derivative s))
    (s*euler_gamma hs-euler_gamma hs1)%R%:E.
Proof.
pose hm:=lebesgue_scalar_is_measure R.
have hFirst:=euler_gamma_completed_integral hs.
have hSecond:=euler_gamma_completed_integral hs1.
have hScaled:=@real_total_integral_scale R R (@lebesgue_scalar_measure R) hm
  (gamma_positive_completion s) (euler_gamma hs) s hFirst.
exact (@real_total_integral_subtract R R (@lebesgue_scalar_measure R) hm
  (fun x=>(s*gamma_positive_completion s x)%R) (gamma_positive_completion (s+1))
  (s*euler_gamma hs)%R (euler_gamma hs1) hScaled hSecond).
Qed.
