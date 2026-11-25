(** Federer (1969), 3.2.13, p. 250: the
    derivative of x^s exp(-x) is continuous
    on the positive ray, so the project's
    proved fundamental theorem applies on positive segments. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground EulerGammaUP EulerGammaMeasurable
  EulerGammaPrimitiveDifferential ScalarPositiveClassZero NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euler_gamma_primitive_derivative_continuous_at]:
    local continuity needed in the integration-by-parts
    calculation for Gamma, Federer 3.2.13, p. 250.
    It follows from the two actual positive-domain
    Gamma integrands and scalar arithmetic. *)
Lemma euler_gamma_primitive_derivative_continuous_at (R:realType) (s a:R):
  0<a ->(fun x:real_line_metric R=>(euler_gamma_primitive_derivative s x:real_line_metric R))
    @ a -->(euler_gamma_primitive_derivative s a:real_line_metric R).
Proof.
move=>ha.
have hFirst:=@euler_gamma_integrand_continuous_at R s a ha.
have hSecond:=@euler_gamma_integrand_continuous_at R (s+1) a ha.
change ((fun x:R^o=>s*euler_gamma_integrand s x-euler_gamma_integrand (s+1) x)
  @ (a:R^o) -->(s*euler_gamma_integrand s a-euler_gamma_integrand (s+1) a:R^o)).
have hConst:(fun x:R^o=>s) @ (a:R^o) -->(s:R^o) by exact:cvg_cst.
exact (cvgB (cvgM hConst hFirst) hSecond).
Qed.

(** Source for [euler_gamma_primitive_derivative_class_zero]:
    intrinsic class-zero law for the derivative in
    the Gamma recurrence, Federer 3.2.13, p. 250.
    The actual positive domain is retained; no
    continuity across the singular origin is asserted. *)
Lemma euler_gamma_primitive_derivative_class_zero (R:realType) (s:R):
  norm_class_zero (fun r:R^o=>`|r|) (fun r:R^o=>`|r|) (fun r=>0<r)
    (euler_gamma_primitive_derivative s).
Proof.
apply:scalar_positive_continuity_class_zero=>a ha.
exact:euler_gamma_primitive_derivative_continuous_at ha.
Qed.
