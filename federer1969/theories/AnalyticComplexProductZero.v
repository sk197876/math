(** Federer (1969), 3.4.12, p. 339:
    the original holomorphic germ ring has no proper
    zero divisors. Reuse the already proved real scalar
    product-zero theorem on the actual squared moduli;
    do not repeat its analytic identity argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexModulus ComplexScalarNorm NormMetric NormAnalyticUP
  NormAnalyticComplexSquareModulus AnalyticProductZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [analytic_complex_product_zero_connected]: a
    zero complex product on an actual connected analytic
    domain has an identically zero original factor,
    supporting 3.4.12, p. 339. The argument
    uses the existing real theorem directly through squared moduli. *)
Theorem analytic_complex_product_zero_connected (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) (f g:X->ComplexScalars.C R):
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A f ->
  @norm_analytic R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A g ->
  (forall x,A x ->f x*g x=0) ->
  (forall x,A x ->f x=0) \/(forall x,A x ->g x=0).
Proof.
move=>hConnected hF hG hProduct.
have hSquareProduct x (hx:A x):norm_square (f x)*norm_square (g x)=0.
  by rewrite -complex_norm_square_mul (hProduct x hx) /norm_square re_zero im_zero !expr0n add0r.
have hAlternative:=@analytic_product_zero_connected R X NX hNX A
  (fun x=>norm_square (f x)) (fun x=>norm_square (g x)) hConnected
  (norm_analytic_complex_square_modulus hF) (norm_analytic_complex_square_modulus hG)
  hSquareProduct.
case:hAlternative=>hFactor;[left|right]=>x hx;apply/eqP;
  by rewrite -norm_square_eq0 (hFactor x hx) eqxx.
Qed.
