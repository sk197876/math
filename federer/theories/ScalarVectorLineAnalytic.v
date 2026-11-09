(** Federer (1969), 3.4.5, p. 321: actual
    scalar lines into the ambient Banach space are analytic,
    supporting the axis coefficient functions in the cited
    example. This is 3.1.24's bounded-linear case, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP
  NormDifferentialScalar NormOpenDomainLaws NormAnalyticUP NormAnalyticLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_vector_line_analytic]: the actual
    line t maps to t*v is analytic on the whole real
    line, supporting the example cited in 3.4.5, p. 321.
    The vector v may be zero and no dimension assumption is used. *)
Lemma scalar_vector_line_analytic (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (v:X):
  @norm_analytic R R^o X (fun t=>`|t|) NX (@scalar_absolute_value_norm R) hNX
    setT (fun t=>t*:v).
Proof.
have hBound:norm_bounded_linear (fun t:R^o=>`|t|) NX (@scalar_coefficient_linear_map R X v).
  exists (NX v);split;first exact:(real_seminorm_nonnegative hNX.1 v).
  by move=>t;rewrite (real_seminorm_scale hNX.1) mulrC.
exact:(@norm_bounded_linear_analytic R R^o X (fun t=>`|t|) NX (@scalar_absolute_value_norm R)
  hNX setT (fun t _=>norm_full_domain_interior _ t) (@scalar_coefficient_linear_map R X v) hBound).
Qed.
