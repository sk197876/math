(** Federer (1969), 3.1.24, p. 241: local correction
    to the displayed absolute-series bound. Condition (1) bounds
    positive derivatives only. The degree-zero term must retain
    |f(a)|, rather than the printed implicit bound one. The
    retained erratum has no entry correcting this display. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra NormAnalyticUP NormScalarDerivativeAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_constant_analytic_at]: the constant
    function is analytic with bound zero on every positive
    derivative, as permitted by condition (1), Federer
    3.1.24, p. 237. This supplies the counterexample
    to the unrestricted degree-zero bound on p. 241. *)
Theorem scalar_constant_analytic_at (R:realType) (c a:R) :
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) (fun _=>True) (fun _=>c) a.
Proof.
pose F:=fun m:nat=>fun _:R=>if m is 0%N then c else 0.
have hN:=scalar_absolute_value_norm R.
have hOpen x:norm_domain_interior (fun t:R^o=>`|t|) (fun _=>True) x.
  exists 1; split; first exact ltr01; by move=>v hv.
have hF m x (_:True):has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    (fun _=>True) (F m) x (@scalar_coefficient_linear_map R R^o (F m.+1 x)).
  rewrite /F scalar_coefficient_linear_zero.
  case:m=>[|m]; exact (@norm_differential_constant R R^o R^o
    (fun t=>`|t|) (fun t=>`|t|) hN hN (fun _=>True) x _ (hOpen x)).
have hb m (hm:(1<=m)%N) x (_:True):`|F m x|<=0^+m*(m`!)%:R.
  case:m hm=>[|m] hm; first by [].
  by rewrite /F normr0 expr0n mul0r.
exact (@norm_scalar_derivative_analytic_at R (fun _=>True) F a 0 Logic.I hF hb).
Qed.

(** Source for [analytic_printed_constant_term_bound_fails]:
    local counterexample to Federer 3.1.24, p. 241,
    first display. The analytic constant function two has
    constant Taylor term of norm two, whereas the printed
    degree-zero geometric majorant is one for every c.
    This correction does not change absolute convergence. *)
Theorem analytic_printed_constant_term_bound_fails (R:realType) (c:R) :
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) (fun _=>True) (fun _=>2) 0 /\
  ~(`|2:R|<=c^+0*(0:R)^+0).
Proof.
split; first exact (scalar_constant_analytic_at (R:=R) 2 0).
rewrite !expr0 mul1r normr_nat=>h; lra.
Qed.
