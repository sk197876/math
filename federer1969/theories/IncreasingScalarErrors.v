(** Federer (1969), 2.5.7, p. 98: finite-p increasing continuity follows
    from convergence of g-f_n to zero. Natural sequences start at zero here,
    so the majorant is g-f_0. These are supporting pointwise facts preceding
    integration. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealBoundsUP ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum RealErrorOrderLimit MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_order_limit_scalar_norm_sequence]: supporting
    identification of order convergence with scalar norm convergence in
    Federer 2.5.7, p. 98 *)
Lemma real_order_limit_scalar_norm_sequence (R : realType)
    (u : nat -> real_norm_metric_space (scalar_absolute_value_norm R))
    (z : real_norm_metric_space (scalar_absolute_value_norm R)) :
  extended_order_limit (fun n => (u n)%:E) z%:E -> u @ \oo --> z.
Proof.
move=> hl U /metricType_numDomainType.nbhs_mdistP [e he heU].
have [N hN] := @extended_finite_order_limit_error R u z e hl he.
exists N=> // n hn; apply: heU.
change (is_true (`|z-u n| < e)%R); rewrite distrC; exact: hN n hn.
Qed.

(** Source for [increasing_scalar_error_bounds]: supporting inequalities 0
    <= g-f_n <= g-f_0 in Federer 2.5.7, p. 98 *)
Lemma increasing_scalar_error_bounds (R : realType) (X : Type)
    (f : nat -> X -> R) (g : X -> R) :
  real_functions_increase_to f g ->
  forall n x, (0 <= g x-f n x <= g x-f 0%N x)%R.
Proof.
move=> hl n x; apply/andP; split.
- rewrite subr_ge0.
  have hh : (f n x)%:E <= (g x)%:E.
    apply: (extended_real_supremum_upper (extended_increasing_limit_supremum (hl x))).
    by exists n.
  by rewrite lee_fin in hh.
- rewrite lerD2l lerN2.
  have hh := (hl x).1 0%N n (leq0n n); by rewrite lee_fin in hh.
Qed.

(** Source for [increasing_scalar_error_limit]: supporting convergence of
    g-f_n to zero in Federer 2.5.7, p. 98 This is pointwise scalar
    convergence; norm convergence after integration is proved separately. *)
Lemma increasing_scalar_error_limit (R : realType) (X : Type)
    (f : nat -> X -> R) (g : X -> R) :
  real_functions_increase_to f g -> forall x,
  (fun n => ((g x-f n x)%R : real_norm_metric_space (scalar_absolute_value_norm R))) @ \oo --> (0%R : real_norm_metric_space (scalar_absolute_value_norm R)).
Proof.
move=> hl x; apply: real_order_limit_scalar_norm_sequence.
apply: real_error_extended_order_limit=> e he.
have [N hN] := @extended_finite_order_limit_error R (fun n => f n x) (g x) e (hl x).2 he.
exists N=> n hn; rewrite subr0 distrC; exact: hN n hn.
Qed.
