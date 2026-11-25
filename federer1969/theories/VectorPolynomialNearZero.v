(** Federer (1969), 3.1.11, p. 221:
    finite vector-valued polynomial coefficients can
    be compared using their behavior near zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP PolynomialCoefficientUniqueness
  NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [vector_polynomial_unit_interval_bound]:
    a finite polynomial is bounded for |t|<=1
    by the sum of its coefficient norms,
    supporting the coefficient identification in
    Federer 3.1.11, p. 221. *)
Lemma vector_polynomial_unit_interval_bound (R : realType)
    (Y : lmodType R) (N : Y->R) (hN : is_real_norm N) (s : seq Y) t :
  `|t|<=1 ->
  N (coefficient_polynomial_value s t)<=\sum_(c <- s) N c.
Proof.
move=>ht; elim:s=>[|c s ih].
- by rewrite /coefficient_polynomial_value /= big_nil (real_seminorm_zero hN.1).
- rewrite big_cons.
  change (N (c+t*:coefficient_polynomial_value s t)<=N c+\sum_(a <- s) N a).
  apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
  apply: lerD; first exact: lexx.
  rewrite (real_seminorm_scale hN.1).
  have hsum : 0<=\sum_(a <- s) N a.
    apply: sumr_ge0=>a _; exact (real_seminorm_nonnegative hN.1 a).
  have hh := le_trans (ler_wpM2l (normr_ge0 t) ih) (ler_wpM2r hsum ht).
  by rewrite mul1r in hh.
Qed.

(** Source for [vector_polynomial_zero_limit]:
    a vector-valued polynomial tends to its
    constant coefficient at zero, supporting
    Federer 3.1.11, p. 221.
    The finite norm bound proves this directly
    in an arbitrary normed target. *)
Theorem vector_polynomial_zero_limit (R : realType)
    (Y : lmodType R) (N : Y->R) (hN : is_real_norm N)
    (c : Y) (s : seq Y) :
  punctured_norm_limit N (coefficient_polynomial_value (c::s)) c.
Proof.
move=>e he.
pose C := \sum_(a <- s) N a.
have hC : 0<=C by apply: sumr_ge0=>a _; exact (real_seminorm_nonnegative hN.1 a).
have hCp : 0<C+1 by lra.
have hep : 0<e/(C+1) by rewrite divr_gt0.
exists (Num.min 1 (e/(C+1))); split; first by rewrite lt_min ltr01 hep.
move=>t /andP [ht0 ht].
have /andP [ht1 hte] : (`|t|<1)&&(`|t|<e/(C+1)) by rewrite -lt_min.
change (N ((c+t*:coefficient_polynomial_value s t)-c)<e).
rewrite addrAC subrr add0r (real_seminorm_scale hN.1).
have hb := vector_polynomial_unit_interval_bound hN s (ltW ht1).
have hle := ler_wpM2l (normr_ge0 t) hb.
have hCC : C<=C+1 by lra.
have hle2 := ler_wpM2l (normr_ge0 t) hCC.
apply: le_lt_trans (le_trans hle hle2) _.
by move: hte; rewrite ltr_pdivlMr.
Qed.
