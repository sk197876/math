(** Federer (1969), 3.2.13, p. 250: the bounded square
    substitutions exhaust both nonnegative improper integrands. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal lra.
From Federer Require Import GammaSquareIntegrand GammaSquareSourceGraph GammaSquareTargetMultiplicity
  EulerGammaMeasurable EulerGammaBounds GammaDyadicExhaustion GeometricPowerBounds
  RealErrorOrderLimit ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [gamma_positive_completion_nonnegative]: nonnegativity
    of the defining Gamma integrand, Federer 3.2.13, p. 250. *)
Lemma gamma_positive_completion_nonnegative (R:realType) (s x:R):
  0<=gamma_positive_completion s x.
Proof.
rewrite /gamma_positive_completion; case:ifP=>hx; last exact:lexx.
exact:ltW (euler_gamma_integrand_positive s hx).
Qed.

(** Source for [gamma_square_zero_nonnegative]: the auxiliary
    origin completion of the Gaussian power is nonnegative,
    Federer 3.2.13, p. 250. *)
Lemma gamma_square_zero_nonnegative (R:realType) (s x:R):
  0<=gamma_square_zero_completion s x.
Proof.
rewrite /gamma_square_zero_completion; case:ifP=>hx; first exact:lexx.
exact:gamma_square_integrand_nonnegative.
Qed.

(** Source for [gamma_square_cutoffs_nonnegative]: both bounded
    square-substitution integrands are nonnegative, supporting
    increasing convergence in Federer 3.2.13, p. 250. *)
Lemma gamma_square_cutoffs_nonnegative (R:realType) (s b x:R):
  0<=gamma_square_source_cutoff s b x /\0<=gamma_square_target_cutoff s b x.
Proof.
have hTwo:0<=(2:R) by lra.
split; rewrite /gamma_square_source_cutoff /gamma_square_target_cutoff;
case:ifP=>hx; try exact:lexx; apply:mulr_ge0=>//.
- exact:gamma_square_zero_nonnegative.
- exact:gamma_positive_completion_nonnegative.
Qed.

(** Source for [gamma_square_cutoffs_monotone]: increasing
    dyadic cutoffs in the two square-substitution integrals,
    Federer 3.2.13, p. 250. *)
Lemma gamma_square_cutoffs_monotone (R:realType) (s x:R) n:
  gamma_square_source_cutoff s (2^+n) x<=gamma_square_source_cutoff s (2^+n.+1) x /\
  gamma_square_target_cutoff s (2^+n) x<=gamma_square_target_cutoff s (2^+n.+1) x.
Proof.
have hTwo:0<(2:R) by lra.
have hB:(2:R)^+n<= 2^+n.+1:=@gamma_dyadic_tail_monotone R n n.+1 (leqnSn n).
have hB0:0<=(2:R)^+n:=exprn_ge0 n (ltW hTwo).
have hC0:0<=(2:R)^+n.+1:=exprn_ge0 n.+1 (ltW hTwo).
have hSquare:((2:R)^+n)^+2<=(2^+n.+1)^+2 by nra.
split.
- rewrite /gamma_square_source_cutoff; case:ifP=>hx.
  + have hNext:`|x|<=(2:R)^+n.+1:=le_trans hx hB.
    by rewrite hNext.
  + exact:(gamma_square_cutoffs_nonnegative s ((2:R)^+n.+1) x).1.
- rewrite /gamma_square_target_cutoff; case:ifP=>hx.
  + have hNext:x<=((2:R)^+n.+1)^+2:=le_trans hx hSquare.
    by rewrite hNext.
  + exact:(gamma_square_cutoffs_nonnegative s ((2:R)^+n.+1) x).2.
Qed.

(** Source for [gamma_square_cutoffs_eventually_full]: every real
    point eventually belongs to both bounded square-substitution
    domains, Federer 3.2.13, p. 250. *)
Lemma gamma_square_cutoffs_eventually_full (R:realType) (s x:R):
  exists N,forall n,(N<=n)%N ->
    gamma_square_source_cutoff s (2^+n) x= 2*gamma_square_zero_completion s x /\
    gamma_square_target_cutoff s (2^+n) x= 2*gamma_positive_completion s x.
Proof.
have hTwo:1<(2:R) by lra.
have [N hN]:=geometric_powers_unbounded `|x| hTwo.
exists N=>n hn.
have hB: `|x|<(2:R)^+n:=lt_le_trans hN (@gamma_dyadic_tail_monotone R N n hn).
have hB1:1<=(2:R)^+n:=exprn_ege1 n (ltW hTwo).
have hx2:x<=((2:R)^+n)^+2 by have:=ler_norm x; nra.
split; rewrite /gamma_square_source_cutoff /gamma_square_target_cutoff.
- by rewrite (ltW hB).
- by rewrite hx2.
Qed.

(** Source for [gamma_square_cutoffs_pointwise_limit]: the two
    bounded integrands converge pointwise to the full improper
    integrands, Federer 3.2.13, p. 250. *)
Lemma gamma_square_cutoffs_pointwise_limit (R:realType) (s x:R):
  extended_order_limit (fun n=>(gamma_square_source_cutoff s (2^+n) x)%:E)
    (2*gamma_square_zero_completion s x)%:E /\
  extended_order_limit (fun n=>(gamma_square_target_cutoff s (2^+n) x)%:E)
    (2*gamma_positive_completion s x)%:E.
Proof.
have [N hN]:=gamma_square_cutoffs_eventually_full s x.
split; apply:real_error_extended_order_limit=>e he; exists N=>n hn.
- by rewrite (hN n hn).1 subrr normr0.
- by rewrite (hN n hn).2 subrr normr0.
Qed.
