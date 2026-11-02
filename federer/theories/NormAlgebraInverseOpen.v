(** Federer (1969), 3.1.11, p. 220:
    invertibility is open in the operator norm. The
    neighbourhood is obtained from the proved perturbation
    series, not from an assumed inverse nearby. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology lra.
From Federer Require Import AlgebraUP RealNormUP NormMetric CompleteMetricUP
  PartialFunctionUP AlgebraInverseUP AlgebraInverse NormDifferentialUP
  NormBoundedLinearTopology NormAlgebraInverseSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_algebra_inverse_domain_interior]:
    an invertible element has an invertible neighbourhood,
    Federer 3.1.11, p. 220. The radius
    1/(norm of the inverse + 1) also covers a zero algebra. *)
Lemma norm_algebra_inverse_domain_interior (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hN))
    (x v : A) :
  is_two_sided_algebra_inverse x v ->
  norm_domain_interior N (partial_function_domain (algebra_inverse A)) x.
Proof.
move=> hv.
have hn := real_seminorm_nonnegative hN.1 v.
have hden : 0<N v+1 by lra.
exists ((N v+1)^-1); split; first by rewrite invr_gt0.
move=> h hh.
have hscale : (N v+1)*N h< 1.
  by move: hh; rewrite -div1r ltr_pdivlMr // mulrC.
have hnH := real_seminorm_nonnegative hN.1 h.
have hsmall : N (alg_mul A v h)< 1.
  apply: le_lt_trans (hM v h) _; nra.
have [z [hz _]] := @norm_algebra_inverse_perturbation_series R A N hN hM hcomplete x v h hv hsmall.
apply/algebra_inverse_domain; by exists z.
Qed.

(** Source for [norm_algebra_inverse_domain_open]:
    the automorphism set A is open in the Banach
    operator space E, Federer 3.1.11, p. 220.
    The theorem is stated for the supporting abstract algebra. *)
Theorem norm_algebra_inverse_domain_open (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hN)) :
  open [set x : real_norm_metric_space hN | partial_function_domain (algebra_inverse A) x].
Proof.
rewrite openE=> x hx.
have [v hv] := (algebra_inverse_domain x).1 hx.
have hi := @norm_algebra_inverse_domain_interior R A N hN hM hcomplete x v hv.
exact ((norm_domain_interior_neighbourhood hN (partial_function_domain (algebra_inverse A)) x).1 hi).
Qed.
