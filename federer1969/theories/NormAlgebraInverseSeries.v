(** Federer (1969), 3.1.11, p. 220:
    the inverse perturbation series (T+S)^(-1), with
    multiplication interpreted as composition in the operator
    application. The argument is valid in any complete
    normed associative algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import Hom AlgebraUP AlgebraPowers Bilinear RealNormUP NormMetric
  NormDifferentialUP NormBoundedLinearTopology CompleteMetricUP
  AlgebraInverseUP AlgebraGeometricSum NormAlgebraNeumann.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_algebra_inverse_perturbation_series]:
    the displayed inverse series in Federer 3.1.11,
    p. 220: powers of minus T^(-1)S, followed by
    T^(-1), converge to the two-sided inverse of T+S
    whenever the norm of T^(-1)S is less than one.
    The conclusion proves existence of that inverse. *)
Theorem norm_algebra_inverse_perturbation_series (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hN))
    (x v h : A) :
  is_two_sided_algebra_inverse x v -> N (alg_mul A v h)< 1 ->
  exists z : real_norm_metric_space hN,
    is_two_sided_algebra_inverse (x+h) z /\
    (fun n=>(alg_mul A (algebra_geometric_sum (-alg_mul A v h) n) v :
      real_norm_metric_space hN)) @ \oo --> z.
Proof.
move=> [hxv hvx] hh.
pose w := -alg_mul A v h.
have hw : N w< 1 by rewrite /w (real_seminorm_negate hN.1).
have [y [hy [hyl hyr]]] := @norm_algebra_neumann_series R A N hN hM hcomplete w hw.
pose K := alg_one A-w.
have hxK : alg_mul A x K=x+h.
  rewrite /K /w opprK (bilDr (alg_bilinear A)) alg_unitr
    alg_assoc hxv alg_unitl; by [].
have hvxh : alg_mul A v (x+h)=K.
  by rewrite /K /w opprK (bilDr (alg_bilinear A)) hvx.
exists (alg_mul A y v : real_norm_metric_space hN); split.
- split.
  + rewrite -hxK -alg_assoc (@alg_assoc R A K y v) hyl alg_unitl.
    exact hxv.
  + rewrite -alg_assoc hvxh; exact hyr.
- pose Mr := @HomMap R A A (fun z=>alg_mul A z v)
    (introT (asboolP _) ((alg_bilinear A).1 v)).
  have hMr : norm_bounded_linear N N Mr.
    exists (N v); split; first exact (real_seminorm_nonnegative hN.1 v).
    move=> z; rewrite mulrC; exact: hM z v.
  have hc := @norm_bounded_linear_continuous R A A N N hN hN Mr hMr.
  move=> U hU; exact: hy _ (hc y U hU).
Qed.
