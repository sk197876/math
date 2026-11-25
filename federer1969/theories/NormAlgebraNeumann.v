(** Federer (1969), 3.1.11, p. 220:
    the Neumann series in a complete normed associative
    algebra. The proof uses the project's geometric Cauchy
    estimate and both finite telescoping identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import Hom AlgebraUP AlgebraPowers Bilinear RealNormUP NormMetric
  NormMetricSubtractContinuity NormDifferentialUP NormBoundedLinearTopology
  CompleteMetricUP NormGeometricIncrementLimit NormAlgebraPowers AlgebraGeometricSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_algebra_neumann_series]:
    the geometric inverse series used in Federer 3.1.11,
    p. 220. Norm less than one guarantees a norm
    limit that is a two-sided inverse of one minus the
    element. No commutativity or nonzero-unit hypothesis is used. *)
Theorem norm_algebra_neumann_series (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hN))
    (x : A) :
  N x< 1 ->
  exists y : real_norm_metric_space hN,
    (fun n=>(algebra_geometric_sum x n : real_norm_metric_space hN)) @ \oo --> y /\
    alg_mul A (alg_one A-x) y=alg_one A /\
    alg_mul A y (alg_one A-x)=alg_one A.
Proof.
move=> hx.
pose T := real_norm_metric_space hN.
pose c := (N x+1)/2.
have hn := real_seminorm_nonnegative hN.1 x.
have hc0 : 0<c by rewrite /c; lra.
have hc1 : c< 1 by rewrite /c; lra.
have hxc : N x<=c by rewrite /c; lra.
have hc : 0<c< 1 by apply/andP.
have hu := real_seminorm_nonnegative hN.1 (alg_one A).
have hinc n : N (algebra_geometric_sum x n.+1-algebra_geometric_sum x n)<=
    c^+n*N (alg_one A).
  rewrite algebra_geometric_sum_successor addrAC subrr add0r.
  exact (norm_algebra_power_bound hN hM (ltW hc0) hxc n).
have [y hy] := @norm_geometric_increments_converge R A N hN hcomplete
  (algebra_geometric_sum x) c (N (alg_one A)) hc hu hinc.
exists y; split; first exact hy.
have hpow := @norm_algebra_powers_vanish R A N hN hM x c hc hxc.
have hp := cvg_pair (cvg_cst (alg_one A : T)) hpow.
have hrest : (fun n=>(alg_one A-@AlgebraPowers.algebra_power R A x n : T)) @ \oo -->
    (alg_one A : T).
  have hh : (fun n=>(alg_one A-@AlgebraPowers.algebra_power R A x n : T)) @ \oo -->
      (alg_one A-0 : T).
    move=> W hW; exact: hp _ (@real_norm_metric_subtract_continuous R A N hN (alg_one A,0) W hW).
  by rewrite subr0 in hh.
pose Ml := @HomMap R A A (fun z=>alg_mul A (alg_one A-x) z)
  (introT (asboolP _) ((alg_bilinear A).2 (alg_one A-x))).
pose Mr := @HomMap R A A (fun z=>alg_mul A z (alg_one A-x))
  (introT (asboolP _) ((alg_bilinear A).1 (alg_one A-x))).
have hMl : norm_bounded_linear N N Ml.
  exists (N (alg_one A-x)); split; first exact (real_seminorm_nonnegative hN.1 (alg_one A-x)).
  exact: hM _.
have hMr : norm_bounded_linear N N Mr.
  exists (N (alg_one A-x)); split; first exact (real_seminorm_nonnegative hN.1 (alg_one A-x)).
  move=> z; rewrite mulrC; exact: hM z _.
have hcl := @norm_bounded_linear_continuous R A A N N hN hN Ml hMl.
have hcr := @norm_bounded_linear_continuous R A A N N hN hN Mr hMr.
have hleft : (fun n=>(Ml (algebra_geometric_sum x n) : T)) @ \oo --> (Ml y : T).
  move=> W hW; exact: hy _ (hcl y W hW).
have hright : (fun n=>(Mr (algebra_geometric_sum x n) : T)) @ \oo --> (Mr y : T).
  move=> W hW; exact: hy _ (hcr y W hW).
have hel : (fun n=>(Ml (algebra_geometric_sum x n) : T))=
    (fun n=>(alg_one A-@AlgebraPowers.algebra_power R A x n : T)).
  apply: funext=> n; exact: algebra_geometric_sum_left.
have her : (fun n=>(Mr (algebra_geometric_sum x n) : T))=
    (fun n=>(alg_one A-@AlgebraPowers.algebra_power R A x n : T)).
  apply: funext=> n; exact: algebra_geometric_sum_right.
rewrite hel in hleft; rewrite her in hright.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have PFr : ProperFilter
    ((fun n=>(alg_one A-@AlgebraPowers.algebra_power R A x n : T)) @ \oo) :=
  @fmap_proper_filter nat T
    (fun n=>(alg_one A-@AlgebraPowers.algebra_power R A x n : T)) \oo PF0.
split.
- exact: (@cvg_unique T (@metric_hausdorff R T) _ PFr (Ml y) (alg_one A) hleft hrest).
- exact: (@cvg_unique T (@metric_hausdorff R T) _ PFr (Mr y) (alg_one A) hright hrest).
Qed.
