(** Federer (1969), 3.1.24, p. 238: uniform
    Taylor convergence is uniform homogeneous polynomial convergence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity NormClassZeroTopology
  ContinuousMultilinearSealed NormAnalyticUP NormTaylorHomogeneousCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_taylor_analytic_polynomial]: the implication
    (3) to (4) in Federer 3.1.24, p. 238.
    The homogeneous functions are exactly the normalized actual
    differential coefficients in the given Taylor series; hence
    its original uniform convergence estimate is unchanged. *)
Theorem norm_taylor_analytic_polynomial (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a :
  @norm_taylor_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_polynomial_analytic_at R X Y NX NY hNX hNY A f a.
Proof.
move=>[U [ha [hUA [hf [D [hD hconv]]]]]].
pose P:=fun m v=>(m`!)%:R^-1 *:
  @ContinuousMultilinear.evaluation R m X Y NX NY hNX hNY [ffun i=>v] (D m).
exists U; split.
- exact (@norm_class_continuous R X Y NX NY hNX hNY U f 0 (hf 0%N) a ha).1.
split; first exact hUA.
exists P; split; last exact hconv.
move=>m.
have [hp hc]:=@norm_taylor_homogeneous_coefficient R X Y NX NY hNX hNY U f m a (D m) (hD m).
split; first exact hp.
move=>x; exact (@norm_class_zero_continuous_at R X Y NX NY hNX hNY (fun _=>True) (P m) x
  (norm_class_continuous (hc 0%N)) Logic.I).
Qed.
