(** Federer (1969), 4.1.1, p. 344: functions
    that vanish on successively larger compact neighbourhood
    bounds form a locally finite family. This supporting
    implication is used by the common-support sequence proof. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  SmoothCompactSet SmoothCompactExhaustionUP NormLocallyFiniteFamilyUP FiniteNatPrefixSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_exhaustion_vanishing_locally_finite]:
    compact-neighbourhood cofinality makes a successively
    vanishing family locally finite, supporting Federer
    4.1.1, p. 344. No bound on
    its nonzero values or derivatives is needed. *)
Theorem compact_exhaustion_vanishing_locally_finite (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (K:nat->smooth_compact_set hNX U) (hK:is_smooth_compact_exhaustion K)
    (Y:zmodType) (f:nat->X->Y):
  (forall n x,smooth_compact_carrier (K n) x ->f n x=0) ->
  is_norm_locally_finite_function_family NX U (@setT nat) f.
Proof.
move=>hZero x hx.
pose C:=@smooth_compact_singleton R X NX hNX U x hx.
have [N [W [hW [hCW hWK]]]]:=@smooth_compact_exhaustion_neighbourhood R X NX hNX U K hK C.
exists W; split; first exact:(hCW x (erefl x)).
split; first by move=>y hy; exact:(smooth_compact_in_domain (K N) y (hWK y hy)).
split.
- move=>y hy; apply:(@norm_domain_interior_neighbourhood R X NX hNX W y).2.
  exact:open_nbhs_nbhs (conj hW hy).
- exists (finite_nat_prefix_set N); split; first by move=>j hj.
  move=>y hy j _ hn.
  have hNj:(N<=j)%N by rewrite leqNgt -finite_nat_prefix_member.
  apply:hZero.
  exact:(@smooth_compact_exhaustion_monotone R X NX hNX U K hK N j hNj y (hWK y hy)).
Qed.
