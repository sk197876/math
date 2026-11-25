(** Federer (1969), 4.1.1, p. 344: the
    auxiliary locally finite selection produces one
    actual smooth function with unbounded selected
    evaluations. This closes the analytic step of
    the common-support contradiction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP OpenFamilyConvergence NormOpenTopology SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothDualHumpUP
  SmoothLocallyFiniteSequenceConvergence FinitePrefixSumSupport RealOpenSequenceFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HumpUnbounded.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable T:nat->Hom E R^o.
Hypothesis hT:forall j,open_family_continuous (smooth_function_opens hD)
  (norm_open_family (@scalar_absolute_value_norm R)) (T j).
Variables (f:nat->E) (k:nat->nat).
Hypothesis hH:is_smooth_dual_hump NX U ev T f k.

(** Source for [smooth_dual_hump_unbounded]: the actual
    smooth locally finite sum has selected evaluations
    exactly n+1, supporting the contradiction for
    convergent weak E' sequences in Federer
    4.1.1, p. 344. *)
Theorem smooth_dual_hump_unbounded:exists g:E,forall n,T (k n) g=n.+1%:R.
Proof.
have hLocal:=@smooth_dual_hump_local_finiteness R X Y E NX U ev T f k hH.
have [g [hSum hConv]]:=@smooth_locally_finite_sequence_sum_exists R X Y NX NY hNX hNY U hU
  E ev hE D hD f hLocal.
exists g=>n.
have hReal:open_family_converges (norm_open_family (@scalar_absolute_value_norm R))
    ((fun m=>T (k n) (\sum_(j<m) f j)) @ \oo) (T (k n) g).
  move=>A hA hg.
  exact:(hConv [set x:E|A (T (k n) x)] (@hT (k n) A hA) hg).
have hConst:exists N,forall m,(N<=m)%N ->T (k n) (\sum_(j<m) f j)=n.+1%:R.
  exists n.+1=>m hm.
  have hZero j (hj:(n.+1<=j)%N):T (k n) (f j)=0.
    exact:(@smooth_dual_hump_tail_zero R X Y E NX U ev T f k hH n j hj).
  have hPad:=@finite_prefix_sum_extend R^o (fun j=>T (k n) (f j)) n.+1 m hm hZero.
  rewrite linear_sum -hPad -linear_sum.
  exact:(@smooth_dual_hump_prescribed_partial R X Y E NX U ev T f k hH n).
exact:(esym (@real_open_eventually_constant_limit R (fun m=>T (k n) (\sum_(j<m) f j))
  n.+1%:R (T (k n) g) hReal hConst)).
Qed.
End HumpUnbounded.
