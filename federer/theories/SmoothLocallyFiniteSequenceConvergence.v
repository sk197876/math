(** Federer (1969), 4.1.1, p. 344: a locally
    finite smooth sequence sum is the limit of
    its ordinary partial sums in the original E
    topology. Exact agreement near each compact
    controls every higher derivative, not only values. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyConvergence SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  NormLocallyFiniteFamilyUP FiniteFamilySumUP SmoothLocallyFiniteSum
  SmoothLocallyFiniteSequenceAgreement SmoothLocalAgreementSeminorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothLocallyFiniteSequenceConvergence.
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
Variable f:nat->E.
Hypothesis hLocal:is_norm_locally_finite_function_family NX U (@setT nat) (fun j x=>ev (f j) x).

(** Source for [smooth_locally_finite_sequence_converges]:
    ordinary partial sums converge in every original
    compact derivative seminorm, supporting the common-
    support sequence assertion in Federer 4.1.1,
    p. 344. *)
Theorem smooth_locally_finite_sequence_converges g:
  is_finite_family_sum_on U (@setT nat) (fun j x=>ev (f j) x) (ev g) ->
  open_family_converges (smooth_function_opens hD) ((fun m=>\sum_(j<m) f j) @ \oo) g.
Proof.
move=>hSum A hA hg.
have [[i K] [r [hr hBall]]]:=((smooth_function_topology_laws hD).2 A).1 hA g hg.
have [N [W [hW [hKW hNear]]]]:=@smooth_locally_finite_sequence_agreement R X Y NX NY hNX hNY
  U hU E ev hE f g K hLocal hSum.
exists N; first exact Logic.I.
move=>m hm; apply:hBall.
have hZero:=@smooth_local_agreement_difference_seminorm R X Y NX NY hNX hNY U hU E ev hE D hD K i
  (smooth_function_derivative_seminorm hD K i) (smooth_function_derivative_seminorm_laws hD K i)
  W (\sum_(j<m) f j) g hW hKW (hNear m hm).
by rewrite hZero.
Qed.

(** Source for [smooth_locally_finite_sequence_sum_exists]:
    the actual smooth sum exists and the ordinary
    partial sums converge to it in E, supporting
    Federer 4.1.1, p. 344. No Banach
    completion replaces the locally finite construction. *)
Theorem smooth_locally_finite_sequence_sum_exists:
  exists g:E,is_finite_family_sum_on U (@setT nat) (fun j x=>ev (f j) x) (ev g) /\
    open_family_converges (smooth_function_opens hD) ((fun m=>\sum_(j<m) f j) @ \oo) g.
Proof.
have [g hg]:=smooth_locally_finite_sum_exists hE hLocal.
exists g; split=>//; exact:smooth_locally_finite_sequence_converges.
Qed.
End SmoothLocallyFiniteSequenceConvergence.
