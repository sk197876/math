(** Federer (1969), 4.1.1, p. 344: D_K(U,Y) is a
    closed subspace of E(U,Y). Evaluation outside K and the
    order-zero singleton seminorm give an open neighbourhood
    of every smooth function not supported in K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothDerivativeSeminormUP SmoothFunctionSeminormFamily SmoothFunctionTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FixedSupportClosed.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).
Local Notation EO := (smooth_function_opens hD).

(** Source for [smooth_fixed_support_closed]: the functions
    with support contained in K form an E-closed set,
    Federer 4.1.1, p. 344. The argument includes empty
    K, empty U and zero-dimensional spaces. *)
Theorem smooth_fixed_support_closed (K:smooth_compact_set hNX U):
  EO (~` [set f:E|support f `<=` smooth_compact_carrier K]).
Proof.
apply:((smooth_function_topology_laws hD).2 _).2=>f hf.
have hSome:exists x,~smooth_compact_carrier K x /\ ev f x<>0.
  case:(pselect (exists x,~smooth_compact_carrier K x /\ ev f x<>0))=>// hNone.
  apply:False_ind; apply:hf; apply:(smooth_function_compact_support_iff hE K f).2=>x hx.
  case:(pselect (ev f x=0))=>// hne; exact:False_ind _ (hNone (ex_intro _ x (conj hx hne))).
have [x [hx hVal]]:=hSome.
have hUx:U x.
  case:(pselect (U x))=>// hOut; exact:False_ind _ (hVal (smooth_function_evaluation_outside hE f hOut)).
pose L:=@smooth_compact_singleton R X NX hNX U x hUx.
pose r:=NY (ev f x).
have hr:0<r.
  rewrite /r (real_norm_positive hNY.1 hNY.2); apply/eqP; exact hVal.
exists (0%N,L),r; split=>// g hg hSupp.
have hZero:ev g x=0:=(smooth_function_compact_support_iff hE K g).1 hSupp x hx.
have hBound:=smooth_derivative_seminorm_bound
  (smooth_function_derivative_seminorm_laws hD L 0%N) (g-f) (leqnn 0%N) (erefl x).
have hNorm:=@smooth_derivative_zero_norm R X Y NX NY hNX hNY U E ev D hD (g-f) x hUx.
rewrite hNorm in hBound.
have hValue:ev (g-f) x=ev g x-ev f x:=
  congr1 (fun h:X->Y=>h x) (linearB (smooth_function_values_hom hE) g f).
rewrite hValue hZero sub0r (real_seminorm_negate hNY.1) in hBound.
have hBad:r<r:=le_lt_trans hBound hg.
by rewrite ltxx in hBad.
Qed.
End FixedSupportClosed.
