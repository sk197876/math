(** Federer (1969), 4.1.1, pp. 343–344: the derivative seminorms
    form a directed separating family. The proof reuses the
    original zeroth-differential identification from 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearZero NormHigherDifferentialUP SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  SmoothFunctionDerivativesUP SmoothCompactSet SmoothDerivativeSeminormUP
  SmoothDerivativeSeminormLaws DirectedSeminormFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothSeminormFamily.
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
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable p:smooth_compact_set hNX U->nat->E->R.
Hypothesis hp:forall K i,
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i (p K i).

(** Source for [smooth_derivative_zero_norm]: D^0 f=f makes
    the zeroth derivative norm equal to the original value norm,
    Federer 4.1.1, p. 343, using 3.1.11, pp. 218–219. *)
Lemma smooth_derivative_zero_norm f x : U x ->
  @ZN 0%N (@D 0%N x f)=NY (ev f x).
Proof.
move=>hx.
have hNorm:=@continuous_multilinear_zero_norm R X Y (Z 0%N) NX NY hNY
  (@ContinuousMultilinear.evaluation R 0%N X Y NX NY hNX hNY)
  (@ZN 0%N) (hZ 0%N) (@D 0%N x f).
have hValue:=(@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD
  0%N f x hx).2.
exact:(eq_trans hNorm (congr1 NY hValue)).
Qed.

(** Source for [smooth_function_seminorms_directed]: union of
    compact sets and maximum order give the single-ball base
    of Federer 4.1.1, p. 344. *)
Theorem smooth_function_seminorms_directed :
  is_directed_seminorm_family
    (fun j:nat * smooth_compact_set hNX U=>p j.2 j.1).
Proof.
constructor.
- exists (0%N,@smooth_compact_empty R X NX hNX U); exact I.
- move=>[i K]; exact:(smooth_derivative_seminorm_is_seminorm (hp K i)).
- move=>[i K] [j L].
  exists (maxn i j,smooth_compact_union K L)=>f; split.
  + apply:(smooth_derivative_seminorm_monotone (hp K i)
      (hp (smooth_compact_union K L) (maxn i j)) (leq_maxl i j)).
    exact:subsetUl.
  + apply:(smooth_derivative_seminorm_monotone (hp L j)
      (hp (smooth_compact_union K L) (maxn i j)) (leq_maxr i j)).
    exact:subsetUr.
Qed.

(** Source for [smooth_function_seminorms_separate]: values on
    singleton compact sets separate smooth functions; this proves
    the Hausdorff assertion of Federer 4.1.1, p. 344. *)
Theorem smooth_function_seminorms_separate :
  seminorm_family_separates
    (fun j:nat * smooth_compact_set hNX U=>p j.2 j.1).
Proof.
move=>f hf; apply:(smooth_function_extensional hE)=>x hx.
rewrite (smooth_function_zero_value hE).
apply:hNY.2; apply/eqP; rewrite eq_le (real_seminorm_nonnegative hNY.1) andbT.
pose K:=@smooth_compact_singleton R X NX hNX U x hx.
have hb:=smooth_derivative_seminorm_bound (hp K 0%N) f (leqnn 0%N) (erefl x).
rewrite (smooth_derivative_zero_norm f hx) in hb.
by rewrite (hf (0%N,K)) in hb.
Qed.
End SmoothSeminormFamily.
