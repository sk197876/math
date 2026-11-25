(** Federer (1969), 4.1.8, p. 360: one cutoff equal
    to one on the projected support preserves every original
    first-variable test there. This supporting identity uses only
    the actual cutoff replacement laws of 4.1.1, pp. 344–345. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces
  SmoothTestEvaluation SmoothCutoffReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothCutoffSupportedTest.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Variable K:smooth_compact_set hNX U.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation C := (@smooth_cutoff_replacement R X Y NX NY hNX hNY d b hb U hU E ev hE K).

(** Source for [smooth_cutoff_replacement_fixes_supported_test]:
    the original compact cutoff preserves every test supported
    in K, supporting the common-support slice argument of
    Federer 4.1.8, p. 360. Equality is in the actual
    test space and uses no joint vector continuity assumption. *)
Theorem smooth_cutoff_replacement_fixes_supported_test (f:DT):
  @smooth_function_support R X Y NX hNX U E ev (inc f) `<=` smooth_compact_carrier K->
  C (inc f)=f.
Proof.
move=>hK.
have[W [hW [hKW [hWU hAgree]]]]:=@smooth_cutoff_replacement_agrees_near_compact
  R X Y NX NY hNX hNY d b hb U hU E ev hE K.
have hShrink:=@smooth_cutoff_replacement_support_subset R X Y NX NY hNX hNY
  d b hb U hU E ev hE K (inc f).
have hCK:@smooth_function_support R X Y NX hNX U E ev (inc (C (inc f)))
    `<=` smooth_compact_carrier K.
  move=>x hx;exact:(hK x (hShrink x hx)).
have hOffF:forall x,~smooth_compact_carrier K x->ev (inc f) x=0.
  exact:(smooth_function_compact_support_iff hE K (inc f)).1 hK.
have hOffC:forall x,~smooth_compact_carrier K x->ev (inc (C (inc f))) x=0.
  exact:(smooth_function_compact_support_iff hE K (inc (C (inc f)))).1 hCK.
apply:(smooth_test_values_extensional hE)=>x hx.
change (ev (inc (C (inc f))) x=ev (inc f) x).
case:(pselect (smooth_compact_carrier K x))=>hKx.
- exact:(hAgree (inc f) x (@hKW x hKx)).
- by rewrite (@hOffC x hKx) (@hOffF x hKx).
Qed.
End SmoothCutoffSupportedTest.
