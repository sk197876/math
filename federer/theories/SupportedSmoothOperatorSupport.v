(** Federer (1969), 4.1.7, pp. 355–359: actual
    compact-test operators preserving every original
    support step shrink the literal function support.
    The proof uses the test's actual compact support
    itself as the compact step of 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SupportedSmoothOperatorTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section SupportedSmoothOperatorSupport.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:set X.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Variable P:Hom E F.
Hypothesis hSupport:forall (K:smooth_compact_set hNX U) f,
  @smooth_function_support R X Y NX hNX U E ev f `<=` smooth_compact_carrier K ->
  @smooth_function_support R X Z NX hNX U F fv (P f) `<=` smooth_compact_carrier K.
Local Notation TE := (smooth_test_space hE).
Local Notation TF := (smooth_test_space hF).
Local Notation ve := (smooth_test_value hE).
Local Notation vf := (smooth_test_value hF).
Local Notation Q := (@supported_smooth_test_operator R X Y Z NX NY NZ hNX hNY hNZ
  U E F ev fv hE hF P hSupport).

(** Source for [supported_smooth_test_support_subset]:
    the actual original test operator shrinks its
    argument's support, supporting current locality
    and proper pushforward in Federer 4.1.7,
    pp. 355–359. *)
Theorem supported_smooth_test_support_subset f:
  @smooth_function_support R X Z NX hNX U TF vf (Q f) `<=`
    @smooth_function_support R X Y NX hNX U TE ve f.
Proof.
pose S:=@smooth_function_support R X Y NX hNX U TE ve f.
pose K:=@Build_smooth_compact_set R X NX hNX U S (fun x hx=>hx.1)
  (@smooth_test_support_compact R X Y NX NY hNX hNY U E ev hE f).
have hInput:@smooth_function_support R X Y NX hNX U E ev (smooth_test_inclusion hE f)
    `<=` smooth_compact_carrier K by move=>x hx;exact:hx.
have hBound:=@hSupport K (smooth_test_inclusion hE f) hInput.
move=>x hx.
change (@smooth_function_support R X Z NX hNX U F fv
  (smooth_test_inclusion hF (Q f)) x) in hx.
rewrite supported_smooth_test_evaluation in hx.
exact:(hBound x hx).
Qed.
End SupportedSmoothOperatorSupport.
