(** Federer (1969), 4.1.4, pp. 348–349: the original
    conclusion is an integral over U. Actual tests vanish
    outside U, so the proved whole-space integral gives that
    literal subset integral. Empty support gives the zero test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP RealSubsetIntegralGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestScalarSubsetIntegral.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).

(** Source for [smooth_test_empty_support_zero]: the empty-A
    case of the conclusion in Federer 4.1.4, p. 348. An
    actual test supported in the empty set is zero. *)
Lemma smooth_test_empty_support_zero f:support f `<=` set0 ->f=0.
Proof.
move=>hSupport; apply:(smooth_test_values_extensional hE)=>x hx.
have hZero:value (0:DT) x=0:=congr1 (fun F:X->Y=>F x) (linear0 (smooth_test_values_hom hE)).
rewrite hZero.
case:(pselect (value f x=0))=>// hNot.
exact:False_ind _ (hSupport x
  (@smooth_function_nonzero_in_support R X Y NX hNX U DT value f x hx hNot)).
Qed.

(** Source for [smooth_test_scalar_subset_integral]: the actual
    scalar integral over U in Federer 4.1.4, p. 348, agrees
    with the whole-space integral of the normalized original
    test. Its zero extension uses the original 2.4.10 law. *)
Lemma smooth_test_scalar_subset_integral (mu:set X->\bar R)
    (alpha:Hom Y R^o) (f:DT) b:
  is_measure_integral mu (real_total_integrand (fun x=>alpha (value f x))) b ->
  is_measure_subset_integral mu U (real_total_integrand (fun x=>alpha (value f x))) b.
Proof.
move=>hIntegral.
have hOff:forall x,~U x ->alpha (value f x)=0.
  move=>x hx; by rewrite (@smooth_test_value_outside R X Y NX NY hNX hNY U E ev hE f x hx) linear0.
exact:((@real_subset_integral_total R X mu U (fun x=>alpha (value f x))
  (fun x=>alpha (value f x)) b (fun _ _=>erefl) hOff).2 hIntegral).
Qed.
End TestScalarSubsetIntegral.
