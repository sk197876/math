(** Federer (1969), 4.1.1, pp. 344–345: evaluation
    and exact compact-support laws of the actual opaque
    test-function space. The proofs use its subspace image
    and the public smooth-function evaluation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity LinearSubspaceRepresentationUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSupport
  SmoothTestSubspaces SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestEvaluation.
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
Local Notation inc := (smooth_test_inclusion hE).

(** Source for [smooth_test_value]: the original function
    represented by a test, Federer 4.1.1, pp. 344–345. *)
Definition smooth_test_value (f:DT):X->Y:=ev (inc f).

(** Source for [smooth_test_values_hom]: test evaluation is
    linear, supporting distribution evaluation in Federer
    4.1.1, p. 345. *)
Definition smooth_test_values_hom:Hom DT (GRing.Lmodule.clone R (X->Y) _):=
  hom_comp (smooth_function_values_hom hE) inc.

(** Source for [smooth_test_values_linear]: pointwise
    vector operations on D(U,Y), Federer 4.1.1,
    pp. 344–345. *)
Lemma smooth_test_values_linear:linear smooth_test_value.
Proof. exact:(hom_linear smooth_test_values_hom). Qed.

(** Source for [smooth_test_value_outside]: normalization
    outside U contributes no test values, supporting the
    zero-extension convention in Federer 4.1.1, p. 345. *)
Lemma smooth_test_value_outside f x:~U x ->smooth_test_value f x=0.
Proof. move=>hx; exact (@smooth_function_evaluation_outside R X Y NX NY hNX hNY U E ev hE (inc f) x hx). Qed.

(** Source for [smooth_test_value_smooth]: every represented
    test is smooth on U, Federer 4.1.1, p. 344. *)
Lemma smooth_test_value_smooth f:norm_class_all_orders hNX hNY U (smooth_test_value f).
Proof. exact (@smooth_function_evaluation_smooth R X Y NX NY hNX hNY U E ev hE (inc f)). Qed.

(** Source for [smooth_test_values_extensional]: tests are
    equal when their original values on U agree, supporting
    the space D(U,Y) of Federer 4.1.1, p. 344. *)
Lemma smooth_test_values_extensional f g:
  (forall x,U x ->smooth_test_value f x=smooth_test_value g x) ->f=g.
Proof.
move=>he; apply:(subspace_representation_injective (smooth_test_space_laws hE)).
exact:(smooth_function_extensional hE he).
Qed.

(** Source for [smooth_test_support_bound]: every actual
    test has support in a compact subset of U, the union
    defining D(U,Y) in Federer 4.1.1, p. 344. *)
Theorem smooth_test_support_bound f:
  exists K:smooth_compact_set hNX U,
    @smooth_function_support R X Y NX hNX U DT smooth_test_value f `<=` smooth_compact_carrier K.
Proof.
exact (@subspace_representation_member R E DT (smooth_compact_support_subspace hE) inc
  (smooth_test_space_laws hE) f).
Qed.

(** Source for [smooth_test_support_compact]: the support
    of every member of D is compact, Federer 4.1.1,
    p. 345. The closure is the original source closure. *)
Theorem smooth_test_support_compact f:
  compact [set x:real_norm_metric_space hNX|
    @smooth_function_support R X Y NX hNX U DT smooth_test_value f x].
Proof.
have [K hK]:=smooth_test_support_bound f.
exact:(@smooth_function_supported_compact R X Y NX hNX U DT smooth_test_value K f hK).
Qed.
End TestEvaluation.
Arguments smooth_test_value {R X Y NX NY hNX hNY U E ev} hE f x.
Arguments smooth_test_values_hom {R X Y NX NY hNX hNY U E ev} hE.
Arguments smooth_test_values_linear {R X Y NX NY hNX hNY U E ev} hE.
Arguments smooth_test_value_outside {R X Y NX NY hNX hNY U E ev} hE f {x} _.
Arguments smooth_test_value_smooth {R X Y NX NY hNX hNY U E ev} hE f.
Arguments smooth_test_values_extensional {R X Y NX NY hNX hNY U E ev} hE {f g} _.
Arguments smooth_test_support_bound {R X Y NX NY hNX hNY U E ev} hE f.
Arguments smooth_test_support_compact {R X Y NX NY hNX hNY U E ev} hE f.
