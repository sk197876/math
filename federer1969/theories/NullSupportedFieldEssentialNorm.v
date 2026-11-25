(** Federer (1969), 4.1.19, p. 377:
    null modifications leave the measurable
    representation unchanged. This supporting
    lemma isolates the zero essential norm of
    a field supported on a null set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionBasic MeasureUP
  MeasureAlmostBasic MeasureEssentialNormUP MeasureEssentialNorm
  MeasureEssentialNormComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_supported_field_essential_norm]:
    the almost-uniqueness assertion of Federer
    4.1.19, p. 377, and the seminorm convention
    of 2.4.12, p. 86. No measurability of
    the exceptional set beyond nullity is needed. *)
Lemma null_supported_field_essential_norm
    (R:realType) (X:choiceType) (Y:Type)
    (mu:set X->\bar R) (hm:is_measure mu)
    (N:Y->R) (f:X->Y) (A:set X):
  mu A=0->
  (forall x,~A x->N (f x)=0%R)->
  measure_essential_norm mu N (partial_function_total f)=0.
Proof.
move=>hA hZero.
apply:(measure_essential_norm_zero_iff hm N
  (partial_function_total f)).2.
apply:(@measure_null_subset R X mu hm _ A _ hA).
move=>x [y [hValue hPositive]];apply:contrapT=>hNot.
change (f x=y) in hValue.
change (is_true ((0<(N y)%:E)%E)) in hPositive.
have hNZero : N y=0%R.
  rewrite -hValue; exact: (@hZero x hNot).
by move:hPositive;rewrite hNZero ltxx.
Qed.
