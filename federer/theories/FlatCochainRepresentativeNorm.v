(** Federer (1969), 4.1.19, p. 377:
    the norm of a measurable representing pair must
    depend only on its almost-everywhere class.
    This supporting definition uses the earlier
    essential seminorms, rather than the pointwise
    global comass of 4.1.7, p. 358. It does not
    identify either quantity with a cochain norm. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP
  MeasureEssentialNormUP MeasureEssentialNorm
  MeasureEssentialNormComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ereal_scope.

(** Source for [flat_cochain_representative_norm]:
    the two dual L-infinity bounds in Federer
    4.1.19, p. 377, interpreted as essential
    bounds on arbitrary measurable representatives. *)
Definition flat_cochain_representative_norm
    (R:realType) (X:choiceType) (Y Z:Type)
    (mu:set X->\bar R) (N:Y->R) (M:Z->R)
    (f:partial_function X Y) (g:partial_function X Z) : \bar R :=
  Order.max (measure_essential_norm mu N f)
    (measure_essential_norm mu M g).

(** Source for [flat_cochain_representative_norm_nonnegative]:
    the original flat norm in Federer 4.1.19,
    p. 377, is a nonnegative dual norm.
    Essential bounds retain this endpoint even
    when the source measure is zero. *)
Lemma flat_cochain_representative_norm_nonnegative
    (R:realType) (X:choiceType) (Y Z:Type)
    (mu:set X->\bar R) (N:Y->R) (M:Z->R)
    (f:partial_function X Y) (g:partial_function X Z):
  0<=flat_cochain_representative_norm mu N M f g.
Proof.
by rewrite /flat_cochain_representative_norm
  le_max measure_essential_norm_nonnegative.
Qed.

(** Source for [flat_cochain_representative_norm_almost_equal]:
    almost uniqueness of both forms in Federer
    4.1.19, p. 377, must preserve their dual norm.
    Apply the already proved essential-norm
    invariance to each field separately. *)
Lemma flat_cochain_representative_norm_almost_equal
    (R:realType) (X:choiceType) (Y Z:Type)
    (mu:set X->\bar R) (hm:is_measure mu)
    (N:Y->R) (M:Z->R)
    (f f':partial_function X Y)
    (g g':partial_function X Z):
  measure_almost_equal mu f f'->
  measure_almost_equal mu g g'->
  flat_cochain_representative_norm mu N M f g=
    flat_cochain_representative_norm mu N M f' g'.
Proof.
move=>hf hg;rewrite /flat_cochain_representative_norm.
by rewrite (measure_essential_norm_almost_equal hm N hf)
  (measure_essential_norm_almost_equal hm M hg).
Qed.
