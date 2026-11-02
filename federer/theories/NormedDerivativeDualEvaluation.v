(** Federer (1969), 2.9.22, p. 167: g'(x) is uniquely characterised by its
    evaluations against all elements of Y*. These supporting limit laws use
    the abstract norm and dual specifications of 2.4.12, p. 87. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP ContinuousRealFunctional
  RealFunctionalNormUP ContinuousDualUP NormedCurveDerivativeUP
  RealCurveDerivativeUP RealCurveDerivativeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [punctured_norm_limit_bounded_evaluation]: supporting
    passage from the norm limit to scalar limits in Federer 2.9.22,
    p. 167, the characterisation (g'(x),alpha)=(alpha o g)'(x).
    A finite bound on the supplied linear functional suffices. *)
Lemma punctured_norm_limit_bounded_evaluation (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (a : Hom E R^o) (C : R)
    (u : R -> E) (v : E) :
  0<=C -> (forall y, `|a y|<=C*N y) ->
  punctured_norm_limit N u v -> punctured_real_limit (fun h => a (u h)) (a v).
Proof.
move=> hC ha hu e he.
have hC1 : 0<C+1 by lra.
have he' : 0<e/(C+1) by rewrite divr_gt0.
have [d [hd hB]] := hu (e/(C+1)) he'.
exists d; split=> // h hh.
have hsmall := hB h hh.
have hmul : (C+1)*N (u h-v)<e.
  by move: hsmall; rewrite ltr_pdivlMr // mulrC.
rewrite -(linearB (hom_as_linear a) (u h) v) hom_as_linearE.
apply: le_lt_trans (ha (u h-v)) _.
apply: le_lt_trans _ hmul.
by rewrite mulrDl mul1r lerDl; exact: real_seminorm_nonnegative hN.1 _.
Qed.

(** Source for [normed_curve_derivative_dual_evaluation]: direct
    implication from the norm derivative to every dual derivative,
    Federer 2.9.22, p. 167. The dual's least-bound laws give
    the required continuity estimate; its implementation stays hidden. *)
Theorem normed_curve_derivative_dual_evaluation (R : realType)
    (E D : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> E) x v :
  has_normed_curve_derivative N g x v -> forall a : D,
  has_real_curve_derivative (fun t => ed a (g t)) x (ed a v).
Proof.
move=> hg a.
have hNa := continuous_dual_norm_laws hD a.
have hbound : forall y, `|ed a y|<=DN a*N y.
  move=> y; exact: real_functional_norm_bound hNa y.
have hu := @punctured_norm_limit_bounded_evaluation R E N hN (ed a) (DN a)
  (fun h => h^-1 *: (g (x+h)-g x)) v
  (real_functional_norm_nonnegative hNa) hbound hg.
apply: (@punctured_real_limit_congr R
  (fun h => ed a (h^-1 *: (g (x+h)-g x))))=> // h _.
rewrite linearZ linearB.
change (h^-1 * (ed a (g (x+h))-ed a (g x)) =
  (ed a (g (x+h))-ed a (g x))/h).
by rewrite mulrC.
Qed.

(** Source for [normed_curve_derivative_dual_characterisation]:
    uniqueness in the first paragraph of Federer 2.9.22, p. 167.
    Given an actual norm derivative, a vector equals it exactly when
    all of its dual evaluations are the corresponding real derivatives.
    This assertion does not substitute weak limits for norm existence. *)
Theorem normed_curve_derivative_dual_characterisation (R : realType)
    (E D : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> E) x v w :
  has_normed_curve_derivative N g x v ->
  (w=v <-> forall a : D,
    has_real_curve_derivative (fun t => ed a (g t)) x (ed a w)).
Proof.
move=> hv; split.
  move=> -> a; exact (@normed_curve_derivative_dual_evaluation R E D N hN ed DN hD g x v hv a).
move=> hw.
apply: (@continuous_real_functionals_separate R E N hN w v)=> a ha.
have [d hd] := continuous_dual_surjective hD (a:=hom_of_linear a) ha.
have hvd := @normed_curve_derivative_dual_evaluation R E D N hN ed DN hD g x v hv d.
have he := punctured_real_limit_unique (hw d) hvd.
by move: he; rewrite hd !hom_of_linearE.
Qed.
