(** Private scalar existence witness supporting Federer (1969), 2.4.12–13,
    pp. 86–88. Source context: RealExponentialUP.v. This is a deliberate
    background dependency: MathComp exp supplies elementary real exponential
    and logarithm only. Its power-series construction is hidden here. No
    external measure, integration, Holder, Minkowski or Lebesgue-space
    result is used. The book treats these elementary scalar functions as
    given. *)
From mathcomp Require Import all_boot all_order all_algebra reals exp.
From Federer Require Import RealExponentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_exponential_logarithm_exists]: existence of
    the elementary scalar functions used in Federer 2.4.12,
    p. 86, and 2.4.13, p. 88; implementation witness
    for the abstract laws, not an extra book theorem. *)
Theorem real_exponential_logarithm_exists (R : realType) :
  exists e l : R -> R, is_real_exponential_logarithm e l.
Proof.
exists (@sequences.expR R), (@ln R); constructor.
- exact: expR_gt0.
- exact: expR0.
- exact: expRD.
- exact: ltr_expR.
- exact: expRK.
- move=> x hx; apply: lnK; by rewrite qualifE.
- exact: expR_ge1Dx.
- exact: expR_gt1Dx.
Qed.
