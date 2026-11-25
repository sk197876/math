(** Federer (1969), 3.4.5, pp. 318–321: actual
    divided coefficient fields depend only on original
    local analytic values, by 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialLocal AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Local.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X Y NX NY hNX hNY).

(** Source for [analytic_directional_coefficient_domain_agreement]:
    changing no values on an original open domain leaves
    the actual divided coefficient field unchanged, supporting
    3.4.5, pp. 318–321. *)
Lemma analytic_directional_coefficient_domain_agreement (A:set X) (f g:X->Y) k v (c:X->Y):
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall x,A x ->f x=g x) ->Coefficient A f k v c ->Coefficient A g k v c.
Proof.
move=>hOpen hValues hc x hx z hz.
have hLocal:=@norm_higher_differential_local_agreement R X Y NX NY hNX hNY Z ev NZ hZ k A A A
  f g hOpen (fun y (_:A y)=>iff_refl _) (fun y hy _=>hValues y hy) x hx z.
exact:(hc x hx z (hLocal.2 hz)).
Qed.

(** Source for [analytic_directional_coefficient_open_restriction]:
    restricting to an original open subdomain preserves
    the divided coefficient values, supporting 3.4.5,
    pp. 318–321. Actual derivative graphs on
    both domains are compared, without default values. *)
Lemma analytic_directional_coefficient_open_restriction (A B:set X) (f:X->Y) k v (c:X->Y):
  (forall x,B x ->A x) ->(forall x,B x ->norm_domain_interior NX B x) ->
  Coefficient A f k v c ->Coefficient B f k v c.
Proof.
move=>hBA hOpen hc x hx z hz.
have hOriginal:=(@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev NZ hZ
  k A B f hBA hOpen x hx z).2 hz.
exact:(hc x (hBA x hx) z hOriginal).
Qed.
End Local.
