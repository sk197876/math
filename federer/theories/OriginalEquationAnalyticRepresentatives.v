(** Federer (1969), 3.4.8(10), pp. 327, 331:
    the actual defining functions represent
    the original finite algebraic generators.
    Apply the public representative equations
    for germ ring operations. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  AnalyticRepresentativeRingEquations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [original_equation_analytic_representatives]:
    gamma_0(f_(m+1))=J(W) and
    gamma_0(f_j)=delta gamma_j-J(T_j),
    3.4.8(10), pp. 327, 331.
    Both the exact function values and
    their germ ring equations are retained. *)
Theorem original_equation_analytic_representatives (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (index:eqType) (first:index)
    (w d:@analytic_representative_type R X NX hNX a)
    (v t:index->@analytic_representative_type R X NX hNX a):
  exists f:index->@analytic_representative_type R X NX hNX a,
    (forall j x,analytic_representative_value (f j) x = if j==first then
      analytic_representative_value w x else
      analytic_representative_value d x*analytic_representative_value (v j) x-
        analytic_representative_value (t j) x) /\
    forall j,(analytic_germ (f j):[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]) =
      if j==first then (analytic_germ w:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]) else
      (analytic_germ d:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])*
        (analytic_germ (v j):[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])-
        (analytic_germ (t j):[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]).
Proof.
pose f:=fun j:index=>if j==first then w else
  @analytic_add_representatives R X NX hNX a
    (@analytic_multiply_representatives R X NX hNX a d (v j))
    (@analytic_negate_representative R X NX hNX a (t j)).
exists f;split.
- move=>j x;rewrite /f;case:(j==first);by [].
- move=>j;rewrite /f;case hCase:(j==first);first by [].
  by rewrite analytic_representative_add_ring_equation analytic_representative_multiply_ring_equation
    analytic_representative_negate_ring_equation.
Qed.
