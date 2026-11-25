(** Federer (1969), 3.4.8(11), p. 333:
    a critical germ filling a neighbourhood
    makes the original function locally constant.
    This supporting connection applies the existing
    generic rank-zero theorem from 3.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormRankZero LinearRankUP SetGermUP SetGermSealed SetGermLaws SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_whole_germ_locally_constant]:
    if the actual critical set has
    the whole germ, the actual derivative
    vanishes near the centre, so the
    function is locally constant. This supports
    the dimension drop in 3.4.8(11),
    p. 333. *)
Theorem critical_whole_germ_locally_constant (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) (D:X->Hom X Y) a:
  (forall x,A x ->has_norm_differential NX NY A f x (D x)) ->
  @set_germ (Topological.clone (real_norm_metric_space hNX) _) a
    [set x|A x /\ forall v,D x v = 0] =
  @set_germ (Topological.clone (real_norm_metric_space hNX) _) a setT ->
  exists r:R,0<r /\ forall x,NX (x-a)<r ->A x /\ f x = f a.
Proof.
move=>hD hGerm.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [U [hU [hUa hEqual]]]:=(@set_germ_equality_original T a _ _).1 hGerm.
have hCritical:forall x,U x ->A x /\ forall v,D x v = 0.
  move=>x hx;have h:(([set x|A x /\ forall v,D x v = 0] `&` U):set X) x.
    rewrite hEqual;by split.
  exact:h.1.
have hOpen:=hU;rewrite openE in hOpen.
have [r [hr hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX U a).2 (hOpen a hUa).
apply:(@norm_generic_rank_zero_locally_constant R X Y NX NY hNX hNY A f D a hD).
exists r;split;first exact:hr.
move=>h hh;have [hAh hZero]:=hCritical (a+h) (hBall h hh).
split;first exact:hAh.
exact:(linear_rank_zeroP (D (a+h))).2 hZero.
Qed.
