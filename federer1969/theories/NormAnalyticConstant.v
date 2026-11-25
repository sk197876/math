(** Federer (1969), 3.1.24, p. 240: constant terms in analytic
    affine coordinate maps have zero positive differentials. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialConstant
  NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_constant_analytic]: constants are analytic,
    supporting the chart formulas in 3.1.24, p. 240. All
    positive differentials are zero on any open actual domain. *)
Theorem norm_constant_analytic (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (hA:forall x,A x -> norm_domain_interior NX A x) (c:Y) :
  @norm_analytic R X Y NX NY hNX hNY A (fun _=>c).
Proof.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have [c0 hc0]:=ContinuousMultilinearZero.continuous_multilinear_zero_surjective hNY (hZ 0%N) c.
move=>a ha; exists A,0; split; first exact ha.
split; first by move=>x hx.
split; first exact (@norm_class_infinity_constant R X Y NX NY hNX hNY Z ev ZN hZ A hA c).
move=>[|p] hp x hx z hz; first by [].
have hzero:=@norm_higher_differential_constant R X Y NX NY hNX hNY Z ev ZN hZ A hA c c0 hc0 p.+1 x hx.
have he:=norm_higher_differential_unique hNX hNY hZ hz hzero.
rewrite he /constant_higher_form (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY (hZ p.+1)).1).
by rewrite expr0n mul0r.
Qed.
