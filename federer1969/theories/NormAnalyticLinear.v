(** Federer (1969), 3.1.24, p. 240: the bounded linear
    coordinate maps used in the analytic versions of 3.1.18–3.1.19
    are analytic. Their differentials above order one vanish. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm ContinuousMultilinearOne
  ContinuousOperatorUP NormOperatorNormUP NormRegularity NormRegularityOperations NormHigherDifferentialUP
  NormHigherDifferentialFirst NormHigherDifferentialUnique NormLinearHigherVanishing NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bounded_linear_analytic]: linear coordinate
    maps in the analytic analogues of Federer 3.1.18–3.1.19,
    cited in 3.1.24, p. 240. Any bounded linear map between
    normed spaces is analytic on any open actual domain, with
    constant M+1 for a nonnegative linear bound M. *)
Theorem norm_bounded_linear_analytic (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (hA:forall x,A x -> norm_domain_interior NX A x) (L:Hom X Y) :
  norm_bounded_linear NX NY L -> @norm_analytic R X Y NX NY hNX hNY A L.
Proof.
move=>hL a ha; have [M [hM hb]]:=hL.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
exists A,(M+1); split; first exact ha.
split; first by move=>x hx.
split; first by move=>k; exact (@norm_class_linear R X Y NX NY hNX hNY A L k hA hL).
move=>p hp x hx z hz.
case:p hp z hz=>[|[|p]] hp z hz; first by [].
- rewrite expr1 mulr1.
  have hd:=(@norm_higher_differential_first R X Y NX NY hNX hNY Z ev ZN hZ A L x z).1 hz.
  have hlin:=@norm_differential_linear R X Y NX NY hNX hNY A x L (@hA x hx) hL.
  have he:=NormDifferentialDirectional.norm_differential_unique hNX hNY hd hlin.
  have hn:=@continuous_multilinear_one_norm_laws R X Y (Z 1%N) NX NY (@ev 1%N) (@ZN 1%N) (hZ 1%N) z.
  have hbound:ZN 1%N z<=M.
    apply:(norm_operator_least hn hM)=>v; by rewrite he; exact (hb v).
  have hM1:M<=M+1 by lra.
  exact (le_trans hbound hM1).
- have hzero:=@norm_linear_higher_vanishing R X Y NX NY hNX hNY Z ev ZN hZ A hA L hL p.+2
    (leq0n p) x hx.
  have he:=norm_higher_differential_unique hNX hNY hZ hz hzero.
  rewrite he (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY (hZ p.+2)).1).
  apply:mulr_ge0; last exact:ler0n.
  apply:exprn_ge0; by lra.
Qed.
