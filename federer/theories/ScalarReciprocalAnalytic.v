(** Federer (1969), 3.4.5, p. 321, citing Cartan
    (1957), pp. 97–99: reciprocal expressions in the actual
    defining coefficient are analytic away from their original
    poles. Actual derivative formulas give the required bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  NormOpenDomainLaws NormClassZeroLocalBound ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearScalar NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialUnique
  NormAnalyticUP ScalarReciprocalHigherDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_reciprocal_analytic]: analyticity of
    the actual reciprocal on its nonzero domain, supporting
    the example cited in 3.4.5, p. 321. The
    pole is retained, rather than assigned an analytic value. *)
Theorem scalar_reciprocal_analytic (R:realType):
  @norm_analytic R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)
    [set t:R^o|t!=0] (fun t=>t^-1).
Proof.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose A:=fun t:R^o=>t!=0.
pose inv:=fun t:R^o=>t^-1.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose NZ i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
have hSmooth:=@scalar_reciprocal_class_infinity R Z ev NZ hZ.
move=>a ha.
have [r [M [hr [hM hBound]]]]:=@norm_class_zero_local_bound R R^o R^o N N hN hN
  A inv a (norm_class_continuous (hSmooth 0%N)) ha.
pose U:=fun x:R^o=>N (x-a)<r.
have hUa:U a by rewrite /U /N subrr normr0.
have hUA x (hx:U x):A x:=(hBound x hx).1.
have hOpen x (hx:U x):norm_domain_interior N U x.
  exact:(@norm_open_ball_domain_interior R R^o N hN a r x hx).
have hClass i:norm_class hN hN U inv i.
  exact:(@norm_class_open_restriction R R^o R^o N N hN hN A U inv i hUA hOpen (hSmooth i)).
exists U,((M+1)^+2);split;first exact:hUa.
split;first exact:hUA.
split;first exact:hClass.
move=>m hm x hx z hz.
have hzFull:=(@norm_higher_differential_open_restriction R R^o R^o N N hN hN
  Z ev NZ hZ m A U inv hUA hOpen x hx z).2 hz.
have [w [hw hEval]]:=@scalar_reciprocal_higher_differentials R Z ev NZ hZ m x (hUA x hx).
have hEqual:=@norm_higher_differential_unique R R^o R^o N N hN hN
  Z ev NZ hZ A inv m x z w hzFull hw.
have hProduct:(\prod_(i<m) ([ffun j:'I_m=>(1:R^o)] i)) = 1.
  by apply:big1=>i _;rewrite ffunE.
rewrite hEqual (continuous_multilinear_scalar_norm hN (hZ m)) hEval hProduct mul1r.
rewrite /N /scalar_reciprocal_derivative_coefficient !normrM !normrX normrN normr1
  expr1n mul1r normr_nat.
have hOne:1<=M+1 by lra.
have hM1:M<=M+1 by lra.
have hPower:`|x^-1|^+m.+1<=(M+1)^+m.+1.
  apply:lerXn2r;[exact:normr_ge0|exact:le_trans ler01 hOne|].
  exact:le_trans (hBound x hx).2 hM1.
have hDegrees:(m.+1<=2 * m)%N by rewrite mul2n -addnn;exact:leq_add hm (leqnn m).
have hExponents:((M+1)^+m.+1)<=(M+1)^+(2 * m).
  have hh:=ler_weXn2l hOne hDegrees.
  exact:hh.
have hEstimate:=ler_wpM2l (ler0n R (m`!)) (le_trans hPower hExponents).
rewrite exprM in hEstimate.
apply:le_trans hEstimate _.
by rewrite mulrC.
Qed.
