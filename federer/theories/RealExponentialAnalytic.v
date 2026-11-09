(** Federer (1969), 3.4.5, p. 321, citing Cartan
    (1957), pp. 97–99: the scalar exponential in the
    locally analytic counterexample is analytic. This follows
    from its actual derivatives and 3.1.24's original bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  NormOpenDomainLaws NormClassZeroLocalBound ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearScalar NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialUnique
  NormAnalyticUP RealExponentialUP RealExponentialSealed RealExponentialSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_exponential_analytic]: analyticity of
    the actual scalar exponential used in the example cited
    in 3.4.5, p. 321. No external calculus theorem
    or analyticity hypothesis is used. *)
Theorem real_exponential_analytic (R:realType):
  @norm_analytic R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) setT
    (@RealExponential.exponential R).
Proof.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose E:=@RealExponential.exponential R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose NZ i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
have hSmooth:=@real_exponential_class_infinity R Z ev NZ hZ.
move=>a _.
have [r [M [hr [hM hBound]]]]:=@norm_class_zero_local_bound R R^o R^o N N hN hN
  setT E a (norm_class_continuous (hSmooth 0%N)) Logic.I.
pose U:=fun x:R^o=>N (x-a)<r.
have hUa:U a by rewrite /U /N subrr normr0.
have hOpen x (hx:U x):norm_domain_interior N U x.
  exact:(@norm_open_ball_domain_interior R R^o N hN a r x hx).
have hClass i:norm_class hN hN U E i.
  exact:(@norm_class_open_restriction R R^o R^o N N hN hN setT U E i
    (fun x hx=>Logic.I) hOpen (hSmooth i)).
exists U,(M+1);split;first exact:hUa.
split;first by move=>x hx.
split;first exact:hClass.
move=>m hm x hx z hz.
have hzFull:=(@norm_higher_differential_open_restriction R R^o R^o N N hN hN
  Z ev NZ hZ m setT U E (fun x hx=>Logic.I) hOpen x hx z).2 hz.
have [w [hw hEval]]:=@real_exponential_higher_differentials R Z ev NZ hZ m x.
have hEqual:=@norm_higher_differential_unique R R^o R^o N N hN hN
  Z ev NZ hZ setT E m x z w hzFull hw.
have hProduct:(\prod_(i<m) ([ffun j:'I_m=>(1:R^o)] i)) = 1.
  by apply:big1=>i _;rewrite ffunE.
rewrite hEqual (continuous_multilinear_scalar_norm hN (hZ m)) hEval hProduct mul1r.
rewrite /N ger0_norm;last exact:ltW (real_exponential_positive (@RealExponential.laws R) x).
have hxBound:E x<=M.
  have hh: N (E x)<=M:=(hBound x hx).2.
  by rewrite /N ger0_norm in hh;[exact:hh|exact:ltW (real_exponential_positive (@RealExponential.laws R) x)].
apply:le_trans hxBound _.
have hOne:1<=M+1 by lra.
have hM1:M<=M+1 by lra.
have hPower:M<=(M+1)^+m:=le_trans hM1 (ler_eXnr hm hOne).
have hFactorial:(1:R)<=(m`!)%:R by rewrite ler1n;exact:fact_gt0.
apply:le_trans hPower _.
have hMultiply:=ler_wpM2l (exprn_ge0 m (le_trans ler01 hOne)) hFactorial.
by rewrite mulr1 in hMultiply.
Qed.
