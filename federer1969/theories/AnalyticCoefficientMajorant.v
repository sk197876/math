(** Federer (1969), 3.1.24, pp. 238–239:
    one geometric majorant for every differential partial sum. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearZero NormHigherDifferentialUP SymmetricForms SymmetricOperatorNorm
  HomogeneousPolynomialFunctions PolynomialTaylorTerms HomogeneousPolynomialDifferentialNorm
  HomogeneousDerivativeGeometricBound GeometricIndexShift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_coefficient_geometric_majorants]: supporting
    uniform convergence of all differentiated partial sums in
    Federer 3.1.24, pp. 238–239. The coefficient bound
    c^m m! gives a common q^m M_i bound on a
    radius-s ball, where q=2cs<1 and M_i=(2c/q)^i i!
    for positive i. M_0 bounds the unrestricted constant
    coefficient as well. Terms above their polynomial degree
    vanish; hence the original series indices may be retained. *)
Theorem analytic_coefficient_geometric_majorants (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (phi:forall m,S_m X Y m) (E:forall m:nat,forall i,X->Z i)
    (A:X->Prop) a c s q :
  0<=c -> 0<=s -> 0<q<1 -> q= 2*c*s ->
  (forall x,A x -> NX (x-a)<=s) ->
  (forall m,(1<=m)%N ->
    (symmetric_operator_norm hNX.1 NY (phi m)<=(c^+m*(m`!)%:R)%:E)%E) ->
  (forall m i x u,@ev i u (E m i x)=
    symmetric_taylor_term i (phi m) (x-a) [tuple u j | j<i]) ->
  (forall x,@ev 0%N [ffun j:'I_0=>(0:X)] (E 0%N 0%N x)=
    sform_polynomial_value (phi 0%N) (x-a)) ->
  exists M:nat->R,(forall i,0<=M i) /\
    (forall i,(1<=i)%N -> M i= (2*c/q)^+i*(i`!)%:R) /\
    forall i m x,A x -> @ZN i (E m i x)<=q^+m*M i.
Proof.
move=>hc hs hq hqeq hA hphi he hzero.
pose M i:=if i==0%N then NY (sform_polynomial_value (phi 0%N) 0)+1
  else (2*c/q)^+i*(i`!)%:R.
have hq0:0<q:=(andP hq).1.
have hqne:q!=0:=lt0r_neq0 hq0.
have hratio:0<=2*c/q.
  apply: divr_ge0; last exact: ltW hq0.
  exact (mulr_ge0 (ler0n _ _) hc).
have hM i:0<=M i.
  case:i=>[|i]; rewrite /M /=.
  - have hn:=real_seminorm_nonnegative hNY.1 (sform_polynomial_value (phi 0%N) 0); lra.
  - exact (mulr_ge0 (exprn_ge0 i.+1 hratio) (ler0n _ _)).
exists M; split; first exact hM.
split.
- move=>[|i] hi; first by [].
  by rewrite /M.
- move=>i m x hx.
  case: (leqP i m)=>[him|hmi].
  + case:m him=>[|m] him.
    * case:i him=>[|i] him; last by [].
      rewrite (continuous_multilinear_zero_norm hNY (hZ 0%N)) hzero /M /= expr0 mul1r.
      have hconst:=sform_polynomial_scale_argument (phi 0%N) (0:R) (x-a).
      rewrite scale0r expr0 scale1r in hconst.
      by rewrite -hconst lerDl ler01.
    * have hh:=@homogeneous_derivative_geometric_bound R X Y (Z i) NX NY hNX hNY m.+1 i
        (@ev i) (@ZN i) (hZ i) (phi m.+1) (x-a) (E m.+1 i x) c s
        him hc hs (hA x hx) (hphi m.+1 (leq0n m)) (he m.+1 i x).
      rewrite -hqeq (geometric_index_shift_factor (2*c) (i`!)%:R hqne him) in hh.
      case:i him hh=>[|i] him hh; last exact hh.
      rewrite expr0 fact0 mulr1 mulr1 in hh.
      have hone:1<=M 0%N.
        rewrite /M /= lerDr; exact: real_seminorm_nonnegative hNY.1 _.
      have hm:=ler_wpM2l (exprn_ge0 m.+1 (ltW hq0)) hone.
      rewrite mulr1 in hm; exact (le_trans hh hm).
  + have hz:=@homogeneous_polynomial_differential_above_degree R X Y (Z i) NX NY m i
      (@ev i) (@ZN i) (hZ i) (phi m) (x-a) (E m i x) hmi (he m i x).
    rewrite hz (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY (hZ i)).1).
    exact (mulr_ge0 (exprn_ge0 m (ltW hq0)) (hM i)).
Qed.
