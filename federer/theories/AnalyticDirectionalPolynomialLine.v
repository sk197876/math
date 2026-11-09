(** Federer (1969), 3.4.5, pp. 318–321: actual
    directional coefficients can be read from an exact
    finite polynomial on a line, by the Taylor
    uniqueness corollary of 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal NormSmoothFields
  NormTaylorRemainderBound NormTaylorLineValues NormTaylorLineRemainder NormLittleOPower
  PolynomialFiniteOrderComparison AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_directional_polynomial_line_coefficient]:
    an exact finite polynomial on a sufficiently short
    original line has precisely those actual divided directional
    coefficients, with zero padding above its degree,
    supporting 3.4.5, pp. 318–321. No scalar
    differentiation library or formal derivative is assumed. *)
Theorem analytic_directional_polynomial_line_coefficient (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) k v a (c:X->Y) M (b:nat->Y) r:
  A a ->@norm_analytic R X Y NX NY hNX hNY A f ->
  @is_analytic_directional_coefficient R X Y NX NY hNX hNY A f k v c ->
  0<r ->(forall t:R,`|t|<r ->f (a+t*:v)=\sum_(j<M) t^+j*:b j) ->
  c a=if (k<M)%N then b k else 0.
Proof.
move=>ha hf hc hr hExact.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose NZ i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have [D hD]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY A f (norm_analytic_class_all_orders hf).
pose L:=(maxn k M).+1.
pose u j:=if (j<=k)%N then ((j`!)%:R)^-1*:ev j [ffun _:'I_j=>v] (D j a) else 0.
pose w j:=if (j<M)%N then b j else 0.
have hK:(k.+1<=L)%N by rewrite /L;exact:leq_maxl.
have hM:(M<=L)%N:=leq_trans (leq_maxr k M) (leqnSn _).
have hTaylorValue t:norm_taylor_value ev D a (t*:v) k=\sum_(j<L) t^+j*:u j.
  rewrite (norm_taylor_value_on_line hZ)
    (big_ord_widen L (fun j=>t^+j*:(((j`!)%:R)^-1*:ev j [ffun _:'I_j=>v] (D j a))) hK) big_mkcond.
  apply:eq_bigr=>j _;rewrite /u ltnS.
  by case:(j<=k)%N;rewrite ?scaler0.
have hPolynomialValue t:(\sum_(j<M) t^+j*:b j)=\sum_(j<L) t^+j*:w j.
  rewrite (big_ord_widen L (fun j=>t^+j*:b j) hM) big_mkcond.
  apply:eq_bigr=>j _;rewrite /w;by case:(j<M)%N;rewrite ?scaler0.
have hTaylor:=@norm_taylor_line_little_o_fields R X Y NX NY hNX hNY Z ev NZ hZ A f D k a v
  ha (norm_class_continuous (norm_analytic_class_all_orders hf 0%N))
  (fun j _=>(hD j).1) (hD k).2.
have hActual:norm_little_o_power NY (fun t=>f (a+t*:v)-\sum_(j<L) t^+j*:u j) k.
  move=>epsilon hEpsilon;have [d [hd hBound]]:=hTaylor epsilon hEpsilon.
  exists d;split;first exact:hd.
  move=>t ht;rewrite -hTaylorValue;exact:hBound t ht.
have hPolynomial:norm_little_o_power NY (fun t=>f (a+t*:v)-\sum_(j<L) t^+j*:w j) k.
  move=>epsilon hEpsilon;exists r;split;first exact:hr.
  move=>t /andP [ht0 ht];rewrite -hPolynomialValue (hExact t ht) subrr (real_seminorm_zero hNY.1).
  exact:(mulr_ge0 (ltW hEpsilon) (exprn_ge0 _ (normr_ge0 t))).
have hKL:(k<L)%N by rewrite -ltnS;exact:hK.
have hCoefficient:=@finite_power_initial_asymptotic_coefficients_unique R Y NY hNY k L
  (fun t=>f (a+t*:v)) u w hActual hPolynomial k (leqnn k) hKL.
by rewrite /u leqnn /w -(hc a ha (D k a) ((hD k).1 a ha)) in hCoefficient.
Qed.
