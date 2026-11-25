(** Federer (1969), 3.4.6, pp. 322–323: actual
    divided coefficients agree when two original lines have
    the same values. The proof uses 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal NormSmoothFields
  NormTaylorRemainderBound NormTaylorLineValues NormTaylorLineRemainder NormLittleOPower
  PolynomialFiniteOrderComparison AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_line_coefficients_agree]: actual
    divided derivatives on identical parameterised lines agree,
    supporting the original split coefficients of 3.4.6,
    pp. 322–323. Taylor remainders determine the coefficients;
    no derivative transport is assumed. *)
Theorem weierstrass_line_coefficients_agree (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (B:set Y) (f:X->R) (g:Y->R) k v w a b (c:X->R) (d:Y->R):
  A a ->B b ->
  @norm_analytic R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R) A f ->
  @norm_analytic R Y R^o NY (fun r=>`|r|) hNY (@scalar_absolute_value_norm R) B g ->
  @is_analytic_directional_coefficient R X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) A f k v c ->
  @is_analytic_directional_coefficient R Y R^o NY (fun r=>`|r|)
    hNY (@scalar_absolute_value_norm R) B g k w d ->
  (exists r:R,0<r /\forall t:R,`|t|<r ->f (a+t*:v)=g (b+t*:w)) ->c a=d b.
Proof.
move=>ha hb hf hg hc hd [rho [hRho hEqual]].
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ez i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
pose W i:=@ContinuousMultilinear.space R i Y R^o NY N hNY hN.
pose ew i:=@ContinuousMultilinear.evaluation R i Y R^o NY N hNY hN.
pose NW i:=@ContinuousMultilinear.norm R i Y R^o NY N hNY hN.
pose hW i:=@ContinuousMultilinear.laws R i Y R^o NY N hNY hN.
have [D hD]:=@norm_smooth_fields_exist R X R^o NX N hNX hN A f (norm_analytic_class_all_orders hf).
have [E hE]:=@norm_smooth_fields_exist R Y R^o NY N hNY hN B g (norm_analytic_class_all_orders hg).
pose u j:=((j`!)%:R)^-1*:ez j [ffun _:'I_j=>v] (D j a).
pose z j:=((j`!)%:R)^-1*:ew j [ffun _:'I_j=>w] (E j b).
have hFirst:=@norm_taylor_line_little_o_fields R X R^o NX N hNX hN Z ez NZ hZ A f D k a v
  ha (norm_class_continuous (norm_analytic_class_all_orders hf 0%N))
  (fun j _=>(hD j).1) (hD k).2.
have hSecond:=@norm_taylor_line_little_o_fields R Y R^o NY N hNY hN W ew NW hW B g E k b w
  hb (norm_class_continuous (norm_analytic_class_all_orders hg 0%N))
  (fun j _=>(hE j).1) (hE k).2.
have hActual:norm_little_o_power N (fun t=>f (a+t*:v)-\sum_(j<k.+1) t^+j*:u j) k.
  move=>epsilon hEpsilon;have [r [hr hBound]]:=hFirst epsilon hEpsilon.
  exists r;split;first exact:hr.
  move=>t ht;rewrite -(@norm_taylor_value_on_line R X R^o NX N Z ez NZ hZ D a v t k).
  exact:hBound t ht.
have hOther:norm_little_o_power N (fun t=>f (a+t*:v)-\sum_(j<k.+1) t^+j*:z j) k.
  move=>epsilon hEpsilon;have [r [hr hBound]]:=hSecond epsilon hEpsilon.
  exists (Num.min r rho);split;first by rewrite lt_min hr hRho.
  move=>t /andP [ht0 ht].
  have /andP [htr htRho]:(`|t|<r)&&(`|t|<rho) by rewrite -lt_min.
  rewrite (hEqual t htRho) -(@norm_taylor_value_on_line R Y R^o NY N W ew NW hW E b w t k).
  exact:hBound t (introT andP (conj ht0 htr)).
have hCoefficient:=@finite_power_initial_asymptotic_coefficients_unique R R^o N hN k k.+1
  (fun t=>f (a+t*:v)) u z hActual hOther k (leqnn k) (ltnSn k).
rewrite /u /z -(hc a ha (D k a) ((hD k).1 a ha))
  -(hd b hb (E k b) ((hE k).1 b hb)) in hCoefficient.
exact:hCoefficient.
Qed.
