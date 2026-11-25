(** Federer (1969), 3.4.5, p. 321: actual directional
    Taylor coefficients determine a global analytic function
    on each original coordinate line, by 3.1.11 and
    3.1.24, pp. 221,240. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP HilbertFormCompactness
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormRegularity NormSmoothFields
  NormOpenDomainLaws NormAnalyticUP NormAnalyticLocal NormAnalyticConstant NormAnalyticArithmetic NormAnalyticOperations
  NormTaylorRemainderBound NormTaylorLineValues NormTaylorLineRemainder
  ScalarVectorLineAnalytic ScalarRightLittleOPower ScalarAnalyticGlobalUniqueness AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_directional_line_zero]: zero actual
    divided coefficients in one original direction force zero
    on the entire actual affine line, supporting 3.4.5,
    p. 321. Actual Taylor remainders prove flatness;
    no coefficient transport or global identity is assumed. *)
Theorem analytic_directional_line_zero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (f:X->R) (c:nat->X->R) a v:
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) setT f ->
  (forall k,@is_analytic_directional_coefficient R X R^o NX (fun t=>`|t|)
    hNX (@scalar_absolute_value_norm R) setT f k v (c k)) ->
  (forall k,c k a=0) ->forall t:R,f (a+t*:v)=0.
Proof.
move=>hf hCoefficient hZero.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
have hConstant:@norm_analytic R R^o X N NX hN hNX setT (fun _=>a):=
  @norm_constant_analytic R R^o X N NX hN hNX setT (fun t _=>norm_full_domain_interior N t) a.
have hLine:@norm_analytic R R^o X N NX hN hNX setT (fun t=>a+t*:v):=
  norm_analytic_add hConstant (@scalar_vector_line_analytic R X NX hNX v).
have hF:=norm_analytic_compose_on (fun t (_:setT t)=>Logic.I) hLine hf.
apply:(scalar_global_analytic_right_flat_zero hF)=>m.
have [D hD]:=@norm_smooth_fields_exist R X R^o NX N hNX hN setT f (norm_analytic_class_all_orders hf).
have hTaylor:=@norm_taylor_line_little_o_fields R X R^o NX N hNX hN Z ev NZ hZ setT f D m a v
  Logic.I (norm_class_continuous (norm_analytic_class_all_orders hf 0%N))
  (fun j _=>(hD j).1) (hD m).2.
have hValue t:norm_taylor_value ev D a (t*:v) m=0.
  rewrite (norm_taylor_value_on_line hZ);apply:big1=>j _.
  have hActual:=hCoefficient j a Logic.I (D j a) ((hD j).1 a Logic.I).
  by rewrite -hActual hZero scaler0.
apply:scalar_little_o_right_restriction.
move=>epsilon hEpsilon;have [r [hr hBound]]:=hTaylor epsilon hEpsilon.
exists r;split;first exact:hr.
move=>t ht;have hh:=hBound t ht;by rewrite hValue subr0 in hh.
Qed.
