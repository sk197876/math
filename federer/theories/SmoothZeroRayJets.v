(** Federer (1969), 3.4.5, p. 321: vanishing
    on an actual cone forces its Taylor polynomials to
    vanish there. This internal step uses the original
    linewise Taylor remainder of 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring boolp functions.
From Federer Require Import Hom RealNormUP NormClassOneUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormTaylorRemainderBound NormTaylorLineValues NormTaylorLineRemainder
  NormLittleOPower ScalarRightLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [smooth_zero_ray_diagonal_jets]: every
    actual Taylor coefficient vanishes on a direction
    whose positive ray is locally a zero ray,
    supporting the cubic-cone proof in 3.4.5, p. 321.
    Neither analyticity nor finite dimension is assumed here. *)
Theorem smooth_zero_ray_diagonal_jets (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop) (f:X->R)
    (D:forall m,X->@ContinuousMultilinear.space R m X R^o NX (fun t=>`|t|)
      hNX (@scalar_absolute_value_norm R)) (v:X) (r:R):
  A 0 ->norm_class_zero NX (fun t:R^o=>`|t|) A f ->
  (forall m x,A x ->has_norm_higher_differential NX
    (fun i=>@ContinuousMultilinear.evaluation R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
    (fun i=>@ContinuousMultilinear.norm R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
      A f m x (D m x)) ->
  (forall m,norm_class_zero NX
    (@ContinuousMultilinear.norm R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)) A (D m)) ->
  0<r ->(forall t:R,0<t<r ->f (t*:v)=0) ->
  forall m,@ContinuousMultilinear.evaluation R m X R^o NX (fun t=>`|t|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_m=>v] (D m 0)=0.
Proof.
move=>hA hF hD hContinuous hr hRay.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
pose g:=fun t:R=>f (t*:v).
have hFlat m:scalar_right_little_o_power g m.
  move=>epsilon hEpsilon;exists r;split;first exact:hr.
  move=>t ht;rewrite /g (hRay t ht) normr0.
  exact:(mulr_ge0 (ltW hEpsilon) (exprn_ge0 _ (ltW (andP ht).1))).
move=>m;elim/ltn_ind:m=>m ih.
pose c:R:=(m`!)%:R^-1*ev m [ffun _:'I_m=>v] (D m 0).
have hTaylor (t:R):@norm_taylor_value R X R^o Z ev D 0 (t*:v) m=t^+m*c.
  rewrite (@norm_taylor_value_on_line R X R^o NX N Z ev NZ hZ D 0 v t m) big_ord_recr /=.
  have hPrefix:(\sum_(i<m) t^+i*:((i`!)%:R^-1*:ev i [ffun _:'I_i=>v] (D i 0)))=0.
    apply:big1=>i _;by rewrite (ih i (ltn_ord i)) !scaler0.
  by rewrite hPrefix add0r.
have hRemainder:=@norm_taylor_line_little_o_fields R X R^o NX N hNX hN
  Z ev NZ hZ A f D m 0 v hA hF (fun i _=>hD i) (hContinuous m).
have hFunction:(fun t:R=>f (0+t*:v)-@norm_taylor_value R X R^o Z ev D 0 (t*:v) m)=
    (fun t=>g t-t^+m*c).
  by apply:funext=>t;rewrite add0r hTaylor.
rewrite hFunction in hRemainder.
have hC:c=0:=@scalar_right_monomial_coefficient_zero R g m c (hFlat m)
  (@scalar_little_o_right_restriction R _ m hRemainder).
have hFactorial:((m`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hValue:=congr1 (fun q:R=>(m`!)%:R*q) hC.
by rewrite /c mulrA mulfV // mul1r mulr0 in hValue.
Qed.
