(** Federer (1969), 3.4.5, p. 321: a smooth
    scalar function negligible to every order from one side
    has every actual jet zero at that endpoint. This
    expands 3.1.11's Taylor remainder, p. 221, for the
    flat-coefficient argument in the cited analytic example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom RealNormUP NormClassOneUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm ContinuousMultilinearScalar NormHigherDifferentialUP
  NormTaylorRemainderBound NormTaylorLineRemainder NormLittleOPower ScalarRightLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_smooth_right_flat_jets]: actual
    Taylor coefficients vanish under all positive-side
    power estimates, supporting the example cited at
    3.4.5, p. 321. The derivatives are original
    recursive differentials, not an assumed formal series. *)
Theorem scalar_smooth_right_flat_jets (R:realType) (A:R->Prop) (f:R->R)
    (D:forall m,R->@ContinuousMultilinear.space R m R^o R^o
      (fun t=>`|t|) (fun t=>`|t|) (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)):
  A 0 ->norm_class_zero (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) A f ->
  (forall m x,A x ->has_norm_higher_differential (fun t:R^o=>`|t|)
    (fun i=>@ContinuousMultilinear.evaluation R i R^o R^o (fun t=>`|t|) (fun t=>`|t|)
      (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R))
    (fun i=>@ContinuousMultilinear.norm R i R^o R^o (fun t=>`|t|) (fun t=>`|t|)
      (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)) A f m x (D m x)) ->
  (forall m,norm_class_zero (fun t:R^o=>`|t|)
    (@ContinuousMultilinear.norm R m R^o R^o (fun t=>`|t|) (fun t=>`|t|)
      (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)) A (D m)) ->
  (forall m,scalar_right_little_o_power f m) ->forall m,D m 0=0.
Proof.
move=>hA hF hD hContinuous hFlat.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose NZ i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
move=>m;elim/ltn_ind:m=>m ih.
pose c:R:=(m`!)%:R^-1*ev m [ffun i:'I_m=>(1:R^o)] (D m 0).
have hTaylor (t:R):@norm_taylor_value R R^o R^o Z ev D 0 t m=t^+m*c.
  rewrite /norm_taylor_value big_ord_recr /=.
  have hPrefix:(\sum_(i<m) (i`!)%:R^-1*:ev i [ffun _=>t] (D i 0))=0.
    apply:big1=>i _;by rewrite (ih i (ltn_ord i)) linear0 scaler0.
  rewrite hPrefix add0r (continuous_multilinear_scalar_evaluation (hZ m)).
  have hProduct:(\prod_(i<m) [ffun _:'I_m=>t] i)=t^+m.
    under eq_bigr do rewrite ffunE.
    by rewrite prodr_const card_ord.
  rewrite hProduct /c.
  change ((m`!)%:R^-1*(t^+m*ev m [ffun i:'I_m=>(1:R^o)] (D m 0))=
    t^+m*((m`!)%:R^-1*ev m [ffun i:'I_m=>(1:R^o)] (D m 0)));ring.
have hRemainder:=@norm_taylor_line_little_o_fields R R^o R^o N N hN hN
  Z ev NZ hZ A f D m 0 1 hA hF (fun i _=>hD i) (hContinuous m).
have hFunction:(fun t:R=>f (0+t*:(1:R^o))-
    @norm_taylor_value R R^o R^o Z ev D 0 (t*:(1:R^o)) m)=(fun t=>f t-t^+m*c).
  apply:funext=>t.
  change (f (0+t*1)-@norm_taylor_value R R^o R^o Z ev D 0 (t*1) m=f t-t^+m*c).
  by rewrite mulr1 add0r hTaylor.
rewrite hFunction in hRemainder.
have hC:c=0:=@scalar_right_monomial_coefficient_zero R f m c (hFlat m)
  (@scalar_little_o_right_restriction R _ m hRemainder).
have hFactorial:((m`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hValue:ev m [ffun i:'I_m=>(1:R^o)] (D m 0)=0.
  have hh:=congr1 (fun q:R=>(m`!)%:R*q) hC.
  by rewrite /c mulrA mulfV // mul1r mulr0 in hh.
apply:(continuous_multilinear_norm_is_norm hN (hZ m)).2.
by rewrite (continuous_multilinear_scalar_norm hN (hZ m)) hValue /N normr0.
Qed.
