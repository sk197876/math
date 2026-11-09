(** Federer (1969), 3.4.5, p. 321: finitely many
    actual analytic coefficient functions have one finite
    bound on one original endpoint neighbourhood. This
    supports the flat-coefficient argument in the cited example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import RealNormUP NormClassOneUP NormRegularity NormClassZeroTopology NormAnalyticUP
  FinitePositiveRadiusCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_coefficient_bound]: a common
    positive-side bound for the actual finite coefficient
    family, supporting the example cited at 3.4.5, p. 321.
    Empty families retain a positive unit bound. *)
Theorem finite_analytic_coefficient_bound (R:realType) (I:finType) (f:I->R->R):
  (forall i,@norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) setT (f i) 0) ->
  exists r C:R,0<r /\0<C /\forall t:R,0<t<r ->forall i,`|f i t|<=C.
Proof.
move=>hAnalytic.
pose C:R:=(\sum_(i:I) `|f i 0|)+1.
have hSum:0<=\sum_(i:I) `|f i 0| by apply:sumr_ge0=>i _;exact:normr_ge0.
have hC:0<C by rewrite /C addrC ltr_pwDl.
have hEach i:`|f i 0|+1<=C.
  rewrite /C lerD2r (bigD1 i) //=.
  have hRest:0<=\sum_(j:I | j!=i) `|f j 0| by apply:sumr_ge0=>j _;exact:normr_ge0.
  have hh:=lerD (lexx (`|f i 0|)) hRest;by rewrite addr0 in hh.
have hRadius i:exists d:R,0<d /\forall t:R,0<t<d ->`|f i t|<=C.
  have [U [c [hU0 [hUT [hSmooth hBound]]]]]:=hAnalytic i.
  have hContinuous:=norm_class_continuous (hSmooth 0%N).
  have [d [hd hControl]]:=@norm_class_zero_local_control R R^o R^o
    (fun t=>`|t|) (fun t=>`|t|) (@scalar_absolute_value_norm R) U (f i) 0 1 hContinuous hU0 ltr01.
  exists d;split;first exact:hd.
  move=>t /andP [ht htSmall].
  have hNorm:`|t-0|=t by rewrite subr0 ger0_norm //;exact:ltW ht.
  have [_ hDifference]:=hControl t (eq_ind_r (fun q:R=>q<d) htSmall hNorm).
  have hTriangle:=ler_normD (f i t-f i 0) (f i 0).
  rewrite subrK in hTriangle.
  apply:le_trans hTriangle _.
  apply:le_trans _ (hEach i);rewrite addrC lerD2l;exact:ltW hDifference.
have [r [hr hBound]]:=@finite_common_positive_radius_bound R I
  (fun i t=>`|f i t|<=C) hRadius.
exists r,C;by split=>//;split.
Qed.
