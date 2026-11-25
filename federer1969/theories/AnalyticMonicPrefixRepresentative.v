(** Federer (1969), 3.4.8(8), p. 330:
    the original monic integral relation
    restricts to a monic scalar polynomial
    on the original coordinate line. Use
    actual prefix representatives and the
    existing power and finite-sum representative theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermUP AnalyticGermSealed AnalyticGermRing
  AnalyticGermRingLaws AnalyticGermRepresentatives AnalyticGermPowers AnalyticGermFiniteSum
  PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_monic_prefix_line_representative]:
    a monic coordinate relation with original
    prefix coefficients has an actual monic
    polynomial line representative, 3.4.8(8),
    p. 330. Prefix coefficients are constant
    on this line. The actual representative
    witnesses do not change the original germ. *)
Theorem analytic_monic_prefix_line_representative (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (P:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]})
  (xi:Hom X R^o) (fXi:@analytic_representative_type R X NX hNX 0)
  k (beta:nat->@analytic_germ_ring R Y NY hNY 0) (v:X):
  is_pointed_analytic_germ_pullback P E ->
  (forall x:X,analytic_representative_value fXi x = xi x) ->
  P v = 0 ->xi v = 1 ->
  exists (f:@analytic_representative_type R X NX hNX 0) (a:nat->R),
    (analytic_germ f:@analytic_germ_ring R X NX hNX 0) =
      (analytic_germ fXi:@analytic_germ_ring R X NX hNX 0)^+k-
        \sum_(i<k) E (beta i)*(analytic_germ fXi:@analytic_germ_ring R X NX hNX 0)^+(i:nat) /\
    forall t:R,analytic_representative_value f (t*:v) = t^+k+\sum_(i<k) a i*t^+(i:nat).
Proof.
move=>hE hXi hPZero hXiOne.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
have hXiLine t:xi (t*:v) = t.
  have hLinear:=@linearZZ R X R^o (hom_as_linear xi) t v.
  change (xi (t*:v) = t*xi v) in hLinear.
  by rewrite hLinear hXiOne mulr1.
have hEach i:exists g:@analytic_representative_type R X NX hNX 0,
    (analytic_germ g:G) = E (beta i) /\exists a:R,forall t:R,analytic_representative_value g (t*:v) = a.
  have [f hF]:=@analytic_germ_has_representative R Y NY hNY 0 (beta i).
  have [g [hG hValues]]:=hE f.
  exists g;split;first by rewrite hF in hG;exact:esym hG.
  exists (analytic_representative_value f 0)=>t.
  by rewrite hValues linearZ /= hPZero scaler0.
have [F hF]:=choice hEach.
pose a:=fun i=>projT1 (cid (hF i).2).
have hFLine i t:analytic_representative_value (F i) (t*:v) = a i:=projT2 (cid (hF i).2) t.
have hPowers i:=@analytic_representative_power_exists R X NX hNX 0 fXi i.
pose power:=fun i=>projT1 (cid (hPowers i)).
have hPowerValues i x:analytic_representative_value (power i) x = (xi x)^+i.
  by rewrite (projT2 (cid (hPowers i))).1 hXi.
have hPowerGerm i:(analytic_germ (power i):G) = (analytic_germ fXi:G)^+i:=
  (projT2 (cid (hPowers i))).2.
pose term:=fun i=>@analytic_multiply_representatives R X NX hNX 0 (F i) (power i).
pose terms:=map (fun i:'I_k=>term (i:nat)) (enum 'I_k).
have [sumRep [hSumValues hSumGerm]]:=@analytic_finite_sum_representative R X NX hNX 0 terms.
have hSumLine t:analytic_representative_value sumRep (t*:v) = \sum_(i<k) a i*t^+(i:nat).
  rewrite hSumValues /terms big_map -[RHS]big_enum.
  apply:eq_bigr=>i _.
  change (analytic_representative_value (F i) (t*:v)*analytic_representative_value (power i) (t*:v) = a i*t^+(i:nat)).
  by rewrite hFLine hPowerValues hXiLine.
have hSumClass:(analytic_germ sumRep:G) = \sum_(i<k) E (beta i)*(analytic_germ fXi:G)^+(i:nat).
  rewrite hSumGerm /terms big_map -[RHS]big_enum.
  apply:eq_bigr=>i _.
  rewrite -(analytic_germ_multiply_equation (@AnalyticGerms.laws R X NX hNX 0)).
  by rewrite (hF i).1 hPowerGerm.
pose f:=@analytic_add_representatives R X NX hNX 0 (power k)
  (@analytic_negate_representative R X NX hNX 0 sumRep).
exists f,(fun i=> -a i);split.
- rewrite -(analytic_germ_add_equation (@AnalyticGerms.laws R X NX hNX 0))
    -(analytic_germ_negate_equation (@AnalyticGerms.laws R X NX hNX 0)).
  by rewrite hPowerGerm hSumClass.
- move=>t;change (analytic_representative_value (power k) (t*:v)-analytic_representative_value sumRep (t*:v) =
    t^+k+\sum_(i<k) (-a i)*t^+(i:nat)).
  rewrite hPowerValues hXiLine hSumLine -sumrN.
  congr (t^+k+_);apply:eq_bigr=>i _;by rewrite mulNr.
Qed.
