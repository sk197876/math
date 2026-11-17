(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8), p. 330:
    the original monic integral relation
    restricts to a monic scalar polynomial
    on the original coordinate line. Use
    actual prefix representatives and the
    existing power and finite-sum representative theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP HolomorphicGermUP HolomorphicGermSealed HolomorphicGermRing
  HolomorphicGermRingLaws HolomorphicGermRepresentatives HolomorphicGermPowers HolomorphicGermFiniteSum
  PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_monic_prefix_line_representative]:
    a monic coordinate relation with original
    prefix coefficients has an actual monic
    polynomial line representative, 3.4.8(8),
    p. 330. Prefix coefficients are constant
    on this line. The actual representative
    witnesses do not change the original germ. *)
Theorem holomorphic_monic_prefix_line_representative (R:realType) (X Y:lmodType (ComplexScalars.C R))
  (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
  (P:Hom X Y)
  (E:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]})
  (xi:Hom X (ComplexScalars.C R)^o) (fXi:@holomorphic_representative_type R X NX hNX 0)
  k (beta:nat->@holomorphic_germ_ring R Y NY hNY 0) (v:X):
  is_pointed_holomorphic_germ_pullback P E ->
  (forall x:X,holomorphic_representative_value fXi x = xi x) ->
  P v = 0 ->xi v = 1 ->
  exists (f:@holomorphic_representative_type R X NX hNX 0) (a:nat->ComplexScalars.C R),
    (holomorphic_germ f:@holomorphic_germ_ring R X NX hNX 0) =
      (holomorphic_germ fXi:@holomorphic_germ_ring R X NX hNX 0)^+k-
        \sum_(i<k) E (beta i)*(holomorphic_germ fXi:@holomorphic_germ_ring R X NX hNX 0)^+(i:nat) /\
    forall t:ComplexScalars.C R,holomorphic_representative_value f (t*:v) = t^+k+\sum_(i<k) a i*t^+(i:nat).
Proof.
move=>hE hXi hPZero hXiOne.
pose G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
have hXiLine t:xi (t*:v) = t.
  have hLinear:=@linearZZ (ComplexScalars.C R) X (ComplexScalars.C R)^o (hom_as_linear xi) t v.
  change (xi (t*:v) = t*xi v) in hLinear.
  by rewrite hLinear hXiOne mulr1.
have hEach i:exists g:@holomorphic_representative_type R X NX hNX 0,
    (holomorphic_germ g:G) = E (beta i) /\exists a:ComplexScalars.C R,forall t:ComplexScalars.C R,holomorphic_representative_value g (t*:v) = a.
  have [f hF]:=@holomorphic_germ_has_representative R Y NY hNY 0 (beta i).
  have [g [hG hValues]]:=hE f.
  exists g;split;first by rewrite hF in hG;exact:esym hG.
  exists (holomorphic_representative_value f 0)=>t.
  by rewrite hValues linearZ /= hPZero scaler0.
have [F hF]:=choice hEach.
pose a:=fun i=>projT1 (cid (hF i).2).
have hFLine i t:holomorphic_representative_value (F i) (t*:v) = a i:=projT2 (cid (hF i).2) t.
have hPowers i:=@holomorphic_representative_power_exists R X NX hNX 0 fXi i.
pose power:=fun i=>projT1 (cid (hPowers i)).
have hPowerValues i x:holomorphic_representative_value (power i) x = (xi x)^+i.
  by rewrite (projT2 (cid (hPowers i))).1 hXi.
have hPowerGerm i:(holomorphic_germ (power i):G) = (holomorphic_germ fXi:G)^+i:=
  (projT2 (cid (hPowers i))).2.
pose term:=fun i=>@holomorphic_multiply_representatives R X NX hNX 0 (F i) (power i).
pose terms:=map (fun i:'I_k=>term (i:nat)) (enum 'I_k).
have [sumRep [hSumValues hSumGerm]]:=@holomorphic_finite_sum_representative R X NX hNX 0 terms.
have hSumLine t:holomorphic_representative_value sumRep (t*:v) = \sum_(i<k) a i*t^+(i:nat).
  rewrite hSumValues /terms big_map -[RHS]big_enum.
  apply:eq_bigr=>i _.
  change (holomorphic_representative_value (F i) (t*:v)*holomorphic_representative_value (power i) (t*:v) = a i*t^+(i:nat)).
  by rewrite hFLine hPowerValues hXiLine.
have hSumClass:(holomorphic_germ sumRep:G) = \sum_(i<k) E (beta i)*(holomorphic_germ fXi:G)^+(i:nat).
  rewrite hSumGerm /terms big_map -[RHS]big_enum.
  apply:eq_bigr=>i _.
  rewrite -(holomorphic_germ_multiply_equation (@HolomorphicGerms.laws R X NX hNX 0)).
  by rewrite (hF i).1 hPowerGerm.
pose f:=@holomorphic_add_representatives R X NX hNX 0 (power k)
  (@holomorphic_negate_representative R X NX hNX 0 sumRep).
exists f,(fun i=> -a i);split.
- rewrite -(holomorphic_germ_add_equation (@HolomorphicGerms.laws R X NX hNX 0))
    -(holomorphic_germ_negate_equation (@HolomorphicGerms.laws R X NX hNX 0)).
  by rewrite hPowerGerm hSumClass.
- move=>t;change (holomorphic_representative_value (power k) (t*:v)-holomorphic_representative_value sumRep (t*:v) =
    t^+k+\sum_(i<k) (-a i)*t^+(i:nat)).
  rewrite hPowerValues hXiLine hSumLine -sumrN.
  congr (t^+k+_);apply:eq_bigr=>i _;by rewrite mulNr.
Qed.
