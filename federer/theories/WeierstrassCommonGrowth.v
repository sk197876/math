(** Federer (1969), 3.4.6, p. 324: a single
    positive pair of geometric constants bounds both original
    input coefficient families. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_common_coefficient_growth]: the
    two original analytic coefficient bounds can use common
    finite positive constants, as required for the recursion
    estimate in 3.4.6, p. 324. Sum padding
    proves their existence without a new bound hypothesis. *)
Lemma weierstrass_common_coefficient_growth (R:realType) (K:Type) (P:K->Prop)
    (phi psi:nat->nat->K->R) (b1 c1 b2 c2:R):
  0<b1 ->0<c1 ->0<b2 ->0<c2 ->
  (forall i j z,P z ->`|phi i j z|<=b1*c1^+(i+j)) ->
  (forall i j z,P z ->`|psi i j z|<=b2*c2^+(i+j)) ->
  exists b c:R,0<b /\0<c /\
    (forall i j z,P z ->`|phi i j z|<=b*c^+(i+j)) /\
    (forall i j z,P z ->`|psi i j z|<=b*c^+(i+j)).
Proof.
move=>hb1 hc1 hb2 hc2 hPhi hPsi.
pose b:=b1+b2.
pose c:=c1+c2.
have hb:0<b by rewrite /b addr_gt0.
have hc:0<c by rewrite /c addr_gt0.
have hB1:b1<=b by rewrite /b lerDl;exact:ltW hb2.
have hB2:b2<=b by rewrite /b lerDr;exact:ltW hb1.
have hC1:c1<=c by rewrite /c lerDl;exact:ltW hc2.
have hC2:c2<=c by rewrite /c lerDr;exact:ltW hc1.
exists b,c;split;first exact:hb.
split;first exact:hc.
split=>i j z hz.
- apply:le_trans (@hPhi i j z hz) _.
  exact:le_trans (ler_wpM2r (exprn_ge0 (i+j)%N (ltW hc1)) hB1)
    (ler_wpM2l (ltW hb) (lerXn2r (i+j)%N (ltW hc1) (ltW hc) hC1)).
- apply:le_trans (@hPsi i j z hz) _.
  exact:le_trans (ler_wpM2r (exprn_ge0 (i+j)%N (ltW hc2)) hB2)
    (ler_wpM2l (ltW hb) (lerXn2r (i+j)%N (ltW hc2) (ltW hc) hC2)).
Qed.
