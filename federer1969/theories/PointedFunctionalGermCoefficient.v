(** Supporting Federer (1969), 3.4.8(1),(5),
    pp. 326, 328: an actual pointed linear coordinate
    has only its first divided directional coefficient.
    The proof uses the exact polynomial on each
    affine line and actual Taylor uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormAnalyticUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermNeighbourhood AnalyticDirectionalCoefficient
  AnalyticDirectionalPolynomialLine AnalyticGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_functional_germ_directional_coefficient]:
    the actual coordinate germ xi(x-a) has divided
    coefficient xi(v) in order one and zero in
    every other order, supporting 3.4.8(1),(5),
    pp. 326, 328, from 3.1.24, p. 240. *)
Lemma pointed_functional_germ_directional_coefficient (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a (xi:Hom X R^o)
  (f:@analytic_representative_type R X NX hNX a) k v:
  (forall x,analytic_representative_value f x = xi (x-a)) ->
  @analytic_germ_directional_coefficient R X NX hNX a k (analytic_germ f) v =
    if k==1%N then xi v else 0.
Proof.
move=>hValues.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose F:=analytic_representative_value f.
have [U [ha [_ [_ hF]]]]:=@analytic_germ_open_representative R X R^o NX NS hNX hNS
  setT F a (analytic_representative_analytic f).
have [c [hc _]]:=@analytic_directional_coefficient_exists R X R^o NX NS hNX hNS U F k v hF.
have hActual:=@analytic_directional_coefficient_at_germ_centre R X NX hNX a k
  (analytic_germ f) f U v c (erefl _) ha hF hc.
pose b:=fun j:nat=>if j==0%N then (0:R^o) else xi v.
have hLine t (ht:`|t|<1):F (a+t*:v)=\sum_(j<2) t^+j*:b j.
  rewrite /F hValues [a+t*:v]addrC addrK linearZ /=.
  rewrite !big_ord_recl big_ord0 /= /b expr0 expr1 scaler0 addr0 add0r.
  reflexivity.
have hValue:=@analytic_directional_polynomial_line_coefficient R X R^o NX NS hNX hNS
  U F k v a c 2%N b 1 ha hF hc ltr01 hLine.
rewrite -hActual hValue /b.
clear hc hActual hValue;by case:k=>[|[|k]].
Qed.
