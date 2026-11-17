(** Federer (1969), 3.4.8(10), pp. 327, 330:
    choose actual original coefficient functions
    with leading coefficient identically one
    and lower values zero at the
    original centre. Use the existing germ
    representative and centre-value laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  AnalyticGermRingLaws AnalyticGermValueSealed DistinguishedPolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [distinguished_coefficient_actual_representatives]:
    b_(i,m+1)(0)=0 and the actual
    leading coefficient one in 3.4.8(10),
    p. 327. Representatives are local
    existence witnesses, chosen only after
    the original distinguished laws are proved.
    Degree zero remains in this supporting theorem. *)
Theorem distinguished_coefficient_actual_representatives (R:realType) (Y:lmodType R)
  (NY:Y->R) (hNY:is_real_norm NY) (P:Type)
  (coefficient:P->nat->@analytic_germ_ring R Y NY hNY 0) (W:P) k:
  is_distinguished_polynomial coefficient (@AnalyticGermValue.map R Y NY hNY 0) W k ->
  exists b:'I_k.+1->@analytic_representative_type R Y NY hNY 0,
    (forall i:'I_k.+1,analytic_germ (b i) = coefficient W i) /\
    (forall y:Y,analytic_representative_value (b ord_max) y = 1) /\
    forall i:'I_k.+1,(i<k)%N ->analytic_representative_value (b i) 0 = 0.
Proof.
move=>hW.
pose G:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
have hEach (i:'I_k.+1):exists f:@analytic_representative_type R Y NY hNY 0,
    (analytic_germ f:G) = coefficient W i /\
    (i = ord_max ->forall y,analytic_representative_value f y = 1).
  case:(eqVneq i ord_max)=>[->|hOther].
  - exists (@analytic_constant_representative R Y NY hNY 0 1);split;last by [].
    change ((1:G) = coefficient W k);exact:esym hW.1.2.
  - have [f hF]:=@analytic_germ_has_representative R Y NY hNY 0 (coefficient W i).
    exists f;split;first exact:hF.
    move=>hEqual;by rewrite hEqual eqxx in hOther.
have [b hB]:=choice hEach.
exists b;split;first by move=>i;exact:(hB i).1.
split;first exact:(hB ord_max).2 erefl.
move=>i hSmall.
have hValue:=congr1 (@AnalyticGermValue.map R Y NY hNY 0) (hB i).1.
rewrite (@AnalyticGermValue.laws R Y NY hNY 0) in hValue.
by rewrite hValue (hW.2 i hSmall).
Qed.
