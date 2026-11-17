(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 330:
    choose actual original coefficient functions
    with leading coefficient identically one
    and lower values zero at the
    original centre. Use the existing germ
    representative and centre-value laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP HolomorphicLinear HolomorphicRestriction HolomorphicFiniteCalculus HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRingLaws HolomorphicGermValueSealed DistinguishedPolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [distinguished_holomorphic_coefficient_actual_representatives]:
    b_(i,m+1)(0)=0 and the actual
    leading coefficient one in 3.4.12, p. 339, extending 3.4.8(10),
    p. 327. Representatives are local
    existence witnesses, chosen only after
    the original distinguished laws are proved.
    Degree zero remains in this supporting theorem. *)
Theorem distinguished_holomorphic_coefficient_actual_representatives (R:realType) (Y:lmodType (ComplexScalars.C R))
  (NY:Y->R) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (P:Type)
  (coefficient:P->nat->@holomorphic_germ_ring R Y NY hNY 0) (W:P) k:
  is_distinguished_polynomial coefficient (@HolomorphicGermValue.map R Y NY hNY 0) W k ->
  exists b:'I_k.+1->@holomorphic_representative_type R Y NY hNY 0,
    (forall i:'I_k.+1,holomorphic_germ (b i) = coefficient W i) /\
    (forall y:Y,holomorphic_representative_value (b ord_max) y = 1) /\
    forall i:'I_k.+1,(i<k)%N ->holomorphic_representative_value (b i) 0 = 0.
Proof.
move=>hW.
pose G:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
have hEach (i:'I_k.+1):exists f:@holomorphic_representative_type R Y NY hNY 0,
    (holomorphic_germ f:G) = coefficient W i /\
    (i = ord_max ->forall y,holomorphic_representative_value f y = 1).
  case:(eqVneq i ord_max)=>[->|hOther].
  - exists (@holomorphic_constant_representative R Y NY hNY 0 1);split;last by [].
    change ((1:G) = coefficient W k);exact:esym hW.1.2.
  - have [f hF]:=@holomorphic_germ_has_representative R Y NY hNY 0 (coefficient W i).
    exists f;split;first exact:hF.
    move=>hEqual;by rewrite hEqual eqxx in hOther.
have [b hB]:=choice hEach.
exists b;split;first by move=>i;exact:(hB i).1.
split;first exact:(hB ord_max).2 erefl.
move=>i hSmall.
have hValue:=congr1 (@HolomorphicGermValue.map R Y NY hNY 0) (hB i).1.
rewrite (@HolomorphicGermValue.laws R Y NY hNY 0) in hValue.
by rewrite hValue (hW.2 i hSmall).
Qed.
