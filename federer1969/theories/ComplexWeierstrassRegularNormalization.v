(** Federer (1969), 3.4.12, p. 339: normalize the original
    nonzero complex divided leading coefficient without changing the
    original direction or transverse functional. Actual scalar germ
    arithmetic proves the normalization internally. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP SymmetricForms
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermFormsUP HolomorphicGermFormsSealed ComplexWeierstrassRegularUP
  ComplexWeierstrassRegularCoefficients ComplexWeierstrassScalarGermArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Normalization.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation C:=(ComplexScalars.C R).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation G:=(@holomorphic_germ_ring R X NX hNXR 0).
Local Notation constant:=(fun c:C=>holomorphic_germ (@holomorphic_constant_representative R X NX hNXR 0 c)).

(** Source for [complex_weierstrass_regular_normalization]: actual
    original regularity yields a nonzero normalizing scalar and
    a regular original germ with divided leading coefficient one,
    extending 3.4.6, p. 322, under 3.4.12, p. 339. *)
Theorem complex_weierstrass_regular_normalization k (v:X) (Phi:G):
  is_complex_weierstrass_regular_germ hNX Phi k v ->
  exists c:C,c!=0 /\is_complex_weierstrass_regular_germ hNX ((constant c:G)*Phi) k v /\
    ((((k`!)%:R)^-1:C)*@HolomorphicGermForms.value R X NX hNX 0 k
      ((constant c:G)*Phi) [tuple v | j<k])= 1.
Proof.
move=>hRegular.
pose a:=(((k`!)%:R)^-1:C)*@HolomorphicGermForms.value R X NX hNX 0 k Phi [tuple v | j<k].
have hA:a!=0 by apply/eqP;exact:complex_weierstrass_regular_leading_nonzero hRegular.
pose c:=a^-1.
pose gamma:G:=(constant c:G)*Phi.
have hScale i:@HolomorphicGermForms.value R X NX hNX 0 i gamma [tuple v | j<i]=
    c*@HolomorphicGermForms.value R X NX hNX 0 i Phi [tuple v | j<i].
  by rewrite /gamma complex_weierstrass_scalar_germ_form sform_scaleE.
have hUnit:(((k`!)%:R)^-1:C)*@HolomorphicGermForms.value R X NX hNX 0 k gamma [tuple v | j<k]= 1.
  rewrite hScale.
  have hReorder:(((k`!)%:R)^-1:C)*(c*@HolomorphicGermForms.value R X NX hNX 0 k Phi [tuple v | j<k])=c*a.
    by rewrite /a;ring.
  by rewrite hReorder /c mulVf.
exists c;split;first by rewrite /c invr_eq0.
split;last exact:hUnit.
split;first exact:hRegular.1.
split.
- move=>i hi;by rewrite hScale (hRegular.2.1 i hi) mulr0.
- move=>hZero.
  have hImpossible:=hUnit;rewrite hZero mulr0 in hImpossible.
  have hNot:(1:C)!=0:=oner_neq0 C.
  by rewrite -hImpossible eqxx in hNot.
Qed.
End Normalization.
