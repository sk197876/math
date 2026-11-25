(** Federer (1969), 3.4.12, p. 338:
    every original holomorphic function has a unique
    actual complex linear differential at each domain point.
    Reuse analytic smoothness, ordinary differential uniqueness
    and the proved scalar-restriction map connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  NormDifferentialUP NormDifferentialDirectional NormRegularity NormClassOneUP NormAnalyticLocal
  ComplexRealLinearMap HolomorphicUP HolomorphicDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Differential.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable NY:Y->R.
Variable hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x).
Variable hNY:is_real_norm (fun y:restricted_space (ComplexScalars.embed R) Y=>NY y).
Variables (A:set X) (f:X->Y).

(** Source for [holomorphic_differential_exists]: the actual
    original complex differential in 3.4.12, p. 338,
    exists at every domain point. Analyticity supplies
    its real derivative, and its original complex scalar
    law gives the complex linear carrier. *)
Theorem holomorphic_differential_exists:
  is_holomorphic hNX hNY A f ->forall a,A a ->exists D:Hom X Y,
    is_holomorphic_differential NX NY A f a D.
Proof.
move=>hHolomorphic a ha.
have hClass:=norm_analytic_class_all_orders hHolomorphic.1 1%N.
have [L hL]:=(norm_class_firstP hNX hNY A f).1 hClass.
have hActual:=norm_class_one_differential hL ha.
have hComplex:=hHolomorphic.2 a (L a) ha hActual.
have [D hValues]:=complex_real_linear_map_exists hComplex.
exists D,(L a);by split.
Qed.

(** Source for [holomorphic_differential_unique]: the original
    real differential uniqueness determines the complex differential
    uniquely, supporting 3.4.12, p. 338. *)
Lemma holomorphic_differential_unique a (D E:Hom X Y):
  is_holomorphic_differential NX NY A f a D ->
  is_holomorphic_differential NX NY A f a E ->D=E.
Proof.
move=>[L [hL hD]] [M [hM hE]].
have hEqual:=norm_differential_unique hNX hNY hL hM.
apply:hom_ext=>x;by rewrite hD hE hEqual.
Qed.
End Differential.
