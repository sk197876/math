(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    pp. 320–321: finite holomorphic variety germs are closed
    under union and intersection. Use products and concatenation
    of the original finite equation families on a common domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric SetGermUP SetGermSealed
  SetGermLaws SetGermLocality FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyLaws
  FiniteHolomorphicVarietyBoundary FiniteHolomorphicVarietyRestriction HolomorphicVarietyGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Closure.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation V sigma:=(@is_holomorphic_variety_germ R X NX hNX a sigma).

(** Source for [holomorphic_variety_germ_empty]: the original
    empty germ is a variety germ, 3.4.12, p. 339. *)
Lemma holomorphic_variety_germ_empty:V (@set_germ T a set0).
Proof.
exists setT,set0;split;first exact:Logic.I.
split;last reflexivity.
exact:(@finite_holomorphic_variety_domain_empty R X NX hNX setT openT).
Qed.

(** Source for [holomorphic_variety_germ_whole]: the original
    whole-space germ is a variety germ, 3.4.12, p. 339. *)
Lemma holomorphic_variety_germ_whole:V (@set_germ T a setT).
Proof.
exists setT,setT;split;first exact:Logic.I.
split;last reflexivity.
exact:(@finite_holomorphic_variety_domain_whole R X NX hNX setT openT).
Qed.

(** Source for [holomorphic_variety_germ_union]: the original
    union is holomorphic, 3.4.12, p. 339. *)
Lemma holomorphic_variety_germ_union (alpha beta:@set_germ_space T a):
  V alpha ->V beta ->V (@SetGerms.join T a alpha beta).
Proof.
move=>[U [S [ha [hS hAlpha]]]] [W [Z [hb [hZ hBeta]]]].
pose O:=U `&` W.
have hO:@open T O:=openI hS.1 hZ.1.
have haO:O a by split.
have hSO:=finite_holomorphic_variety_open_restriction hS hO (fun x hx=>hx.1).
have hZO:=finite_holomorphic_variety_open_restriction hZ hO (fun x hx=>hx.2).
exists O,((O `&` S) `|` (O `&` Z));split;first exact:haO.
split;first exact:finite_holomorphic_variety_union hSO hZO.
rewrite -(@set_germ_union_equation T a _ _ _ (@SetGerms.laws T a))
  !(@set_germ_neighbourhood_intersection T a O _ hO haO).
by rewrite hAlpha hBeta.
Qed.

(** Source for [holomorphic_variety_germ_intersection]: the
    original intersection is holomorphic, 3.4.12, p. 339. *)
Lemma holomorphic_variety_germ_intersection (alpha beta:@set_germ_space T a):
  V alpha ->V beta ->V (@SetGerms.meet T a alpha beta).
Proof.
move=>[U [S [ha [hS hAlpha]]]] [W [Z [hb [hZ hBeta]]]].
pose O:=U `&` W.
have hO:@open T O:=openI hS.1 hZ.1.
have haO:O a by split.
have hSO:=finite_holomorphic_variety_open_restriction hS hO (fun x hx=>hx.1).
have hZO:=finite_holomorphic_variety_open_restriction hZ hO (fun x hx=>hx.2).
exists O,((O `&` S) `&` (O `&` Z));split;first exact:haO.
split;first exact:finite_holomorphic_variety_intersection hSO hZO.
rewrite -(@set_germ_intersection_equation T a _ _ _ (@SetGerms.laws T a))
  !(@set_germ_neighbourhood_intersection T a O _ hO haO).
by rewrite hAlpha hBeta.
Qed.
End Closure.
