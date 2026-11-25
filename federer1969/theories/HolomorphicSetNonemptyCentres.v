(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    for a locally holomorphic set, the centres
    with nonempty germs are exactly its original
    points in the holomorphic domain. This justifies
    the point-indexed form of the dimension supremum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric SetGermUP SetGermExistence
  SetGermCentreMember HolomorphicVarietyGermUP HolomorphicSetLocalCover
  FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyRelativeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_set_outside_empty_neighbourhood]: the
    local closedness implicit in the dimension
    definition of 3.4.10, p. 337.
    The existing finite-equation representative is closed
    relative to its actual open domain. *)
Theorem holomorphic_set_outside_empty_neighbourhood (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (U S:set X) a:
  @is_holomorphic_set_in R X NX hNX U S ->U a ->~S a ->
  exists W:set X,@open (real_norm_metric_space hNX) W /\W a /\S `&` W=set0.
Proof.
move=>hHolomorphic haU haNot.
have hCover:=(@holomorphic_set_local_cover_equivalence R X NX hNX U S).1 hHolomorphic.
have [V [haV hVariety]]:=hCover a haU.
have [C [hC hEquation]]:=finite_holomorphic_variety_relative_closed_form hVariety.
have haNotC:~C a.
  move=>haC;apply:haNot;have h:(V `&` S) a by rewrite hEquation;split.
  exact:h.2.
exists (V `&` ~` C);split;first exact:openI hVariety.1 (closed_openC hC).
split;first by split.
apply/seteqP;split;last by move=>x.
move=>x [hxS [hxV hxNot]];apply:hxNot.
have h:(V `&` S) x by split.
by rewrite hEquation in h;exact:h.2.
Qed.

(** Source for [holomorphic_set_nonempty_germ_centres]: the
    original family in the dimension supremum
    of 3.4.10, p. 337, omits
    precisely the empty germs at points outside
    the actual holomorphic set. *)
Theorem holomorphic_set_nonempty_germ_centres (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (U S:set X) a:
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_holomorphic_set_in R X NX hNX U S ->U a ->
  (@set_germ T a S<>@set_germ T a set0)<->S a.
Proof.
move=>T hHolomorphic haU;split.
- move=>hNonempty;apply:contrapT=>haNot;apply:hNonempty.
  have [W [hW [haW hEmpty]]]:=holomorphic_set_outside_empty_neighbourhood hHolomorphic haU haNot.
  apply/set_germ_equality_original;exists W;split;first exact:hW.
  split;first exact:haW.
  by rewrite hEmpty set0I.
- exact:set_germ_centre_member_nonempty.
Qed.
