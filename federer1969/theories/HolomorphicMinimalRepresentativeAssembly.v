(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(12), pp. 327, 335:
    the union of stratum components accumulating at zero
    is contained in every original holomorphic supergerm.
    Use the finite component selection and the already
    proved holomorphic continuation on each actual component. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SetGermUP SetGermOrder SetGermExistence
  FiniteHolomorphicVarietyUP FunctionalHolomorphicSubmanifoldUP FunctionalHolomorphicManifold
  HolomorphicFiniteStratificationUP FiniteFamilyGermCore HolomorphicComponentIdentity
  HolomorphicMinimalRepresentativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section MinimalAssembly.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation E:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ E 0).

(** Source for [holomorphic_minimal_representative_from_strata]:
    the exact component union in the printed proof
    of 3.4.8(12), p. 335. Only the
    necessary finite-stratum laws are used here; the
    full original theorem supplies them separately. *)
Theorem holomorphic_minimal_representative_from_strata
    (alpha:@set_germ_space E 0) (U:set X) mu
    (V S:'I_mu->set X):
  (forall i,@open E (V i) /\V i `<=` U) ->
  (forall i,exists d,@is_functional_holomorphic_submanifold R n d (V i) (S i)) ->
  (forall i,finite_set (@connected_component E (S i) @` S i)) ->
  germ (\bigcup_i S i)=alpha ->
  exists H:set X,@is_holomorphic_minimal_representative R n alpha U H.
Proof.
move=>hV hFunctional hComponents hGerm.
pose F:set (set E):=\bigcup_i (@connected_component E (S i) @` S i).
have hFinite:finite_set F:=bigcup_finite (@finite_finset 'I_mu setT)
  (fun i hi=>hComponents i).
pose H:set X:=\bigcup_(C in [set C|F C /\@closure E C 0]) C.
have hUnion:(\bigcup_(C in F) C)=\bigcup_i S i.
  apply/seteqP;split.
  - move=>x [C [i hi [a ha hC]] hxC];exists i;first exact:Logic.I.
    subst C;exact:(@connected_component_sub E (S i) a x hxC).
  - move=>x [i hi hx].
    exists (@connected_component E (S i) x).
    + exists i;first exact:Logic.I;by exists x.
    + exact:connected_component_refl hx.
have hHGerm:germ H=alpha.
  rewrite /H (@finite_family_germ_core E 0 F hFinite) hUnion;exact:hGerm.
have hInside i:S i `<=` U.
  have [d [_ [_ [f [g [_ [_ [hEquation hRest]]]]]]]]:=hFunctional i.
  move=>x hx;exact:(hV i).2 x ((hEquation x).1 hx).1.
exists H;constructor;first exact:hHGerm.
move=>T hT hContain x [C [[i hi [a ha hC]] hClosure] hxC].
subst C.
have hLocal:@set_germ_subset E 0 (germ (\bigcup_i S i)) (germ T).
  by rewrite hGerm.
have [O [hO [hO0 hOT]]]:=(@set_germ_subset_original E 0 (\bigcup_i S i) T).1 hLocal.
have [b [hbC hbO]]:=hClosure O (open_nbhs_nbhs (conj hO hO0)).
have [hU [I [f [hf hEquation]]]]:=hT.
apply/(hEquation x).2;split.
- exact:hInside i x (@connected_component_sub E (S i) a x hxC).
- move=>j.
  have [d hManifold]:=hFunctional i.
  have hHolomorphicManifold:=functional_holomorphic_submanifold_holomorphic hManifold.
  apply:(@holomorphic_component_identity R n d U (S i) O (f j) a b
    hHolomorphicManifold (hInside i) (hf j) hO hbC hbO _ x hxC).
  move=>y hy hyO;have hyB:(\bigcup_i S i) y by exists i.
  exact:((hEquation y).1 (hOT y hyB hyO)).2 j.
Qed.
End MinimalAssembly.
