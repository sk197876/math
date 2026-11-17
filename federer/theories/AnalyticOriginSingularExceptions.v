(** Federer (1969), 3.4.10, p. 337:
    near the original centre, the nonregular part
    lies in finitely many sets with smaller-dimensional
    analytic containing germs. Use the complete corrected
    stratification and its already proved regular core. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP
  SetGermSealed SetGermLaws SetGermExistence SetGermLocality SetGermOrder
  AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  FiniteAnalyticVarietyUP FiniteAnalyticVarietyBoundary AnalyticGermLocalRepresentative
  AnalyticFiniteStratificationUP AnalyticFiniteStratificationExistence
  FunctionalAnalyticManifold AnalyticSubmanifoldUP AnalyticRegularLocusUP FiniteAnalyticStrataRegularCore
  AnalyticStrataExceptionalGerms OrderedStrataDisjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginExceptions.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G0:=(@set_germ_space T 0).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  hB n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [analytic_origin_singular_exceptions]: the
    local finite analytic exceptional family behind both
    singular-part assertions of 3.4.10, p. 337.
    All strata and their boundary germs are
    constructed from the original analytic germ. The
    only regular-locus premise is its independent defining
    neighbourhood law, not a regularity conclusion. *)
Theorem analytic_origin_singular_exceptions (U S L:set X) m:
  @open T U ->U 0 ->
  @is_analytic_variety_germ R X NX hNX 0 (germ S) ->
  (depth (ideal (germ S))<=m)%N ->
  @is_analytic_regular_locus R n m U S L ->
  exists J:finType,exists W:set X,exists A:J->set X,exists nu:J->G0,
    @open T W /\W 0 /\W `<=` U /\
    (S `\` L) `&` W `<=` \bigcup_j A j /\
    forall j,@is_analytic_variety_germ R X NX hNX 0 (nu j) /\
      set_germ_subset (germ (A j)) (nu j) /\
      (nu j=germ set0 \/(depth (ideal (nu j))<m)%N).
Proof.
move=>hU hU0 hS hDepth hL.
have [V0 [hV00 [hV0U hVS]]]:=@analytic_germ_local_representative R X NX hNX U S hU0 hU hS.
have hGermVS:germ (V0 `&` S)=germ S:=@set_germ_neighbourhood_intersection T 0 V0 S hVS.1 hV00.
have hBound:(depth (ideal (germ (V0 `&` S)))<=m)%N by rewrite hGermVS.
have hEmpty:=@finite_analytic_variety_domain_empty R X NX hNX V0 hVS.1.
have [mu [V [F [G [hLaws hInside]]]]]:=@analytic_finite_stratification_exists_at_bound R m n
  V0 (V0 `&` S) V0 set0 hV00 hVS hV00 hEmpty hBound.
have [d [A [nu [hFunctional [hLow [hBoundary hNu]]]]]]:=
  @analytic_strata_exceptional_germs R n _ _ m V0 set0 mu V F G hLaws.
have hGerm:=analytic_stratification_germ hLaws.
rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)) setC0
  (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) setIT hGermVS in hGerm.
have [N [hN [hN0 hNEquation]]]:=(@set_germ_equality_original T 0 S (\bigcup_i F i)).1 hGerm.
pose C:set X:=\bigcup_i (~` V i).
have hC:@closed T C.
  apply:(closed_bigcup (@finite_finset 'I_mu setT))=>i _.
  exact:open_closedC (analytic_stratification_neighbourhoods hLaws i).1.
pose W:set X:=N `&` (U `&` ~` C).
have hW:@open T W:=openI hN (openI hU (closed_openC hC)).
have hW0:W 0.
  split;first exact:hN0.
  split;first exact:hU0.
  move=>[i _ hNot];exact:hNot (analytic_stratification_neighbourhoods hLaws i).2.1.
have hWU:W `<=` U by move=>x hx;exact:hx.2.1.
have hWV i:W `<=` V i.
  move=>x hx;apply:contrapT=>hNot;apply:hx.2.2;by exists i.
have hEquation:S `&` W=(\bigcup_i F i) `&` W.
  apply/seteqP;split.
  - move=>x [hxS hxW];split;last exact:hxW.
    have h:((\bigcup_i F i) `&` N) x by rewrite -hNEquation;split;[exact:hxS|exact:hxW.1].
    exact:h.1.
  - move=>x [hxF hxW];split;last exact:hxW.
    have h:(S `&` N) x by rewrite hNEquation;split;[exact:hxF|exact:hxW.1].
    exact:h.1.
have hManifold i:(d i<=m)%N /\@is_euclidean_analytic_submanifold R n (d i) (F i).
  split;first exact:(hFunctional i).1.
  exact:functional_analytic_submanifold_analytic (hFunctional i).2.
have hPairwise:=@ordered_strata_pairwise_disjoint X mu set0 F
  (@analytic_stratification_disjoint R n (germ (V0 `&` S)) (germ set0) m V0 set0 mu V F G hLaws).
have hRegular:=@finite_analytic_strata_regular_core R n m (Finite.clone 'I_mu _)
  U S L W V F G d hL hW hWU hEquation hWV hManifold hPairwise
  (@analytic_stratification_boundary R n (germ (V0 `&` S)) (germ set0) m V0 set0 mu V F G hLaws).
exists (Finite.clone ('I_mu+'I_mu)%type _),W,A,nu.
split;first exact:hW.
split;first exact:hW0.
split;first exact:hWU.
split;last exact:hNu.
move=>x [[hxS hxNot] hxW];apply:contrapT=>hNoA.
apply:hxNot;apply:(hRegular x hxS hxW).
- move=>i hxG;apply:hNoA;exists (inr i);first exact:Logic.I.
  by rewrite hBoundary.
- move=>i hSmall hxF;apply:hNoA;exists (inl i);first exact:Logic.I.
  by rewrite hLow hSmall.
Qed.
End OriginExceptions.
