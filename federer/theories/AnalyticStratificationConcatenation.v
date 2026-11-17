(** Federer (1969), corrected 3.4.8(11), pp. 327, 333:
    concatenate the strata of successive irreducible
    differences. The second family avoids S0 and
    all first-family strata on its actual defining
    neighbourhood. No first-family neighbourhood or component
    family is restricted during this assembly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermOrderedDifferences
  AnalyticFiniteStratificationUP FunctionalAnalyticContainment OrdinalFamilyConcatenation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Concatenation.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation T:=(Topological.clone (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n))) _).

(** Source for [analytic_stratification_concatenation]:
    all corrected laws for the original successive
    irreducible differences in 3.4.8(11), p. 333.
    The second starting set is the exact actual
    union of S0 and earlier strata within its
    chosen neighbourhood. The finite indexing preserves
    every published earlier-boundary requirement. *)
Theorem analytic_stratification_concatenation (alpha gamma beta:@set_germ_space T 0) m
    (U0 S0 W:set X) mu nu (V1 S1 G1:'I_mu->set X) (V2 S2 G2:'I_nu->set X):
  @is_analytic_finite_stratification R n alpha beta m U0 S0 mu V1 S1 G1 ->
  W `<=` U0 ->
  @is_analytic_finite_stratification R n gamma (@SetGerms.join T 0 beta alpha)
    m W (W `&` (S0 `|` \bigcup_i S1 i)) nu V2 S2 G2 ->
  @is_analytic_finite_stratification R n (@SetGerms.join T 0 alpha gamma) beta
    m U0 S0 (mu+nu) (ordinal_family_cat V1 V2) (ordinal_family_cat S1 S2) (ordinal_family_cat G1 G2).
Proof.
move=>hFirst hWU0 hSecond.
have hSecondInside i:S2 i `<=` W.
  have [d [_ hFunctional]]:=analytic_stratification_functional hSecond i.
  have hSiVi:=functional_analytic_domain_containment hFunctional.
  have hViW:=(analytic_stratification_neighbourhoods hSecond i).2.2.
  move=>x hx;exact:hViW x (hSiVi x hx).
constructor.
- move=>i;case:(split_ordP i)=>[j ->|j ->];rewrite ?ordinal_family_cat_left ?ordinal_family_cat_right.
  + exact:analytic_stratification_neighbourhoods hFirst j.
  + have [hV [hV0 hVW]]:=analytic_stratification_neighbourhoods hSecond j.
    split;first exact:hV.
    split;first exact:hV0.
    move=>x hx;exact:hWU0 x (hVW x hx).
- rewrite ordinal_set_family_cat_union set_germ_union_ordered_difference
    (analytic_stratification_germ hFirst) (analytic_stratification_germ hSecond).
  exact:(@set_germ_union_equation T 0 _ _ _ (@SetGerms.laws T 0)).
- move=>i;case:(split_ordP i)=>[j ->|j ->];rewrite ?ordinal_family_cat_left ?ordinal_family_cat_right.
  + exact:analytic_stratification_functional hFirst j.
  + exact:analytic_stratification_functional hSecond j.
- move=>i;case:(split_ordP i)=>[j ->|j ->];rewrite ?ordinal_family_cat_left ?ordinal_family_cat_right.
  + exact:analytic_stratification_components hFirst j.
  + exact:analytic_stratification_components hSecond j.
- move=>i;case:(split_ordP i)=>[j ->|j ->].
  + rewrite ordinal_family_cat_left ordinal_set_family_cat_earlier_left.
    exact:analytic_stratification_disjoint hFirst j.
  + rewrite ordinal_family_cat_right ordinal_set_family_cat_earlier_right.
    move=>x hx hPast.
    have hDisjoint:=@analytic_stratification_disjoint R n gamma (@SetGerms.join T 0 beta alpha)
      m W (W `&` (S0 `|` \bigcup_i S1 i)) nu V2 S2 G2 hSecond j x hx.
    apply:hDisjoint.
    case:hPast=>[hS0x|[hOld|hNew]].
    * left;split;[exact:hSecondInside j x hx|by left].
    * left;split;[exact:hSecondInside j x hx|by right].
    * by right.
- move=>i;case:(split_ordP i)=>[j ->|j ->];rewrite ?ordinal_family_cat_left ?ordinal_family_cat_right.
  + exact:analytic_stratification_boundary hFirst j.
  + exact:analytic_stratification_boundary hSecond j.
- move=>i;case:(split_ordP i)=>[j ->|j ->];rewrite ?ordinal_family_cat_left ?ordinal_family_cat_right.
  + exact:analytic_stratification_boundary_analytic hFirst j.
  + exact:analytic_stratification_boundary_analytic hSecond j.
- move=>i;case:(split_ordP i)=>[j ->|j ->];rewrite ?ordinal_family_cat_left ?ordinal_family_cat_right.
  + exact:analytic_stratification_boundary_dimension hFirst j.
  + exact:analytic_stratification_boundary_dimension hSecond j.
- move=>i;case:(split_ordP i)=>[j ->|j ->].
  + rewrite ordinal_family_cat_left ordinal_set_family_cat_earlier_left.
    exact:analytic_stratification_boundary_earlier hFirst j.
  + rewrite ordinal_family_cat_right ordinal_set_family_cat_earlier_right.
    move=>x hx.
    have hEarlier:=@analytic_stratification_boundary_earlier R n gamma (@SetGerms.join T 0 beta alpha)
      m W (W `&` (S0 `|` \bigcup_i S1 i)) nu V2 S2 G2 hSecond j.
    have [[_ [hS0x|hOld]]|hNew]:=@hEarlier x hx.
    * by left.
    * right;by left.
    * right;by right.
Qed.
End Concatenation.
