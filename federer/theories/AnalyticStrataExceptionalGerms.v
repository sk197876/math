(** Federer (1969), 3.4.10, p. 337:
    the lower-dimensional strata and their corrected
    analytic boundaries have smaller-dimensional analytic
    containing germs. Reuse 3.4.8(16) for each
    functional stratum instead of assuming its hull
    has the same dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP
  SetGermOrder AnalyticVarietyGermUP AnalyticVarietyGermBooleanClosure GermVanishingSealed
  AnalyticDepthSealed AnalyticFiniteStratificationUP FunctionalAnalyticSubmanifoldUP
  FunctionalAnalyticHullDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ExceptionalGerms.
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

(** Source for [analytic_strata_exceptional_germs]: the
    finite lower-dimensional analytic containing germs used
    for both singular-part conclusions of 3.4.10,
    p. 337. Empty germs are explicit.
    Every original lower-dimensional stratum and every
    corrected boundary is retained in the indexed
    family; no dimension conclusion is assumed for
    a functional stratum's analytic hull. *)
Theorem analytic_strata_exceptional_germs (alpha beta:G0) m (U0 S0:set X)
    mu (V S G:'I_mu->set X):
  @is_analytic_finite_stratification R n alpha beta m U0 S0 mu V S G ->
  exists d:'I_mu->nat,
  exists A:('I_mu+'I_mu)%type->set X,
  exists nu:('I_mu+'I_mu)%type->G0,
    (forall i,(d i<=m)%N /\@is_functional_analytic_submanifold R n (d i) (V i) (S i)) /\
    (forall i,A (inl i)=if (d i<m)%N then S i else set0) /\
    (forall i,A (inr i)=G i) /\
    forall j,@is_analytic_variety_germ R X NX hNX 0 (nu j) /\
      set_germ_subset (germ (A j)) (nu j) /\
      (nu j=germ set0 \/(depth (ideal (nu j))<m)%N).
Proof.
move=>hLaws.
have [d hD]:=choice (fun i=>analytic_stratification_functional hLaws i).
pose A:('I_mu+'I_mu)%type->set X:=fun j=>match j with
  | inl i=>if (d i<m)%N then S i else set0
  | inr i=>G i
  end.
have hEach:forall j:('I_mu+'I_mu)%type,exists nu:G0,
    @is_analytic_variety_germ R X NX hNX 0 nu /\
    set_germ_subset (germ (A j)) nu /\
    (nu=germ set0 \/(depth (ideal nu)<m)%N).
  case=>i.
  - rewrite /A /=;case hLow:(d i<m)%N.
    + have [nu [hNu [hContained hDimension]]]:=@functional_analytic_hull_dimension R n (d i)
        (V i) (S i) (analytic_stratification_neighbourhoods hLaws i).2.1 (hD i).2.
      exists nu;split;first exact:hNu.
      split;first exact:hContained.
      case:hDimension=>hDimension;first by left.
      right;exact:leq_ltn_trans hDimension hLow.
    + exists (germ set0);split;first exact:analytic_variety_germ_empty.
      split;first exact:set_germ_subset_reflexive.
      by left.
  - exists (germ (G i));split.
    + exists (V i),(G i);split;first exact:(analytic_stratification_neighbourhoods hLaws i).2.1.
      split;last reflexivity;exact:analytic_stratification_boundary_analytic hLaws i.
    + split;first exact:set_germ_subset_reflexive.
      exact:analytic_stratification_boundary_dimension hLaws i.
have [nu hNu]:=choice hEach.
exists d,A,nu;split;first exact:hD.
split;first by move=>i.
split;first by move=>i.
exact:hNu.
Qed.
End ExceptionalGerms.
