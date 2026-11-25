(** Federer (1969), 3.4.8(11), p. 327:
    independent laws for the finite decomposition
    of alpha minus beta. Apply the published
    correction at book p. 327 line 24:
    each boundary lies in its own stratum
    and an earlier, smaller-dimensional analytic variety.
    The empty boundary germ is stated separately
    because the book defines dimension only for
    nonempty variety germs, 3.4.8(3), p. 326. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct FiniteDualDimension InnerNorm HilbertFormCompactness SetGermUP SetGermSealed
  FiniteAnalyticVarietyUP FunctionalAnalyticSubmanifoldUP GermVanishingSealed AnalyticDepthSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Stratification.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [is_analytic_finite_stratification]:
    all conclusions of corrected 3.4.8(11),
    p. 327, specified before existence.
    The finite index starts at the first
    new stratum; the original S0 is
    included explicitly among the earlier sets. *)
Record is_analytic_finite_stratification
    (alpha beta:@set_germ_space T 0) m (U0 S0:set X) mu
    (V S G:'I_mu->set X):Prop:={
  (** Source for [analytic_stratification_neighbourhoods]:
      each Vi is a neighbourhood of zero
      in V0, 3.4.8(11), p. 327. *)
  analytic_stratification_neighbourhoods:forall i,
    @open T (V i) /\ V i 0 /\ V i `<=` U0;
  (** Source for [analytic_stratification_germ]:
      the union represents alpha minus beta,
      3.4.8(11), p. 327. *)
  analytic_stratification_germ:
    @SetGerms.meet T 0 alpha (@SetGerms.neg T 0 beta) = germ (\bigcup_i S i);
  (** Source for [analytic_stratification_functional]:
      every Si is a functional analytic
      submanifold of dimension at most m,
      3.4.8(11), p. 327. *)
  analytic_stratification_functional:forall i,exists d,
    (d<=m)%N /\ @is_functional_analytic_submanifold R n d (V i) (S i);
  (** Source for [analytic_stratification_components]:
      every Si has finitely many actual
      connected components, 3.4.8(11), p. 327. *)
  analytic_stratification_components:forall i,
    finite_set (@connected_component T (S i) @` S i);
  (** Source for [analytic_stratification_disjoint]:
      Si avoids S0 and every earlier
      stratum, published correction at book
      p. 327 line 24. *)
  analytic_stratification_disjoint:forall i x,S i x ->
    ~ (S0 `|` \bigcup_(j in [set j:'I_mu|(j<i)%N]) S j) x;
  (** Source for [analytic_stratification_boundary]:
      Vi intersect closure Si lies in
      Si union Gi, published correction
      at book p. 327 line 24. *)
  analytic_stratification_boundary:forall i,
    V i `&` @closure T (S i) `<=` S i `|` G i;
  (** Source for [analytic_stratification_boundary_analytic]:
      Gi is an analytic subvariety of
      Vi, published correction at book
      p. 327 line 24. *)
  analytic_stratification_boundary_analytic:forall i,
    @is_finite_analytic_variety R X NX hNX (V i) (G i);
  (** Source for [analytic_stratification_boundary_dimension]:
      every nonempty Gi germ has dimension
      less than m, published correction
      at book p. 327 line 24.
      The empty germ has no dimension
      in the original definition. *)
  analytic_stratification_boundary_dimension:forall i,
    germ (G i) = germ set0 \/
    (depth (@AnalyticSetIdeal.value R X NX hNX 0 (germ (G i)))<m)%N;
  (** Source for [analytic_stratification_boundary_earlier]:
      Gi is contained in S0 and
      the earlier strata, published correction
      at book p. 327 line 24. *)
  analytic_stratification_boundary_earlier:forall i,
    G i `<=` S0 `|` \bigcup_(j in [set j:'I_mu|(j<i)%N]) S j
}.
End Stratification.
