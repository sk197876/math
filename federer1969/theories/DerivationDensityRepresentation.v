(** The geometric summation proof of Federer (1969), 2.9.7, pp. 155–156.
    Compare psi_phi with the existing sealed integral-density measure of the
    derivate. On each geometric band both masses lie between t^j phi and
    t^(j+1) phi. Countable disjoint summation gives comparisons with factor
    t in both directions; let t decrease to one. This is the printed proof,
    with the integral sum expressed using the density-measure laws of
    2.4.10, p. 85. The non-real exceptional set follows Federer's erratum p.
    3, book p. 155 line 26. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  PartialFunctionUP PartialExtendedOrderLoci ExtendedRealOrderTopology
  MeasureDerivationContext MeasureDerivates DerivationMeasurable DerivationLevelSeparation
  AbsoluteContinuousPart ContinuousPartDecomposition ContinuousPartDecompositionUP
  ContinuousPartMeasurableSets DerivateClosedLevelBounds DerivationZeroAndNonreal
  DerivationGeometricCells DisjointAlmostCoverComparison DensityCellBounds
  MeasureDensityUP MeasureDensity MeasureDensityNullSets ExtendedGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_continuous_part_density]: the
    two displayed sum estimates in Federer 2.9.7,
    p. 156, identifying psi_phi(A) with
    the upper integral of D over A. The
    supporting theorem uses the sealed density measure
    to express countable additivity of the nonnegative
    integrals. Measurable A may have infinite measure. *)
Theorem derivation_continuous_part_density (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) A :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> measure_measurable phi A ->
  measure_continuous_part psi phi A=measure_with_density phi (measure_derivate psi phi V) A.
Proof.
move=> hc hp hA.
have hf := derivation_context_measure hc.
have hm := derivation_measure_law hf.
have hmp := derivation_measure_law hp.
pose f := measure_derivate psi phi V.
pose gamma := measure_continuous_part psi phi.
pose nu := @measure_with_density R X phi f.
have hnu := @measure_with_density_laws R X phi f.
have hpos : measure_almost_everywhere phi (partial_extended_nonnegative_locus f).
  apply: (@measure_almost_everywhere_mono R X phi hm (partial_function_domain f) _ _
    (@measure_derivate_domain_conull R X phi psi V hc hp))=> x [y hy].
  exists y; split=> //; exact (@measure_derivate_value_nonnegative R X phi psi V x y hm hmp hy).
have hn := @measure_with_density_is_measure R X phi hm f hpos.
have [E [hdecomp _]] := @measure_continuous_part_decomposition R X phi psi hf hp.
have hg := continuous_decomposition_class hdecomp.
have hmg := derivation_measure_law hg.
have hZg := @continuous_part_zero_points_null R X phi psi V hc hp.
have hWg := @continuous_part_nonreal_points_null R X phi psi V hc hp.
have hZn := @derivation_density_zero_points_null R X phi psi nu V hc hp hnu.
have hWn := @measure_density_null_set R X phi nu hm f (derivation_nonreal_points psi phi V) hnu
  (@derivation_nonreal_points_null R X phi psi V hc hp).
have hboth t : (1<t)%R -> gamma A<=t%:E*nu A /\ nu A<=t%:E*gamma A.
  move=> ht; have ht0 : (0<t)%R := lt_trans (@ltr01 R) ht.
  have htN : t!=0%R by rewrite gt_eqF.
  have htE : 0<=t%:E by rewrite lee_fin; exact: ltW ht0.
  pose F j := derivation_geometric_cell psi phi V A t j.
  have hFm j : measure_measurable phi (F j) := @derivation_geometric_cell_measurable R X phi psi V A t j hc hp hA.
  have hFgm j : measure_measurable gamma (F j) :=
    @continuous_part_preserves_measurable_sets R X phi psi hf hp (F j) (hFm j).
  have hFnm j : measure_measurable nu (F j) := @measure_with_density_measurable R X phi hm f (F j) hpos (hFm j).
  have hFsub j : F j `<=` A by move=> x [hx _].
  have hFdis i j : i<>j -> F i `&` F j=set0 :=
    @derivation_geometric_cells_disjoint R X psi phi V A t ht i j.
  have hFgzero : gamma (A `\` \bigcup_j F j)=0 :=
    @derivation_geometric_remainder_null R X phi psi gamma V A t hm hmp hmg ht hZg hWg.
  have hFnzero : nu (A `\` \bigcup_j F j)=0 :=
    @derivation_geometric_remainder_null R X phi psi nu V A t hm hmp hn ht hZn hWn.
  have hgbounds j : (t^j)%:E*phi (F j)<=gamma (F j) /\ gamma (F j)<=(t^(j+1))%:E*phi (F j).
    have hlowp : (0<t^j)%R by rewrite exprz_gt0.
    have hupp : (0<t^(j+1))%R by rewrite exprz_gt0.
    split.
    - apply: (@derivate_closed_upper_level_bound R X phi psi V (F j) (t^j)%R hc hp hlowp)=> x [_ [y [hy [hlo hhi]]]].
      by exists y.
    - apply: (@derivate_closed_lower_level_bound R X phi psi V (F j) (t^(j+1))%R hc hp hupp)=> x [_ [y [hy [hlo hhi]]]].
      exists y; split=> //; exact: ltW hhi.
  have hnbounds j : (t^j)%:E*phi (F j)<=nu (F j) /\ nu (F j)<=(t^(j+1))%:E*phi (F j).
    have hlowp : (0<=t^j)%R by apply: ltW; rewrite exprz_gt0.
    have hupp : (0<=t^(j+1))%R by apply: ltW; rewrite exprz_gt0.
    apply: (@density_measurable_cell_bounds R X phi nu f (F j) (t^j)%R (t^(j+1))%R hm hnu (hFm j) hlowp hupp)=> x [_ [y [hy [hlo hhi]]]].
    exists y; split=> //; split=> //; exact: ltW hhi.
  have hpower j : (t*t^j=t^(j+1))%R by rewrite expfzDr // expr1z mulrC.
  have hgn j : gamma (F j)<=t%:E*nu (F j).
    have h := @lee_wpmul2l R t%:E htE _ _ (hnbounds j).1.
    rewrite muleA -EFinM (hpower j) in h.
    exact: le_trans (hgbounds j).2 h.
  have hng j : nu (F j)<=t%:E*gamma (F j).
    have h := @lee_wpmul2l R t%:E htE _ _ (hgbounds j).1.
    rewrite muleA -EFinM (hpower j) in h.
    exact: le_trans (hnbounds j).2 h.
  split.
  - exact (@measure_disjoint_almost_cover_comparison R X _ gamma nu A setT F t hmg hn
      (ltW ht0) (countableP _) (fun j _ => hFsub j) (fun j _ => hFgm j) (fun j _ => hFnm j)
      (fun i j _ _ => hFdis i j) hFgzero (fun j _ => hgn j)).
  - exact (@measure_disjoint_almost_cover_comparison R X _ nu gamma A setT F t hn hmg
      (ltW ht0) (countableP _) (fun j _ => hFsub j) (fun j _ => hFnm j) (fun j _ => hFgm j)
      (fun i j _ _ => hFdis i j) hFnzero (fun j _ => hng j)).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@extended_geometric_squeeze R (nu A) (gamma A) (measure_nonnegative hn A))=> t ht.
  exact: (hboth t ht).1.
- apply: (@extended_geometric_squeeze R (gamma A) (nu A) (measure_nonnegative hmg A))=> t ht.
  exact: (hboth t ht).2.
Qed.
