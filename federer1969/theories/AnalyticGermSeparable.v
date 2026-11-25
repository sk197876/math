(** Federer (1969), 3.4.5, p. 319: the
    analytic germ ring is separable when the source has
    finite dimension. The actual factorial-growth classes supply
    the compact cover; finite nets supply the dense set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP LinearBasis AnalyticGermUP AnalyticGermMetric
  AnalyticGermGrowthSealed AnalyticGermGrowthCover AnalyticGermGrowthCompact CompactCoverSeparability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_dimensional_analytic_germs_separable]:
    the separability conclusion of 3.4.5, p. 319,
    for the exact original derivative metric. An actual
    finite basis discharges finite dimensionality. *)
Theorem finite_dimensional_analytic_germs_separable (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) n (b:'I_n->X):
  is_basis b ->exists D:set (@analytic_germ_metric R X NX hNX a),countable D /\dense D.
Proof.
move=>hb.
pose M:=@analytic_germ_metric R X NX hNX a.
pose K (i:nat*nat):set M:=@AnalyticGermGrowth.value R X NX hNX a i.1 i.2.
refine (@countable_compact_cover_separable R [the metricType R of M] (@analytic_germ_zero R X NX hNX a)
  [the countType of ((nat*nat)%type:Type)] K _ _).
- move=>[s t];exact:(@analytic_germ_growth_class_compact R X NX hNX a n b hb s t).
- move=>alpha;have [s [t [_ [_ hAlpha]]]]:=@analytic_germ_positive_growth_cover R X NX hNX a alpha.
  by exists (s,t).
Qed.
