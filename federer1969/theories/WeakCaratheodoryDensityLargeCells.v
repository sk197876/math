(** Supporting containing-generator proof for Federer (1969),
    2.10.19(3)–(5), p. 181. This is an additional supporting theorem, not a
    silent change to the numbered 2.10.18 statements. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import MetricDiameterUP MetricDiameter MeasureUP MeasureBasic
  MeasureDerivates ExtendedRealConventions PartialFunctionUP CoveringUpperValues
  CoveringRelationLimits CaratheodoryDensityUpperBound CaratheodoryWeakEnlargementUP
  DiameterEnlargements CoveringFamilyUP.
From Federer Require Import WeakCaratheodoryDensityQuotient.
From Federer Require Import CaratheodoryDensityLargeCells.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weak_caratheodory_large_cells_fine]: supporting weak-cost
    enlargement argument for 2.10.19(3)–(5), p. 181 Zero costs and the
    corrected covering quotient are explicit; the printed strict 2.10.18 is
    unchanged. *)
Theorem weak_caratheodory_large_cells_fine (R : realType) (X : metricType R)
    (F : set (set X)) (c mu : set X -> \bar R) (E : set X -> set X)
    (k : R) (B V : set X) (delta : \bar R) (t : R) :
  is_measure mu -> (0<t)%R -> is_weak_caratheodory_enlargement F c E k -> open V -> B `<=` V -> 0<delta ->
  (forall x, B x -> t%:E<covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_measure_cost_ratio mu c) x) ->
  family_covers_finely (caratheodory_large_cell_family F c mu E V delta t) B.
Proof.
move=> hm ht hE ho hBV hd hlim x hx e he.
have hk := weak_enlargement_constant_positive hE.
have hV : nbhs x V by move: ho; rewrite openE=> ho; exact: ho x (hBV x hx).
have [v hv hball] := proj1 (metricType_numDomainType.nbhs_mdistP x _) hV.
have [d [hd0 hdd]] : exists d : R, (0<d)%R /\ d%:E<delta.
  move: hd; case: delta=> [d| |] hd //.
  - exists (d/2)%R; split; first by move: hd; rewrite lte_fin=> hd; lra.
    rewrite lte_fin; move: hd; rewrite lte_fin=> hd; lra.
  - exists 1%R; split; first exact: ltr01.
    exact: ltry.
pose r := (Num.min e (Num.min (v/k) (d/k)))%R.
have hr : (0<r)%R by rewrite /r !lt_min he !divr_gt0.
have hre : (r<=e)%R by rewrite /r ge_min lexx.
have hrmin : (r<=Num.min (v/k) (d/k))%R by rewrite /r ge_min lexx orbT.
have hrv : (k*r<=v)%R.
  have hminb : (Num.min (v/k) (d/k)<=v/k)%R by rewrite ge_min lexx.
  have h : (k*r<=k*(v/k))%R by rewrite ler_pM2l //; exact: le_trans hrmin hminb.
  by rewrite [(k*(v/k))%R]mulrC divfK ?gt_eqF // in h.
have hrd : (k*r<=d)%R.
  have hminb : (Num.min (v/k) (d/k)<=d/k)%R by rewrite ge_min lexx orbT.
  have h : (k*r<=k*(d/k))%R by rewrite ler_pM2l //; exact: le_trans hrmin hminb.
  by rewrite [(k*(d/k))%R]mulrC divfK ?gt_eqF // in h.
have [S [y [[hF hxS] [hdiam [hgraph hy]]]]] :=
  @covering_upper_limit_large_value R X (caratheodory_family_relation F)
    (caratheodory_measure_cost_ratio mu c) x t%:E r (hlim x hx) hr.
have hdiv := (@caratheodory_measure_cost_ratio_graph R X mu c S y).1 hgraph.
have hmass := caratheodory_density_divide_large (@measure_nonnegative R X mu hm S)
  (@weak_enlargement_cost_nonnegative R X F c E k hE S hF) ht hdiv hy.
have hxE : E S x := @weak_enlargement_contains R X F c E k hE S hF x (@diameter_enlargement_contains R X F S hF x hxS).
have hdiamE := @weak_enlargement_diameter R X F c E k hE S hF.
have hsmall : extended_metric_diameter (E S)<(k*r)%:E.
  apply: le_lt_trans hdiamE _; rewrite EFinM lte_pmul2l ?fin_numE //; by rewrite lte_fin.
exists S; split.
- split=> //; split=> //; split.
  + move=> z hz; apply: hball.
    have hh := le_lt_trans (metric_diameter_upper (extended_metric_diameter_specification (E S)) hxE hz) hsmall.
    rewrite lte_fin in hh; exact: lt_le_trans hh hrv.
  + apply: lt_trans hsmall _; apply: le_lt_trans _ hdd; by rewrite lee_fin.
- split=> // z hz; rewrite /metric_open_ball.
  have hh := le_lt_trans (metric_diameter_upper (extended_metric_diameter_specification S) hxS hz) hdiam.
  rewrite lte_fin in hh; exact: lt_le_trans hh hre.
Qed.
