(** Large density cells supporting Federer (1969), 2.10.18(1), p. 180, first
    proof paragraph. Use Federer's original partial quotient: the strict
    growth assumption makes its denominators positive finite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import MetricDiameterUP MetricDiameter MeasureUP MeasureBasic
  MeasureDerivates ExtendedRealConventions PartialFunctionUP CoveringUpperValues
  CoveringRelationLimits CaratheodoryDensityUpperBound CaratheodoryEnlargementUP
  DiameterEnlargements CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_finite_quotient_large]: supporting
    conversion of the strict density threshold into the
    inequality mu(S)>t zeta(S) in 2.10.18(1), p. 180.
    Infinite numerators are allowed; no new quotient convention. *)
Lemma positive_finite_quotient_large (R : realType) (x c y : \bar R) (t : R) :
  0<c -> c < +oo -> extended_divide x c=Some y -> t%:E<y -> t%:E*c<x.
Proof.
move=> hc hcf.
have hcfin : c \is a fin_num by rewrite (ge0_fin_numE (ltW hc)).
rewrite /extended_divide (gt_eqF hc) hcfin orbT=> -[<-] hy.
clear hcfin; move: hc hcf hy; case: c=> [r| |] // hr _ hy.
have hrR : (0<r)%R by move: hr; rewrite lte_fin.
have he : (x/r%:E)*r%:E=x.
  by rewrite inver (gt_eqF hrR) -muleA -EFinM mulVf ?gt_eqF // mule1.
have h : t%:E*r%:E<(x/r%:E)*r%:E.
  by rewrite lte_pmul2r ?fin_numE // lte_fin.
by rewrite he in h.
Qed.

(** Source for [caratheodory_large_cell_family]: the fine family in the
    first paragraph of the proof of 2.10.18(1), p. 180 E contains the
    printed hat S and is a controlled generator. *)
Definition caratheodory_large_cell_family (R : realType) (X : metricType R)
    (F : set (set X)) (c mu : set X -> \bar R) (E : set X -> set X)
    (V : set X) (delta : \bar R) (t : R) : set (set X) :=
  [set S | F S /\ t%:E*c S<mu S /\ E S `<=` V /\ extended_metric_diameter (E S)<delta].

(** Source for [caratheodory_large_cells_fine]: supporting fineness
    assertion in 2.10.18(1), p. 180 *)
Theorem caratheodory_large_cells_fine (R : realType) (X : metricType R)
    (F : set (set X)) (c mu : set X -> \bar R) (E : set X -> set X)
    (k : R) (B V : set X) (delta : \bar R) (t : R) :
  is_caratheodory_enlargement F c E k -> open V -> B `<=` V -> 0<delta ->
  (forall x, B x -> t%:E<covering_upper_limit (caratheodory_family_relation F)
    (measure_ratio_function mu c) x) ->
  family_covers_finely (caratheodory_large_cell_family F c mu E V delta t) B.
Proof.
move=> hE ho hBV hd hlim x hx e he.
have hk := caratheodory_enlargement_constant_positive hE.
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
  have hm : (Num.min (v/k) (d/k)<=v/k)%R by rewrite ge_min lexx.
  have h : (k*r<=k*(v/k))%R by rewrite ler_pM2l //; exact: le_trans hrmin hm.
  by rewrite [(k*(v/k))%R]mulrC divfK ?gt_eqF // in h.
have hrd : (k*r<=d)%R.
  have hm : (Num.min (v/k) (d/k)<=d/k)%R by rewrite ge_min lexx orbT.
  have h : (k*r<=k*(d/k))%R by rewrite ler_pM2l //; exact: le_trans hrmin hm.
  by rewrite [(k*(d/k))%R]mulrC divfK ?gt_eqF // in h.
have [S [y [[hF hxS] [hdiam [hgraph hy]]]]] :=
  @covering_upper_limit_large_value R X (caratheodory_family_relation F)
    (measure_ratio_function mu c) x t%:E r (hlim x hx) hr.
have hmass := positive_finite_quotient_large (@caratheodory_enlargement_cost_positive R X F c E k hE S hF)
  (@caratheodory_enlargement_cost_finite R X F c E k hE S hF) hgraph hy.
have hxE : E S x := @caratheodory_enlargement_contains R X F c E k hE S hF x (@diameter_enlargement_contains R X F S hF x hxS).
have hdiamE := @caratheodory_enlargement_diameter R X F c E k hE S hF.
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
