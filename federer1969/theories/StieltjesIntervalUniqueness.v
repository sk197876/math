(** Supporting uniqueness for Federer (1969), 2.10.7, p. 174, the
    implication from continuity-endpoint interval increments to equality of
    the two Borel regular measures. Use the already proved half-open
    interval agreement theorem of 2.5.18(3), p. 112, outside the actual
    countable discontinuity set of the nondecreasing integrator. Borel hulls
    then give equality on all sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground RealMetricCompleteness StieltjesMonotone
  CurveDiscontinuities StieltjesInducedOpenIntervals HalfOpenIntervalAgreement
  MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [stieltjes_continuity_interval_measure_unique]:
    supporting actual uniqueness step in Federer
    2.10.7, p. 174. Local finiteness is
    derived from finite interval costs. Null
    continuity-point atoms pass to half-open
    intervals, and Borel regularity extends
    Borel agreement to arbitrary target sets. *)
Theorem stieltjes_continuity_interval_measure_unique (R : realType) (g : R -> R)
    (mu nu : set R -> \bar R) (hm : is_measure mu) (hn : is_measure nu) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) ->
  is_borel_regular_measure mu -> is_borel_regular_measure nu ->
  (forall a b, (a<b)%R -> mu `]a,b[<=(g b-g a)%:E) ->
  (forall a b, (a<b)%R -> nu `]a,b[<=(g b-g a)%:E) ->
  (forall x, g @ x --> g x -> mu [set x]=0) ->
  (forall x, g @ x --> g x -> nu [set x]=0) ->
  (forall a b, (a<b)%R -> g @ a --> g a -> g @ b --> g b -> mu `]a,b[=nu `]a,b[) ->
  forall A, mu A=nu A.
Proof.
move=> hg hrmu hrnu hcostmu hcostnu hpointmu hpointnu hinc A.
have hfin := @monotone_locally_finite_variation R g hg.
pose Y := [the metricType R of real_line_metric R].
pose C := @curve_jump_points R Y g.
have hC : countable C := @curve_jump_points_countable R Y g hfin.
have hcont x : ~ C x -> g @ x --> g x.
  move=> hx; apply: contrapT=> hnot; apply: hx.
  exact ((@curve_jump_points_iff R Y g hfin (@real_line_metric_complete R) x).2 hnot).
have hhalf l r : (l<r)%R -> ~ C l -> ~ C r -> mu `[l,r[=nu `[l,r[.
  move=> hlr hl hr; have hcl := hcont l hl; have hcr := hcont r hr.
  rewrite (@null_endpoint_half_open_interval R mu hm l r (hpointmu l hcl) (hpointmu r hcr))
    (@null_endpoint_half_open_interval R nu hn l r (hpointnu l hcl) (hpointnu r hcr)).
  exact: hinc l r hlr hcl hcr.
have hBorel : forall B, borel_set B -> mu B=nu B.
  apply: (@half_open_agreement_borel R mu nu C hm hn).
  - move=> B hB; exact: (@borel_regular_borel_measurable R [the topologicalType of (R : Type)] mu hm hrmu B hB).
  - move=> B hB; exact: (@borel_regular_borel_measurable R [the topologicalType of (R : Type)] nu hn hrnu B hB).
  - exact: interval_increment_bound_local_finiteness hm hcostmu.
  - exact: interval_increment_bound_local_finiteness hn hcostnu.
  - exact hC.
  - exact hhalf.
apply/eqP; rewrite eq_le; apply/andP; split.
- have [B [hAB [hB he]]] := borel_regular_cover hrnu A.
  have hle := measure_mono hm hAB; by rewrite (hBorel B hB) -he in hle.
- have [B [hAB [hB he]]] := borel_regular_cover hrmu A.
  have hle := measure_mono hn hAB; by rewrite -(hBorel B hB) -he in hle.
Qed.
