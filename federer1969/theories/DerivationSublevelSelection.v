(** The disjoint Vitali selection and mass comparison in Federer (1969),
    2.9.3, p. 154. Here the strict threshold is Federer's, and bounded
    auxiliary cells ensure both measures are finite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext CoveringRelationUP CoveringRelationLimits
  CoveringLowerSublevel DerivationSublevelCells MeasureDerivates
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit BorelRegularMeasureUP TopologicalBorel
  AbsoluteContinuousPart AbsoluteContinuousPartBasic
  NonnegativeSum NonnegativeSumScale MeasureCountableAdditivity
  MeasureDisjointSupport CountablyClosedFamilyUP VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_lower_sublevel_open_bound]: the
    chain of inequalities after the Vitali selection in
    Federer 2.9.3, p. 154. It compares alpha_phi(A)
    to c beta(W) for an open almost cover W,
    without requiring A to be measurable or bounded. *)
Theorem derivation_lower_sublevel_open_bound (R : realType) (X : metricType R)
    (phi alpha beta : set X -> \bar R) (V : X -> set X -> Prop)
    (A W : set X) (c : R) :
  is_measure_derivation_context phi V ->
  is_derivation_measure alpha -> is_derivation_measure beta -> (0<c)%R ->
  open W -> phi (A `\` W)=0 ->
  (forall x, A x -> covering_lower_limit V (measure_ratio_function alpha beta) x<c%:E) ->
  measure_continuous_part alpha phi A<=c%:E*beta W.
Proof.
move=> hc ha hb hcpos hW hzW hA.
have hv := derivation_context_vitali hc.
have hmphi := derivation_measure_law (derivation_context_measure hc).
have hma := derivation_measure_law ha.
have hmb := derivation_measure_law hb.
pose C := covering_lower_sublevel V (measure_ratio_function alpha beta) c%:E W 1%R.
have hCV x S : C x S -> V x S by move=> [h _].
have hf x : (A `&` W) x -> covering_relation_fine_at C x.
  move=> [hx hw]; apply: covering_lower_sublevel_fine (vitali_relation_covering hv) hW hw _ (hA x hx).
  exact: ltr01.
have [G [hG [hcount [hdis hzG]]]] := @vitali_relation_selection R X phi V hv C (A `&` W) hCV hf.
pose U := \bigcup_(S in G) S.
have hwithin S : G S -> S `<=` W.
  move=> hS; have [x [_ [_ [hSW _]]]] := hG S hS; exact hSW.
have hB S : G S -> borel_set S.
  move=> hS; have [x [_ hC]] := hG S hS.
  apply: (vitali_relation_borel hv); exists x; split=> //; exact: hCV hC.
have hameas S : G S -> measure_measurable alpha S.
  move=> hS; exact (@borel_regular_borel_measurable R X alpha hma (derivation_measure_borel_regular ha) S (hB S hS)).
have hbmeas S : G S -> measure_measurable beta S.
  move=> hS; exact (@borel_regular_borel_measurable R X beta hmb (derivation_measure_borel_regular hb) S (hB S hS)).
have hcell S : G S -> alpha S<=c%:E*beta S.
  move=> hS; have [x [_ hC]] := hG S hS.
  exact: derivation_sublevel_cell_bound ha hb hC.
have hz : phi (A `\` U)=0.
  apply: (@measure_null_subset R X phi hmphi _ ((A `\` W) `|` ((A `&` W) `\` U))).
  - move=> x [hx hn]; case: (pselect (W x))=> hw.
    + right; by split=> //; split.
    + left; by split.
  - exact (@measure_null_union R X phi hmphi (A `\` W) ((A `&` W) `\` U) hzW hzG).
have hmg := @measure_continuous_part_is_measure R X alpha phi hmphi hma.
have hgz : measure_continuous_part alpha phi (A `\` U)=0 :=
  @continuous_part_null R X phi alpha _ hma (measure_continuous_part_specification alpha phi) _ hz.
have hAU := @null_remainder_measure_cover_bound R X (measure_continuous_part alpha phi) A U hmg hgz.
have hdom := @measure_continuous_part_le R X alpha phi hmphi (derivation_measure_borel_regular ha) U.
have hdis' S T : G S -> G T -> S!=T -> forall x, S x -> T x -> False.
  move=> hS hT /eqP hne x hs ht.
  have hx : (S `&` T) x by split.
  by rewrite (hdis S T hS hT hne) in hx.
have hsum := @measure_countable_disjoint_additivity R X [the choiceType of set X]
  alpha hma G idfun hcount hameas hdis'.
have hmono : nonnegative_sum G alpha<=nonnegative_sum G (fun S => c%:E*beta S).
  exact: nonnegative_sum_mono hcell.
have hscale := @nonnegative_sum_scale R [the choiceType of set X] G beta c (ltW hcpos)
  (fun S _ => measure_nonnegative hmb S).
have htotal := @measure_disjoint_sum_bound R X [the choiceType of set X]
  beta hmb W G idfun hwithin hbmeas hdis.
have hmult : c%:E*nonnegative_sum G beta<=c%:E*beta W.
  apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW hcpos.
  exact htotal.
rewrite hscale in hmono.
have hU : alpha U<=c%:E*beta W by rewrite /U hsum; exact: le_trans hmono hmult.
exact: le_trans hAU (le_trans hdom hU).
Qed.
