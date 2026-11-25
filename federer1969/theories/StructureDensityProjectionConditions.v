(** Federer (1969), 3.3.15, p. 299: every original density
    stratum satisfies BOTH original projection conditions of 3.3.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions StructureDensityStrata StructureProjectionConditions
  StructureHausdorffNullProjection StructureHausdorffFiniteFibres HausdorffMeasure
  MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_density_stratum_hausdorff_finite]: supporting
    finite original H^m(E_i) in Federer 3.3.15, p. 299. The proved
    upper-density comparison and actual finite whole regularized mass
    discharge the finiteness needed by original counting integrals. *)
Lemma structure_density_stratum_hausdorff_finite (R:realType) (X:metricType R) m
    (psi:set X->\bar R) i:
  is_measure psi ->is_borel_regular_measure psi ->psi setT< +oo ->
  @hausdorff_measure R X m (structure_upper_density_stratum m psi i)< +oo.
Proof.
move=>hPsi hRegular hFinite.
pose E:=structure_upper_density_stratum m psi i.
pose c:=(structure_density_threshold R i)^-1%R.
have hBound:=@structure_density_stratum_hausdorff_bound R X m psi i E
  hPsi hRegular hFinite (fun x hx=>hx).
have hC0:(0<=c%:E)%E.
  rewrite lee_fin /c invr_ge0; exact:ltW (@structure_density_threshold_positive R i).
have hTotal:=@measure_mono R X psi hPsi E setT (subsetT E).
have hGlobal:=le_trans hBound (lee_wpmul2l hC0 hTotal).
have hWholeNum:psi setT \is a fin_num.
  by rewrite (ge0_fin_numE (@measure_nonnegative R X psi hPsi setT)).
have hValue:psi setT=(fine (psi setT))%:E by rewrite fineK.
apply:le_lt_trans hGlobal _.
rewrite hValue -EFinM; exact:ltry.
Qed.

(** Source for [structure_density_stratum_projection_conditions]: the
    all-projection conclusion before applying 3.3.12 in Federer
    3.3.15, p. 299. Actual density comparison makes every original
    psi-null subset Hausdorff-null; actual 2.10.11 gives original
    almost-finite fibres from the derived finite Hausdorff mass.
    Every original subset and fibre is retained. *)
Theorem structure_density_stratum_projection_conditions (R:realType) n m
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R) i:
  is_measure psi ->is_borel_regular_measure psi ->psi setT< +oo ->
  forall p:euclidean_projection_space R n m,
    structure_projection_preserves_null_subsets psi (structure_upper_density_stratum m psi i) p /\
    structure_projection_almost_finite_fibres (structure_upper_density_stratum m psi i) p.
Proof.
move=>hPsi hRegular hFinite p.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose E:=structure_upper_density_stratum m psi i.
have hE:borel_set E:=@structure_density_stratum_borel R [the metricType R of X] m psi i hPsi.
have hHFinite:=@structure_density_stratum_hausdorff_finite R [the metricType R of X] m psi i
  hPsi hRegular hFinite.
split.
- move=>B hBE hNull.
  have hBound:=@structure_density_stratum_hausdorff_bound R [the metricType R of X] m psi i B
    hPsi hRegular hFinite hBE.
  rewrite hNull mule0 in hBound.
  have hHNull:@hausdorff_measure R [the metricType R of X] m B=0.
    apply/eqP; rewrite eq_le (measure_nonnegative (@hausdorff_measure_is_measure R [the metricType R of X] m)) andbT.
    exact:hBound.
  exact:(@structure_hausdorff_null_projection R n m E p B hBE hHNull).
- exact:(@structure_hausdorff_almost_finite_fibres R n m E p hE hHFinite).
Qed.
