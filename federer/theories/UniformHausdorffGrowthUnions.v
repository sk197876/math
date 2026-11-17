(** Federer (1969), 3.4.12, p. 339: the real-case
    growth argument extends to a finite family of irreducible
    representatives. Reuse outer-measure subadditivity and bounded unions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP ExtendedSupremumPowers MeasureSplit UniformHausdorffGrowthUP MeasureUP MeasureBasic MeasureAlmostBasic
  HausdorffMeasure HausdorffDimensionDrop MetricDiameter MetricBoundedUnion CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [uniform_hausdorff_growth_higher_degree]: lower-dimensional
    finite-mass representatives are null at a larger degree,
    by 2.10.2, p. 172, and satisfy the required estimate
    with coefficient zero. Boundedness is retained. *)
Lemma uniform_hausdorff_growth_higher_degree (R:realType) (X:metricType R)
    d m (S:set X) c:
  (d<m)%N ->hausdorff_measure d S< +oo ->
  is_uniform_hausdorff_growth d S c ->is_uniform_hausdorff_growth m S 0%R.
Proof.
move=>hDM hFinite hGrowth.
have hNull:=@hausdorff_finite_mass_higher_degree_zero R X d m S hDM hFinite.
constructor.
- exact:uniform_hausdorff_growth_bounded hGrowth.
- exact:lexx.
- move=>A hAS.
  have hA:=measure_null_subset (@hausdorff_measure_is_measure R X m) hAS hNull.
  by rewrite hA mul0e.
Qed.

(** Source for [uniform_hausdorff_growth_union]: finite union
    assembly of the diameter estimate required in 3.4.12,
    p. 339. Intersect every original subset with the two
    representatives; the same subset diameter bounds both pieces. *)
Lemma uniform_hausdorff_growth_union (R:realType) (X:metricType R)
    m (S T:set X) (c d:R):
  is_uniform_hausdorff_growth m S c ->is_uniform_hausdorff_growth m T d ->
  is_uniform_hausdorff_growth m (S `|` T) (c+d)%R.
Proof.
move=>hS hT;constructor.
- exact:metric_bounded_union (uniform_hausdorff_growth_bounded hS) (uniform_hausdorff_growth_bounded hT).
- exact:addr_ge0 (uniform_hausdorff_growth_coefficient hS) (uniform_hausdorff_growth_coefficient hT).
- move=>A hA.
  have hCover:A `<=` (A `&` S) `|` (A `&` T).
    move=>x hx;case:(hA x hx)=>hMember;[left|right];by split.
  apply:le_trans (@measure_binary_cover R X (@hausdorff_measure R X m)
    (@hausdorff_measure_is_measure R X m) A (A `&` S) (A `&` T) hCover) _.
  have hFirst:=@uniform_hausdorff_growth_bound R X m S c hS (A `&` S) (fun x hx=>hx.2).
  have hSecond:=@uniform_hausdorff_growth_bound R X m T d hT (A `&` T) (fun x hx=>hx.2).
  have hDiamS:extended_metric_diameter (A `&` S)<=extended_metric_diameter A.
    exact:(@extended_metric_diameter_mono R X (A `&` S) A (fun x hx=>hx.1)).
  have hDiamT:extended_metric_diameter (A `&` T)<=extended_metric_diameter A.
    exact:(@extended_metric_diameter_mono R X (A `&` T) A (fun x hx=>hx.1)).
  have hPowerS:=nonnegative_extended_power_monotone m (metric_diameter_nonnegative (extended_metric_diameter_specification (A `&` S))) hDiamS.
  have hPowerT:=nonnegative_extended_power_monotone m (metric_diameter_nonnegative (extended_metric_diameter_specification (A `&` T))) hDiamT.
  have hC:(0<=c%:E) by rewrite lee_fin;exact:uniform_hausdorff_growth_coefficient hS.
  have hD:(0<=d%:E) by rewrite lee_fin;exact:uniform_hausdorff_growth_coefficient hT.
  apply:le_trans (leeD hFirst hSecond) _.
  rewrite EFinD (ge0_muleDl _ hC hD).
  apply:leeD.
  + apply:lee_pmul=>//;exact:expe_ge0 (metric_diameter_nonnegative (extended_metric_diameter_specification (A `&` S))).
  + apply:lee_pmul=>//;exact:expe_ge0 (metric_diameter_nonnegative (extended_metric_diameter_specification (A `&` T))).
Qed.

(** Source for [uniform_hausdorff_growth_empty]: the empty
    finite component family in 3.4.12, p. 339, has
    zero mass and diameter in every original degree. *)
Lemma uniform_hausdorff_growth_empty (R:realType) (X:metricType R) m:
  @is_uniform_hausdorff_growth R X m set0 0%R.
Proof.
constructor.
- by rewrite /metric_set_bounded extended_metric_diameter_empty lt0y.
- exact:lexx.
- move=>A hA;have hEmpty:A=set0 by apply/seteqP;split=>x hx;[exact:hA x hx|case:hx].
  by rewrite hEmpty (measure_empty (@hausdorff_measure_is_measure R X m)) mul0e.
Qed.
