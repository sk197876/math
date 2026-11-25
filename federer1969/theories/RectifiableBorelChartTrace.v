(** Federer (1969), 3.2.23, p. 260: intersect an injective
    chart image with a Borel test set before applying the area formula.
    Compact charts of 3.2.18 refine the printed 3.2.4 decomposition;
    their inverse images need only be Borel, not compact. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableCompactChartsUP RectifiableCompactChartLaws LipschitzUP LipschitzBasic NormMetricScaleContinuity
  TopologicalBorel BorelFamilyBasic ContinuousBorelPreimages CompactLipschitzImageMass
  HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [uniform_compact_chart_borel_trace]: supporting
    Borel parameter sets A,B in the last displayed calculation
    of Federer 3.2.23, p. 260. Pull back a Borel test set
    through the global chart and intersect with its compact parameter
    set. Its image is the exact Borel trace of the chart image;
    injectivity and finite Hausdorff mass are proved. *)
Theorem uniform_compact_chart_borel_trace (R:realType) m n (lambda:R)
    (K:set (R_n R m)) (psi:R_n R m->R_n R n) (E:set (R_n R n)):
  is_uniform_compact_rectifiable_chart lambda K psi ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) E ->
  exists A:set (R_n R m),
    @borel_set (inner_metric_space (@euclidean_inner_productP R m)) A /\
    A `<=` K /\psi @` A=(psi @` K) `&` E /\
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (psi @` A)< +oo) /\
    (forall x y,A x ->A y ->psi x=psi y ->x=y).
Proof.
move=>hChart hE.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose A:=K `&` (psi @^-1` E).
have hBound:=rectifiable_chart_global_bound hChart.
have hCont:continuous (fun x:X=>(psi x:Y)).
  apply:(@metric_fixed_lipschitz_continuous R X Y psi lambda hBound.1)=>x y.
  exact:(hBound.2 x y Logic.I Logic.I).
have hK:@borel_set (inner_metric_space (@euclidean_inner_productP R m)) K:=closed_borel_set (compact_closed (@metric_hausdorff R X)
  (rectifiable_chart_compact hChart)).
have hPre:@borel_set (inner_metric_space (@euclidean_inner_productP R m)) (psi @^-1` E):=
  @continuous_borel_preimage (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) psi hCont E hE.
have hA:@borel_set (inner_metric_space (@euclidean_inner_productP R m)) A:=
  @borel_family_binary_intersection [the choiceType of X] setT _
    (borel_sets_family (inner_metric_space (@euclidean_inner_productP R m)))
  K (psi @^-1` E) hK hPre.
have hSub:A `<=` K by move=>x hx; exact hx.1.
exists A; split; first exact hA.
split; first exact hSub.
split.
- apply/seteqP; split.
  + by move=>y [x [hx hEx] <-]; split; first by exists x.
  + move=>y [[x hx hxy] hy]; exists x; last exact hxy.
    split; first exact hx; change (E (psi x)); by rewrite hxy.
- split.
  + have hFinite:=compact_lipschitz_image_finite_hausdorff_mass
      (metric_lipschitz_of_bound hBound) (rectifiable_chart_compact hChart).
    apply:(le_lt_trans _ hFinite).
    apply:(measure_mono (@hausdorff_measure_is_measure R Y m))=>y [x hx hxy].
    exists x; last exact hxy; exact:hSub x hx.
  + move=>x y hx hy; exact:(uniform_compact_chart_injective hChart (hSub x hx) (hSub y hy)).
Qed.
