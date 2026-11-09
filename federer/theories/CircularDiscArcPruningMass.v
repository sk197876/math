(** Federer (1969), 3.3.19, p. 305: the original
    exceptional-stage masses satisfy the printed complementary
    arc fraction plus 2/n recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularTrigonometrySealed
  CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP CircularDiscRadialMapUP CircularDiscBadChildCount
  CircularDiscArcPruningUP CircularDiscArcPruningContainment FiniteRefinementFractionBudget
  CircularDiscSubfamilyMass HausdorffMeasure PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_arc_pruned_radius_budget]: the
    actual selected child radius sum is bounded by the actual
    parent radius sum times the printed complementary arc
    fraction plus 2/n, supporting 3.3.19, p. 305. *)
Lemma circular_disc_arc_pruned_radius_budget j (eta:partial_function E E)
    (hEta:is_circular_disc_radial_map H j eta) (F:{fset E}) (a b:R):
  (F `<=` H j)%fset ->0<=a ->a<=b ->b<=2* p ->
  2* rho j.+1*#|` @circular_disc_arc_pruned_step R j eta F a b|%:R<=
    (2* rho j*#|` F|%:R)*(1-(b-a)/(2* p)+2/(j+4)%:R).
Proof.
move=>hF ha hab hb.
pose c:R:= 1-(b-a)/(2* p)+2/(j+4)%:R.
pose B:= fun z:E=>@circular_disc_bad_child_indices R j eta z a b.
have hn:(0<j+4)%N by rewrite addn_gt0 orbT.
have hBudget z:z \in F ->#|` B z|%:R/(j+4)%:R<=c.
  move=>hz;exact:(@circular_disc_bad_child_count R H j eta hEta z a b (fsubsetP hF z hz) ha hab hb).
have hCount:= @finite_refinement_fraction_budget R E E (j+4)%N F B
  (fun z k=>circular_disc_child_center z (rho j) k) c hn hBudget.
have hPositive:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hNonnegative:0<=2* rho j by lra.
have hScaled:= ler_wpM2l hNonnegative hCount.
have hLeft:2* rho j*(#|` @circular_disc_arc_pruned_step R j eta F a b|%:R/(j+4)%:R)=
    2* rho j.+1*#|` @circular_disc_arc_pruned_step R j eta F a b|%:R.
  rewrite (factorial_disc_radius_step (@FactorialDiscScales.laws R));ring.
have hRight:2* rho j*(#|` F|%:R* c)=(2* rho j*#|` F|%:R)* c by ring.
change (is_true (2* rho j*(#|` @circular_disc_arc_pruned_step R j eta F a b|%:R/(j+4)%:R)<=
  2* rho j*(#|` F|%:R* c))) in hScaled.
by rewrite hLeft hRight in hScaled.
Qed.

(** Source for [circular_disc_arc_pruning_mass_step]: the
    original H1(A intersect union K_n) is at most the
    preceding original mass times the complementary arc
    fraction plus 2/n, the printed estimate of 3.3.19,
    p. 305. Exact actual level masses and the proved
    finite child count discharge every measure premise. *)
Theorem circular_disc_arc_pruning_mass_step (eta:nat->partial_function E E)
    (hEta:forall j,is_circular_disc_radial_map H j (eta j)) s (a b:R)
    (K:nat->{fset E}) (hK:is_circular_disc_arc_pruning H eta s a b K)
    (A:set E) (hA:is_circular_disc_limit H A):
  0<=a ->a<=b ->b<=2* p ->forall l,
  (mu (A `&` (\bigcup_(z in [set` K l.+1]) metric_closed_ball z (rho (s+l.+1)%N)))<=
    mu (A `&` (\bigcup_(z in [set` K l]) metric_closed_ball z (rho (s+l)%N)))*
      (1-(b-a)/(2* p)+2/((s+l)+4)%:R)%:E)%E.
Proof.
move=>ha hab hb l.
have hSubset:= @circular_disc_arc_pruning_subset R H hH eta s a b K hK.
have hOld:= @circular_disc_level_subfamily_mass R H hH A hA (s+l)%N (K l) (hSubset l).
have hNew:= @circular_disc_level_subfamily_mass R H hH A hA (s+l.+1)%N (K l.+1) (hSubset l.+1).
rewrite hOld hNew -EFinM.
have hNumeric:= @circular_disc_arc_pruned_radius_budget (s+l)%N (eta (s+l)%N)
  (hEta (s+l)%N) (K l) a b (hSubset l) ha hab hb.
rewrite (circular_arc_pruning_step hK) addnS.
exact:lee_tofin hNumeric.
Qed.
End Mass.
