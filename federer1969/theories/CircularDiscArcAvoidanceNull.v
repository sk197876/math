(** Federer (1969), 3.3.19, p. 305: actual original
    points avoiding one proper arc at every sufficiently late
    stage form a Hausdorff-null set. All geometric recurrence
    and finite-mass premises are discharged for original A. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularTrigonometrySealed CircularDiscTreeUP CircularDiscLimitUP CircularDiscExactMass
  CircularDiscRadialMapUP CircularDiscRadialIntervals CircularDiscArcPruningUP CircularDiscArcPruningExistence
  CircularDiscArcPruningContainment CircularDiscArcPruningMass CircularDiscArcContractionCutoff
  GeometricOuterCoverNull PartialFunctionUP HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Nullity.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.
Variable eta:nat->partial_function E E.
Hypothesis hEta:forall j,is_circular_disc_radial_map H j (eta j).

(** Source for [circular_disc_arc_pruning_geometric_mass]:
    repeated application of the actual K_n estimate gives
    a finite geometric budget, supporting the vanishing
    intersection in 3.3.19, p. 305. The local late
    contraction inequality is discharged in the theorem below. *)
Lemma circular_disc_arc_pruning_geometric_mass s (a b q:R) (K:nat->{fset E})
    (hK:is_circular_disc_arc_pruning H eta s a b K):
  0<=a ->a<=b ->b<=2* p ->0<q<1 ->
  (forall l,1-(b-a)/(2* p)+2/((s+l)+4)%:R<=q) ->
  forall l,(mu (A `&` (\bigcup_(z in [set` K l])
    metric_closed_ball z (rho (s+l)%N)))<=(q^+l*2)%:E)%E.
Proof.
move=>ha hab hb hq hCoefficient.
have hMu:= @hausdorff_measure_is_measure R E 1.
pose F:= fun l:nat=>A `&` (\bigcup_(z in [set` K l]) metric_closed_ball z (rho (s+l)%N)).
have hInitial:F 0%N= A.
  rewrite /F (circular_arc_pruning_root hK) addn0.
  apply/seteqP;split;first by move=>x [hx _].
  move=>x hx;split=>//.
  have [z [hz hxZ]]:=(hA x).1 hx s.
  by exists z.
elim=>[|l ih].
- change (is_true (mu (F 0%N)<=(q^+0*2)%:E)%E).
  by rewrite hInitial (@circular_disc_hausdorff_mass R H hH A hA) expr0 mul1r.
- have hStep:= @circular_disc_arc_pruning_mass_step R H hH eta hEta s a b K hK A hA ha hab hb l.
  change (is_true (mu (F l.+1)<=mu (F l)*
    (1-(b-a)/(2* p)+2/((s+l)+4)%:R)%:E)%E) in hStep.
  have hFraction:= lee_wpmul2l (measure_nonnegative hMu (F l)) (lee_tofin (hCoefficient l)).
  have hStepQ:= le_trans hStep hFraction.
  have hUpper:= lee_wpmul2r (lee_tofin (ltW (andP hq).1)) ih.
  apply:(le_trans hStepQ).
  have hScalar:q^+l*2* q= q^+l.+1*2 by rewrite exprS;ring.
  by rewrite -EFinM hScalar in hUpper.
Qed.

(** Source for [circular_disc_arc_avoidance_null]: for every
    original late cutoff and each positive-length proper
    principal arc, the original points of A whose eta_n
    never enter that arc have actual H1 outer mass zero,
    exactly the exceptional-set argument in 3.3.19, p. 305.
    Local K_n families, their original-set containment and
    geometric decay are proved above; no independence or
    almost-everywhere angular premise is added. *)
Theorem circular_disc_arc_avoidance_null (a b:R) v:
  0<=a ->a<b ->b<=2* p ->
  mu (A `&` [set x:E|forall j,(v<=j)%N ->forall y,
    partial_function_graph (eta j) x y ->~circular_parameter_arc a b y])= 0%E.
Proof.
move=>ha hab hb.
have [q [N [hq hCutoff]]]:= @circular_disc_arc_contraction_cutoff R a b ha hab hb.
pose s:nat:= maxn v N.
have hN:(N<=s)%N by rewrite /s leq_maxr.
have hv:(v<=s)%N by rewrite /s leq_maxl.
have [K hK]:= @circular_disc_arc_pruning_exists R H eta s a b.
pose B:= A `&` [set x:E|forall j,(v<=j)%N ->forall y,
  partial_function_graph (eta j) x y ->~circular_parameter_arc a b y].
pose F:= fun l:nat=>A `&` (\bigcup_(z in [set` K l]) metric_closed_ball z (rho (s+l)%N)).
have hCover l:B `<=` F l.
  move=>x [hxA hAvoid];split=>//.
  have hLate k y:partial_function_graph (eta (s+k)%N) x y ->~circular_parameter_arc a b y.
    move=>hGraph;apply:(hAvoid (s+k)%N _ y hGraph).
    exact:(leq_trans hv (leq_addr k s)).
  have [z [hz hxZ]]:=@circular_disc_arc_pruning_contains_avoiders R H hH eta hEta
    s a b K hK A hA x hxA hLate l.
  by exists z.
have hCoefficient l:1-(b-a)/(2* p)+2/((s+l)+4)%:R<=q.
  apply:hCutoff;exact:(leq_trans hN (leq_addr l s)).
have hBudget:= @circular_disc_arc_pruning_geometric_mass s a b q K hK
  ha (ltW hab) hb hq hCoefficient.
apply:(@geometric_outer_cover_null R E mu B F q 2
  (@hausdorff_measure_is_measure R E 1) hq (ler0n _ _) hCover hBudget).
Qed.
End Nullity.
