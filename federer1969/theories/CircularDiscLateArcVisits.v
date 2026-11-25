(** Federer (1969), 3.3.19, p. 305: one common
    conull set visits every rational proper arc after every
    original integer cutoff. All exceptional sets are derived
    from the original finite-family contraction argument. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularTrigonometrySealed CircularDiscTreeUP CircularDiscLimitUP
  CircularDiscRadialMapUP CircularDiscRadialIntervals CircularDiscArcAvoidanceNull PartialFunctionUP
  HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Visits.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).

(** Source for [is_circular_late_arc_visitor]: countable
    interval tests for the dense every-tail conclusion of
    3.3.19, p. 305. This is a predicate on actual
    original radial values, preceding its almost-everywhere proof. *)
Definition is_circular_late_arc_visitor (eta:nat->partial_function E E) (x:E):Prop:=
  forall a b:rat,(0<=(ratr a:R)) ->(ratr a<ratr b:>R) ->(ratr b<=2* p:>R) ->
  forall v:nat,exists j:nat,exists y:E,(v<=j)%N /\
    partial_function_graph (eta j) x y /\circular_parameter_arc (ratr a) (ratr b) y.

Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.
Variable eta:nat->partial_function E E.
Hypothesis hEta:forall j,is_circular_disc_radial_map H j (eta j).

(** Source for [circular_disc_late_arc_hit_almost]: for each
    original positive proper arc and every integer cutoff,
    H1 almost every original point has a later eta_n value
    in that arc, as in 3.3.19, p. 305. *)
Theorem circular_disc_late_arc_hit_almost (a b:R) v:
  0<=a ->a<b ->b<=2* p ->
  measure_almost_everywhere_on mu A [set x:E|exists j:nat,exists y:E,
    (v<=j)%N /\partial_function_graph (eta j) x y /\circular_parameter_arc a b y].
Proof.
move=>ha hab hb.
pose P:= [set x:E|exists j:nat,exists y:E,
  (v<=j)%N /\partial_function_graph (eta j) x y /\circular_parameter_arc a b y].
have hEqual:A `\` P= A `&` [set x:E|forall j,(v<=j)%N ->forall y,
  partial_function_graph (eta j) x y ->~circular_parameter_arc a b y].
  apply/seteqP;split.
  - move=>x [hxA hNot];split=>//;move=>j hj y hGraph hArc.
    apply:hNot;exists j,y;by split=>//;split.
  - move=>x [hxA hAvoid];split=>//;move=>[j [y [hj [hGraph hArc]]]].
    exact:(hAvoid j hj y hGraph hArc).
rewrite /measure_almost_everywhere_on -/P hEqual.
exact:(@circular_disc_arc_avoidance_null R H hH A hA eta hEta a b v ha hab hb).
Qed.

(** Source for [circular_disc_late_rational_arc_visits_almost]:
    one common H1-conull subset of original A has a later
    actual eta_n value in every positive rational proper arc
    after every integer cutoff. Countability supplies the common
    set in the dense every-tail assertion of 3.3.19, p. 305. *)
Theorem circular_disc_late_rational_arc_visits_almost:
  measure_almost_everywhere_on mu A (is_circular_late_arc_visitor eta).
Proof.
pose D:set ((rat*rat)*nat)%type:=[set i:((rat*rat)*nat)%type|0<=(ratr i.1.1:R) /\
  (ratr i.1.1<ratr i.1.2:>R) /\(ratr i.1.2<=2* p:>R)].
pose P:= fun i:((rat*rat)*nat)%type=>[set x:E|A x ->exists j:nat,exists y:E,(i.2<=j)%N /\
  partial_function_graph (eta j) x y /\circular_parameter_arc (ratr i.1.1) (ratr i.1.2) y].
have hEach i:D i ->measure_almost_everywhere mu (P i).
  case:i=>[[a b] v] [ha [hab hb]].
  apply:(@measure_almost_everywhere_on_implication R E mu A _).1.
  exact:(@circular_disc_late_arc_hit_almost (ratr a:R) (ratr b:R) v ha hab hb).
have hMu:= @hausdorff_measure_is_measure R E 1.
have hAll:= @measure_almost_everywhere_countable R E _ mu hMu D P (countableP D) hEach.
apply:(@measure_almost_everywhere_on_implication R E mu A _).2.
apply:(@measure_almost_everywhere_mono R E mu hMu _ _ _ hAll).
move=>x hx hxA a b ha hab hb v.
have hD:D ((a,b),v) by split=>//;split.
exact:(hx ((a,b),v) hD hxA).
Qed.
End Visits.
