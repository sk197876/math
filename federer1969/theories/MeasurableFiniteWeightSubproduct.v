(** Federer (1969), 3.2.20, p. 257: supporting
    measurability of the summand integrands when summing the compact
    charts. A finite measurable density recovers every dominated
    weighted subproduct, without assuming the weight measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedFiniteProjectionBorel RealReciprocalBorel
  PartialFunctionUP PartialFunctionBasic PartialDensityProduct MeasureUP MeasurableFunctionUP
  MeasurableDensityProduct MeasurableGraphEquivalence MeasurableTotalBasic MeasurableRealEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_total_zero_product]: supporting total-function
    form of the distinguished product in 2.4.10, p. 85, for
    the chart sum in Federer 3.2.20, p. 257. Both infinite
    values and the zero-infinity pairs are included. *)
Lemma measurable_total_zero_product (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : X -> extended_real_line R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>f x* g x : extended_real_line R)).
Proof.
move=> hf hg.
have hProd := measurable_density_product hm hf hg.
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hProd)=> x y.
rewrite partial_density_product_graph; split.
- by move=> [a [b [<- [<- he]]]].
- move=> he; exists (f x),(g x); by split; last split.
Qed.

(** Source for [measurable_finite_weight_subproduct]: supporting
    summand measurability in Federer 3.2.20, p. 257.
    If 0<=r<=p are finite measurable densities, measurability
    of w*p implies that of w*r. The original extended-real
    weight w need not be measurable, finite or integrable. *)
Lemma measurable_finite_weight_subproduct (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (w : X -> \bar R) (p r : X -> R) :
  (forall x,(0<=p x)%R) -> (forall x,(0<=r x<=p x)%R) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(r x)%:E : extended_real_line R)) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>w x* (p x)%:E : extended_real_line R)) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>w x* (r x)%:E : extended_real_line R)).
Proof.
move=> hp hr hpMeas hrMeas hw.
have hpReal : is_measure_measurable_function mu
    (partial_function_total (fun x=>(p x : real_line_metric R))).
  exact: (@measurable_total_borel_postcomposition R X (extended_real_line R)
    [the topologicalType of real_line_metric R] mu hm
    (fun x=>((p x)%:E : extended_real_line R)) (fun z=>(fine z:real_line_metric R))
    hpMeas (@extended_finite_projection_borel R)).
have hInvReal := @measurable_total_borel_postcomposition R X
  [the topologicalType of real_line_metric R] [the topologicalType of real_line_metric R]
  mu hm (fun x=>(p x:real_line_metric R)) (fun z=>(z^-1)%R)
  hpReal (@real_reciprocal_borel R).
have hInv := measurable_total_real_embedding hm hInvReal.
have hRatio := measurable_total_zero_product hm hrMeas hInv.
have hProd := measurable_total_zero_product hm hw hRatio.
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hProd)=> x y.
have he : (w x* (p x)%:E)* ((r x)%:E* ((p x)^-1)%R%:E)=w x* (r x)%:E.
  case: (eqVneq (p x) 0%R)=> hpx.
  - have hr0 : r x=0%R.
      apply/eqP; rewrite eq_le (andP (hr x)).1 andbT.
      by move: (andP (hr x)).2; rewrite hpx.
    by rewrite hpx hr0 !mul0e !mule0.
  - rewrite -muleA.
    have hFactor : (p x)%:E* ((r x)%:E* ((p x)^-1)%R%:E)=(r x)%:E.
      by rewrite -!EFinM mulrCA mulfV // mulr1.
    by rewrite hFactor.
by change ((w x* (p x)%:E)* ((r x)%:E* ((p x)^-1)%R%:E)=y <-> w x* (r x)%:E=y); rewrite he.
Qed.
