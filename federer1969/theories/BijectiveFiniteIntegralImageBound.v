(** Federer (1969), 3.2.31, p. 269: supporting transport of a
    nonnegative finite integral through the small linear rescaling.
    Image-measure integration is 2.4.18, pp. 90–91; the setwise
    bound is supplied by 3.2.30, p. 268. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition MeasureUP MeasurePushforward PushforwardMeasurableSets
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralBounds
  MeasureIntegralUniqueness PushforwardIntegral FiniteDominatedNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bijective_finite_integral_image_bound]: supporting
    rescaled integral inequality in Federer 3.2.31, p. 269.
    Both inverse identities identify the actual image sets. The
    measurable transformed integrand is proved separately in each
    application, for compact fibres by 2.10.26, pp. 189–190.
    No invariance of arbitrary completed measurable sets is assumed. *)
Theorem bijective_finite_integral_image_bound (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_borel_regular_measure mu)
    (T U:X->X) (f:X->extended_real_line R) (a c:R):
  cancel T U ->cancel U T ->continuous U ->(0<c)%R ->
  (forall A,mu (T @` A)<=c%:E*mu A) ->
  (forall x,0<=f x) ->
  is_measure_integral mu (partial_function_total f) a%:E ->
  is_measure_measurable_function mu (partial_function_total (fun x=>f (U x))) ->
  measure_upper_integral mu (partial_function_total (fun x=>f (U x)))<=c%:E*a%:E.
Proof.
move=>hTU hUT hU hc hImage hp hi hfU.
pose nu:=measure_pushforward U mu.
have hn:is_measure nu:=measure_pushforward_is_measure U hm.
have hB B (h:borel_set B):measure_measurable nu B.
  apply:pushforward_measurable_from_preimage.
  apply:(borel_regular_borel_measurable hm hr).
  exact (@continuous_borel_preimage X X U hU B h).
have hDom A:nu A<=c%:E*mu A.
  have hSets:U @^-1` A=T @` A.
    apply/seteqP; split=>x.
    - move=>hx; exists (U x)=>//; exact:hUT.
    - move=>[y hy <-]; by rewrite /= hTU.
  by rewrite /nu /measure_pushforward hSets; exact:hImage.
have [b [hbi [hb0 hba]]]:=@finite_dominated_nonnegative_integral R X
  mu nu hm hn hr f a c hc hB hDom hp hi.
have hPre:is_measure_measurable_function mu
    (partial_function_precompose U (partial_function_total f)).
  exact hfU.
have hBack:=(measure_pushforward_integral_iff hm hPre b).2 hbi.
have hTotal:is_measure_integral mu (partial_function_total (fun x=>f (U x))) b.
  apply:(measure_integral_graph_equivalent _ hBack)=>x y.
  exact:partial_function_precompose_total.
have hValue:=measure_upper_integral_unique
  (measure_upper_integral_specification mu _) hTotal.2.1.
by rewrite hValue.
Qed.
