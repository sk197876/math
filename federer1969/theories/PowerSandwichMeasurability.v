(** Federer (1969), 3.2.22, pp. 259–260:
    measurable distortion approximations give a measurable
    intrinsic Jacobian by the almost-limit theorem 2.3.2(6). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostEquality MeasurableFunctionUP MeasurableAlmostModification MeasurableTotalLimits
  NearOnePowerParameters ReciprocalSandwichConvergence RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_sandwich_measurability]: supporting the
    integrals of the intrinsic Jacobian in Federer 3.2.22,
    pp. 259–260. Select countably many measurable
    approximations whose distortion powers are 1+1/(j+1).
    On a common conull set they converge to J, so
    2.3.2(6), pp. 73–74, proves measurability.
    For degree zero a single approximation already agrees
    almost everywhere. Only existing complete measure laws
    and local existential choices are used. *)
Theorem power_sandwich_measurability (R:realType) (X:choiceType)
    (rho:set X->\bar R) q (J:X->real_line_metric R):
  is_measure rho ->(forall x,0<=J x) ->
  (forall lambda:R,1<lambda ->exists h:X->real_line_metric R,
    is_measure_measurable_function rho (partial_function_total h) /\
    measure_almost_everywhere rho [set x|
      (lambda^+q)^-1*J x<=h x /\ h x<=lambda^+q*J x]) ->
  is_measure_measurable_function rho (partial_function_total J).
Proof.
move=>hr hJ; case:q=>[|q] hApprox.
- have hTwo:1<(2:R) by rewrite ltr1n.
  have [h [hMeas hBounds]]:=hApprox 2 hTwo.
  apply:(measurable_function_almost_equal hr hMeas).
  apply:(measure_almost_everywhere_mono hr _ hBounds)=>x [hL hU].
  rewrite expr0 invr1 !mul1r in hL hU.
  have hEq:h x=J x by apply/eqP; rewrite eq_le hU hL.
  exists (h x); split; first reflexivity; exact:esym hEq.
have hEach j:exists h:X->real_line_metric R,
    is_measure_measurable_function rho (partial_function_total h) /\
    measure_almost_everywhere rho [set x|
      (1+(j.+1%:R:R)^-1)^-1*J x<=h x /\ h x<=(1+(j.+1%:R:R)^-1)*J x].
  have ht:1<(1+(j.+1%:R:R)^-1) by rewrite ltrDl invr_gt0 ltr0n.
  have [lambda [hLambda hPower]]:=@near_one_positive_power_parameter R q.+1
    (1+(j.+1%:R:R)^-1) (ltn0Sn q) ht.
  have [h [hMeas hBounds]]:=hApprox lambda hLambda.
  exists h; split; first exact hMeas; by rewrite hPower in hBounds.
have [h hLaws]:=choice hEach.
have hAll:=@measure_almost_everywhere_countable R X [the choiceType of (nat:Type)] rho hr
  setT (fun j=>[set x|(1+(j.+1%:R:R)^-1)^-1*J x<=h j x /\
    h j x<=(1+(j.+1%:R:R)^-1)*J x]) (countableP _) (fun j _=>(hLaws j).2).
apply:(measurable_total_functions_almost_limit hr (fun j=>(hLaws j).1) hAll)=>x hEvery.
exact:(reciprocal_sandwich_convergence (hJ x) (fun j=>hEvery j Logic.I)).
Qed.
