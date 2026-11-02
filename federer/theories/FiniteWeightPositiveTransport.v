(** Federer (1969), 3.2.20, p. 257: extend the finite-real
    transformation in 3.2.5(2), pp. 244–245, to positive parts
    of arbitrary extended-real weights by 2.4.7, p. 84. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral
  TotalIncreasingIntegralValues TotalIncreasingIntegralSupremum
  FiniteWeightTruncationAlgebra FiniteWeightedTruncationLimit MeasurableWeightedTruncation
  FiniteWeightIntegralTransportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_weight_positive_part_transport_forward]: supporting
    monotone-limit step in Federer 3.2.20, p. 257. Only
    the given weighted positive integrand and the finite source density
    need be measurable. The unweighted function may be arbitrary and
    either the original weight or its integral may be infinite. *)
Theorem finite_weight_positive_part_transport_forward (R : realType)
    (X Y Z : choiceType) (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu)
    (u : X -> Z) (v : Y -> Z) (p : X -> R) (q : Y -> R) :
  (forall x,(0<=p x)%R) -> (forall y,(0<=q y)%R) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) ->
  (forall (h : Z -> R) a,
    is_measure_integral mu (partial_function_total (fun x=>(h (u x))%:E* (p x)%:E : extended_real_line R)) a ->
    is_measure_integral nu (partial_function_total (fun y=>(h (v y))%:E* (q y)%:E : extended_real_line R)) a) ->
  forall (g : Z -> \bar R) a,
    is_measure_integral mu (partial_function_total
      (fun x=>extended_positive_part (g (u x)* (p x)%:E) : extended_real_line R)) a ->
    is_measure_integral nu (partial_function_total
      (fun y=>extended_positive_part (g (v y)* (q y)%:E) : extended_real_line R)) a.
Proof.
move=> hp hq hpMeas hTransport g a hI.
pose h n z := fine (Order.min (extended_positive_part (g z)) (n.+1)%:R%:E).
have hClip n z : (0<=h n z<=(n.+1)%:R)%R /\
    (h n z)%:E=Order.min (extended_positive_part (g z)) (n.+1)%:R%:E.
  have hc : (0<=((n.+1)%:R : R))%R by rewrite ler0n.
  have [b [hb he]] := @finite_positive_weight_truncation_exists R (g z) (n.+1)%:R hc.
  rewrite /h -he /=; by split.
pose us n (x : X) : extended_real_line R := (h n (u x))%:E* (p x)%:E.
pose vs n (y : Y) : extended_real_line R := (h n (v y))%:E* (q y)%:E.
have hu0 n x : 0<=us n x.
  apply: mule_ge0; rewrite lee_fin; [exact: (andP (hClip n (u x)).1).1|exact: hp].
have hv0 n y : 0<=vs n y.
  apply: mule_ge0; rewrite lee_fin; [exact: (andP (hClip n (v y)).1).1|exact: hq].
have huMeas n : is_measure_measurable_function mu (partial_function_total (us n)).
  have hc : ((n.+1)%:R : R)!=0%R by rewrite pnatr_eq0.
  exact: (@measurable_finite_weighted_truncation R X mu hm
    (fun x=>g (u x)) p (fun x=>h n (u x)) (n.+1)%:R hc hp
    (fun x=>(hClip n (u x)).2) hpMeas hI.1).
pose asq n := measure_lower_integral mu (partial_function_total (us n)).
have huI n : is_measure_integral mu (partial_function_total (us n)) (asq n).
  have hPos : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total (us n))).
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
      (measure_almost_everywhere_true hm))=> x _; exists (us n x); split; first reflexivity.
    exact: hu0.
  exact: (nonnegative_measurable_function_integral hm (huMeas n) hPos).1.
have hvI n : is_measure_integral nu (partial_function_total (vs n)) (asq n).
  exact: (hTransport (h n) (asq n) (huI n)).
have huLim x : extended_increases_to (fun n=>us n x)
    (extended_positive_part (g (u x)* (p x)%:E)).
  have he : (fun n=>us n x)=
      (fun n=>(Order.min (extended_positive_part (g (u x))) (n.+1)%:R%:E)* (p x)%:E).
    by apply: funext=> n; rewrite /us (hClip n (u x)).2.
  rewrite he finite_nonnegative_weight_positive_part //.
  exact: (@finite_weighted_truncations_increase R (extended_positive_part (g (u x))) (p x) (hp x)).
have hvLim y : extended_increases_to (fun n=>vs n y)
    (extended_positive_part (g (v y)* (q y)%:E)).
  have he : (fun n=>vs n y)=
      (fun n=>(Order.min (extended_positive_part (g (v y))) (n.+1)%:R%:E)* (q y)%:E).
    by apply: funext=> n; rewrite /vs (hClip n (v y)).2.
  rewrite he finite_nonnegative_weight_positive_part //.
  exact: (@finite_weighted_truncations_increase R (extended_positive_part (g (v y))) (q y) (hq y)).
have haLim := @total_increasing_integral_values R X mu hm us _ asq a hu0 huLim huI hI.
exact: (@total_increasing_integral_supremum R Y nu hn vs _ asq a
  hv0 hvLim hvI (extended_increasing_limit_supremum haLim)).
Qed.

(** Source for [finite_weight_positive_part_transport]: supporting exact
    positive-part integral-graph equality in Federer 3.2.20,
    p. 257. Both directions follow from the finite-weight law
    and increasing convergence; no measurability of g is assumed. *)
Theorem finite_weight_positive_part_transport (R : realType)
    (X Y Z : choiceType) (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu)
    (u : X -> Z) (v : Y -> Z) (p : X -> R) (q : Y -> R) :
  (forall x,(0<=p x)%R) -> (forall y,(0<=q y)%R) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) ->
  is_measure_measurable_function nu (partial_function_total (fun y=>(q y)%:E : extended_real_line R)) ->
  is_finite_weight_pair_transport mu nu u v p q -> forall (g : Z -> \bar R) a,
    is_measure_integral mu (partial_function_total
      (fun x=>extended_positive_part (g (u x)* (p x)%:E) : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total
      (fun y=>extended_positive_part (g (v y)* (q y)%:E) : extended_real_line R)) a.
Proof.
move=> hp hq hpMeas hqMeas hTransport g a; split.
- exact: (@finite_weight_positive_part_transport_forward R X Y Z mu nu hm hn u v p q
    hp hq hpMeas (fun h b=>(hTransport h b).1) g a).
- exact: (@finite_weight_positive_part_transport_forward R Y X Z nu mu hn hm v u q p
    hq hp hqMeas (fun h b=>(hTransport h b).2) g a).
Qed.
