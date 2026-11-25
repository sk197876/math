(** Federer (1969), 3.2.20, pp. 256–257: arbitrary
    extended-real weights, obtained from the finite-real transformation
    by increasing convergence and the two part integrals of
    2.4.4(6), p. 82. Undefined infinity differences stay undefined. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureUpperIntegralPositivePart PartialFunctionIntegralParts
  MeasureIntegralPartsDifference FiniteWeightIntegralTransportUP FiniteWeightPositiveTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_postcomposition_integral_iff]: supporting exact
    graph bookkeeping for the positive and negative part integrals
    in Federer 3.2.20, p. 257, via 2.4.4(6), p. 82.
    Total postcomposition preserves every defined integral value. *)
Lemma total_postcomposition_integral_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R)
    (k : extended_real_line R -> extended_real_line R) a :
  is_measure_integral mu (partial_function_postcompose (partial_function_total f) k) a <->
  is_measure_integral mu (partial_function_total (fun x=>k (f x))) a.
Proof.
have he x y : partial_function_graph (partial_function_postcompose (partial_function_total f) k) x y <->
    partial_function_graph (partial_function_total (fun x=>k (f x))) x y.
  split; first by move=> [z [<- hy]].
  move=> hy; exists (f x); by split.
split; [exact: (measure_integral_graph_equivalent he)|
  exact: (measure_integral_graph_equivalent (fun x y=>iff_sym (he x y)))].
Qed.

(** Source for [finite_weight_extended_integral_transport]: supporting
    extended-real form of the two transformations used in Federer
    3.2.20, p. 257. Equality includes both infinite integral
    values and exact signed definedness. No unweighted measurability,
    summability or finiteness of total density mass is assumed. *)
Theorem finite_weight_extended_integral_transport (R : realType)
    (X Y Z : choiceType) (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu)
    (u : X -> Z) (v : Y -> Z) (p : X -> R) (q : Y -> R) :
  (forall x,(0<=p x)%R) -> (forall y,(0<=q y)%R) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) ->
  is_measure_measurable_function nu (partial_function_total (fun y=>(q y)%:E : extended_real_line R)) ->
  is_finite_weight_pair_transport mu nu u v p q -> forall (g : Z -> \bar R) a,
    is_measure_integral mu (partial_function_total
      (fun x=>g (u x)* (p x)%:E : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total
      (fun y=>g (v y)* (q y)%:E : extended_real_line R)) a.
Proof.
move=> hp hq hpMeas hqMeas hTransport g a.
pose U (x : X) : extended_real_line R := g (u x)* (p x)%:E.
pose V (y : Y) : extended_real_line R := g (v y)* (q y)%:E.
have hPos b : is_measure_integral mu
    (partial_extended_function_positive_part (partial_function_total U)) b <->
    is_measure_integral nu
    (partial_extended_function_positive_part (partial_function_total V)) b.
  rewrite !/partial_extended_function_positive_part !total_postcomposition_integral_iff.
  exact: (@finite_weight_positive_part_transport R X Y Z mu nu hm hn u v p q
    hp hq hpMeas hqMeas hTransport g b).
have hNeg b : is_measure_integral mu
    (partial_extended_function_negative_part (partial_function_total U)) b <->
    is_measure_integral nu
    (partial_extended_function_negative_part (partial_function_total V)) b.
  rewrite !/partial_extended_function_negative_part !total_postcomposition_integral_iff.
  have hU : (fun x=>extended_negative_part (U x) : extended_real_line R)=
      (fun x=>extended_positive_part ((-g (u x))* (p x)%:E) : extended_real_line R).
    by apply: funext=> x; rewrite /U /extended_negative_part -mulNe.
  have hV : (fun y=>extended_negative_part (V y) : extended_real_line R)=
      (fun y=>extended_positive_part ((-g (v y))* (q y)%:E) : extended_real_line R).
    by apply: funext=> y; rewrite /V /extended_negative_part -mulNe.
  rewrite hU hV.
  exact: (@finite_weight_positive_part_transport R X Y Z mu nu hm hn u v p q
    hp hq hpMeas hqMeas hTransport (fun z=>-g z) b).
change (is_measure_integral mu (partial_function_total U) a <->
  is_measure_integral nu (partial_function_total V) a).
rewrite (measure_integral_parts_iff hm _ a) (measure_integral_parts_iff hn _ a).
split; move=> [P [N [hP [hN hDiff]]]]; exists P,N; split.
- exact: (hPos P).1 hP.
- split; [exact: (hNeg N).1 hN|exact hDiff].
- exact: (hPos P).2 hP.
- split; [exact: (hNeg N).2 hN|exact hDiff].
Qed.
