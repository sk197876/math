(** Federer (1969), 2.10.24(1), p. 187, integral of h_j: interchange the
    nonnegative weighted generator sum and the integral, by 2.4.8, p. 84.
    The characteristic restriction is B_j. This is supporting
    infrastructure, not a separate book claim. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureIntegralUP MeasureCountableNonnegativeSum
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral
  NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction NumericalSum PartialNumericalSumUP
  WeightedMetricEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_generator_restriction]: supporting
    h_j=g_j times the characteristic function of B_j
    in 2.10.24(1), p. 187. The two-case presentation
    preserves zero times infinity equal to zero. *)
Definition weighted_generator_restriction (R : realType) (X J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) (B : set X) x : \bar R :=
  if x \in B then weighted_generator_sum S G u x else 0.

(** Source for [weighted_generator_restriction_nonnegative]:
    supporting nonnegativity of h_j for the Fatou step
    in 2.10.24(1), p. 187. *)
Lemma weighted_generator_restriction_nonnegative (R : realType) (X J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) (B : set X) x :
  0<=weighted_generator_restriction S G u B x.
Proof. rewrite /weighted_generator_restriction; case: ifP=> _; [exact: nonnegative_sum_nonnegative|exact: lexx]. Qed.

(** Source for [weighted_generator_restriction_integral]:
    supporting identity integral h_j=sum u_j(S) psi(B_j cap S)
    in 2.10.24(1), p. 187. Countably many measurable
    generators suffice; the integral and individual measures
    may be infinite and zero weights are retained. *)
Theorem weighted_generator_restriction_integral (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (S : J -> set X) (G : set J) (u : J -> R) (B : set X) :
  is_measure mu -> countable G -> (forall j, G j -> (0<=u j)%R) ->
  (forall j, G j -> measure_measurable mu (B `&` S j)) ->
  is_measure_integral mu (partial_function_total (weighted_generator_restriction S G u B))
    (nonnegative_sum G (fun j=>(u j)%:E*mu (B `&` S j))).
Proof.
move=> hm hG hu hBS.
pose s j := @CharacteristicFunction.value R X (B `&` S j).
have hs j := @CharacteristicFunction.laws R X (B `&` S j).
pose v j x := ((u j)%:E*(s j x)%:E : extended_real_line R).
have hv j (hj : G j) x : 0<=v j x.
  apply: mule_ge0; [by rewrite lee_fin; exact: hu|exact: (@characteristic_extended_nonnegative R X (B `&` S j) (s j) (hs j) x)].
have hpos j (hj : G j) : 0<=(u j)%:E by rewrite lee_fin; exact: hu.
have hi j (hj : G j) := @measure_nonnegative_extended_characteristic_integral R X mu hm
  (B `&` S j) (s j) (u j)%:E (hs j) (hBS j hj) (hpos j hj).
have hpoint x : nonnegative_sum G (fun j=>v j x)=weighted_generator_restriction S G u B x.
  rewrite /weighted_generator_restriction; case: ifPn=> hxB.
  - rewrite /weighted_generator_sum -nonnegative_sum_restrict.
    apply: nonnegative_sum_ext=> j hj.
    case: ifPn=> hxS.
    + rewrite /v /s (characteristic_on_set (hs j) (conj (set_mem hxB) (set_mem hxS))) mule1; by [].
    + rewrite /v /s (characteristic_off_set (hs j)) ?mule0 //.
      move=> [_ hx]; apply: (negP hxS).
      have hjx : j \in [set j | S j x] by apply: mem_set; exact hx.
      exact hjx.
  - apply: nonnegative_sum_zero=> j hj; rewrite /v /s (characteristic_off_set (hs j)) ?mule0 //.
    move=> [hx _]; apply: (negP hxB); exact: mem_set hx.
apply: (@measure_countable_nonnegative_integral_values R X J mu hm G
  (fun j=>partial_function_total (v j)) _ _ hG); last first.
- exact hi.
- by move=> j hj x y <-; exact: hv.
- move=> x z; split.
  + move=> hz; exists (fun j=>v j x); split; first by move=> j hj.
    rewrite (numerical_sum_nonnegative (fun j hj=>hv j hj x)) hpoint.
    by rewrite (hz : weighted_generator_restriction S G u B x=z).
  + move=> [w [hw hsum]].
    have hw0 j (hj : G j) : 0<=w j by rewrite -(hw j hj : v j x=w j); exact: hv.
    rewrite (numerical_sum_nonnegative hw0) in hsum; case: hsum=> <-.
    change (weighted_generator_restriction S G u B x=nonnegative_sum G w).
    rewrite -hpoint; apply: nonnegative_sum_ext=> j hj; exact: hw.
Qed.
