(** Repeated nonnegative integration supporting Federer (1969), 2.10.16, p.
    178. Average a normal-coordinate count over an additional orthogonal
    rotation. The two orders of integration identify its invariant value
    with the mean Jacobian times the rotational count constant. Federer
    2.6.2(4), p. 115, proof p. 117 *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasurableFunctionUP
  CountablyMeasurableUP CountablyMeasurableProduct ProductMeasure ProductMeasureShuffle MeasureBijectionUP
  TotalNonnegativeProductIntegral TotalNonnegativeExtendedScaleIntegral PositiveCharacteristicMeasurability
  PushforwardTotalNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rotated_product_integral_value]: supporting
    equality of the two rotation averages for 2.10.16,
    p. 178. All section integrals and joint measurability
    are premises here, discharged for the actual normal-map
    family in the application. Values I and B may be
    infinite, and all multiplications use 0 times infinity=0. *)
Theorem rotated_product_integral_value (R : realType) (X P G : choiceType)
    (alpha : set X -> \bar R) (beta : set P -> \bar R) (theta : set G -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (ht : is_measure theta)
    (h : (X*P)*G -> extended_real_line R) (j : P -> extended_real_line R) (I B c : \bar R) :
  measure_countably_measurable alpha setT -> measure_countably_measurable beta setT ->
  measure_countably_measurable theta setT -> theta setT= 1 ->
  0<=I -> 0<=B -> (forall z, 0<=h z) -> (forall p, 0<=j p) ->
  is_measure_measurable_function (product_measure (product_measure_is_measure ha hb) ht) (partial_function_total h) ->
  (forall g, is_measure_integral (product_measure ha hb) (partial_function_total (fun z => h (z,g))) I) ->
  (forall p, is_measure_integral (product_measure ha ht)
    (partial_function_total (fun z => h ((z.1,p),z.2))) (B*j p)) ->
  is_measure_integral beta (partial_function_total j) c -> I=B*c.
Proof.
move=> hX hP hG ht1 hI hB hp hj hm hs hr hjint.
pose mu := product_measure (product_measure_is_measure ha hb) ht.
pose hmu := product_measure_is_measure (product_measure_is_measure ha hb) ht.
have hwXP := @product_whole_countably_measurable R X P alpha beta ha hb hX hP.
have hw := @product_whole_countably_measurable R (X*P)%type G (product_measure ha hb) theta
  (product_measure_is_measure ha hb) ht hwXP hG.
have hi := total_nonnegative_integral_specification hmu hp hm.
pose v := measure_lower_integral mu (partial_function_total h).
have hconst := @total_nonnegative_product_sections R (X*P)%type G (product_measure ha hb) theta
  (product_measure_is_measure ha hb) ht h (fun _ => I) hw hp hm hs.
have hcI := @nonnegative_extended_constant_integral R G theta ht I hI.
rewrite ht1 mule1 in hcI.
have hev : v=I := measure_integral_unique hconst hcI.
pose k (z : (X*G)*P) := h ((z.1.1,z.2),z.1.2).
pose T (z : (X*P)*G) := ((z.1.1,z.2),z.1.2).
have hbij := @countable_product_three_exchange R X P G alpha beta theta ha hb ht hX hP hG.
have heT : (fun z => k (T z))=h by apply/funext=> -[[x p] g].
have hmk : is_measure_measurable_function mu (partial_function_total (fun z => k (T z))) by rewrite heT.
have [w [hw1 hw2]] := @pushforward_total_nonnegative_integrals R ((X*P)*G)%type ((X*G)*P)%type
  mu hmu T k (fun z => hp _) hmk.
rewrite heT in hw1.
rewrite (measure_bijection_pushforward hbij) in hw2.
have hew : w=I by rewrite -(measure_integral_unique hi hw1); exact hev.
rewrite hew in hw2.
have hwXG := @product_whole_countably_measurable R X G alpha theta ha ht hX hG.
have hwt := @product_whole_countably_measurable R (X*G)%type P (product_measure ha ht) beta
  (product_measure_is_measure ha ht) hb hwXG hP.
have houter := @total_nonnegative_product_sections R (X*G)%type P (product_measure ha ht) beta
  (product_measure_is_measure ha ht) hb k (fun p => B*j p) hwt (fun z => hp _) hw2.1 hr.
have heI : measure_lower_integral (product_measure (product_measure_is_measure ha ht) hb)
    (partial_function_total k)=I.
  exact (measure_integral_unique
    (total_nonnegative_integral_specification (product_measure_is_measure (product_measure_is_measure ha ht) hb)
      (fun z => hp _) hw2.1) hw2).
rewrite heI in houter.
exact: measure_integral_unique houter (total_nonnegative_extended_scale_integral hb hj hjint hB).
Qed.
