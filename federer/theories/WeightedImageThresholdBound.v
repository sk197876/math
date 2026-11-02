(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting weighted
    projected-volume estimate for the constructions of 2.10.4(1) and
    2.10.5(1), pp. 172–173. A pointwise weighted cover of A also covers
    every projected point after each source member is replaced by its image.
    Integrating the nonnegative image sum gives the threshold estimate, by
    2.4.8, p. 84, and the characteristic comparison of 2.4.12, pp. 86–87. no
    identical geometric application is attributed to it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureAlmostUP MeasureAlmostBasic
  MeasureNonnegativeThresholdBound NonnegativeSum NonnegativeSumSupport WeightedMetricEnvelopeUP WeightedGeneratorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_image_threshold_bound]: supporting
    weighted image-cover inequality for the final
    paragraph of 2.10.24, p. 188. Images may
    overlap and individual measures or the total sum
    may be infinite. Only their measurability is
    required; the map need not be injective. *)
Theorem weighted_image_threshold_bound (R : realType) (X Y J : choiceType)
    (mu : set Y -> \bar R) (p : X -> Y) (S : J -> set X)
    (G : set J) (u : J -> R) (A : set X) (t : R) :
  is_measure mu -> countable G -> (forall j, G j -> (0<=u j)%R) ->
  measure_measurable mu (p @` A) -> (forall j, G j -> measure_measurable mu (p @` S j)) ->
  (0<=t)%R -> (forall x, A x -> t%:E<=weighted_generator_sum S G u x) ->
  t%:E*mu (p @` A)<=nonnegative_sum G (fun j=>(u j)%:E*mu (p @` S j)).
Proof.
move=> hm hG hu hA hS ht hcover.
pose T j := p @` S j.
pose g y := weighted_generator_sum T G u y.
have hTS j (hj : G j) : measure_measurable mu (setT `&` T j) by rewrite setTI; exact: hS.
have hi := @weighted_generator_restriction_integral R Y J mu T G u setT hm hG hu hTS.
have hfun : weighted_generator_restriction T G u setT=g.
  apply: funext=> y; by rewrite /weighted_generator_restriction in_setT.
rewrite hfun in hi.
have hlow := @measure_lower_integral_unique R Y mu (partial_function_total g) _ _
  (measure_lower_integral_specification mu _) hi.2.2.
have hbound y (hy : (p @` A) y) : exists z, partial_function_graph (partial_function_total g) y z /\ t%:E<=z.
  have [x hx heq] := hy; exists (g y); split=> //.
  apply: le_trans (hcover x hx) _; apply: nonnegative_sum_subset=> j [hj hxj]; split=> //.
  exists x=> //; exact heq.
have hpositive : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total g)).
  apply: (@measure_almost_everywhere_mono R Y mu hm setT _ _ (measure_almost_everywhere_true hm))=> y _.
  exists (g y); split=> //; exact: nonnegative_sum_nonnegative.
have hh := @nonnegative_threshold_lower_integral_bound R Y mu hm (p @` A) t (partial_function_total g)
  hA ht hbound hpositive.
rewrite hlow in hh.
have heq : nonnegative_sum G (fun j=>(u j)%:E*mu (setT `&` T j))=
    nonnegative_sum G (fun j=>(u j)%:E*mu (p @` S j)).
  apply: nonnegative_sum_ext=> j hj; by rewrite setTI.
by rewrite heq in hh.
Qed.
