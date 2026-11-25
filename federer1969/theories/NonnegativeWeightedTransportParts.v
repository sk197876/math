(** Federer (1969), 3.2.20, pp. 256–257: recover the
    arbitrary signed extended weight after summing nonnegative chart
    integrals. Apply the exact two-part criterion of 2.4.4(6), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureUpperIntegralPositivePart PartialFunctionIntegralParts
  MeasureIntegralPartsDifference FiniteWeightExtendedTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_nonnegative_product_positive_part]: supporting
    part identity for Federer 3.2.20, p. 257, using
    2.1.1(11), p. 53. The nonnegative second factor may be
    infinite; zero times either infinity retains its distinguished value. *)
Lemma extended_nonnegative_product_positive_part (R : realType) (z b : \bar R) :
  0<=b -> extended_positive_part (z* b)=extended_positive_part z* b.
Proof.
move=> hb; case: (leP 0 z)=> hz.
- have hProd : 0<=z* b := mule_ge0 hz hb.
  by rewrite /extended_positive_part (max_idPl hProd) (max_idPl hz).
- have hProd : z* b<=0 := mule_le0_ge0 (ltW hz) hb.
  by rewrite /extended_positive_part (max_idPr hProd) (max_idPr (ltW hz)) mul0e.
Qed.

(** Source for [extended_nonnegative_product_negative_part]: supporting
    negative-part identity for the signed weight in Federer
    3.2.20, p. 257. Infinite densities and signed
    infinite weights obey the same exact scalar formula. *)
Lemma extended_nonnegative_product_negative_part (R : realType) (z b : \bar R) :
  0<=b -> extended_negative_part (z* b)=extended_negative_part z* b.
Proof.
move=> hb; rewrite /extended_negative_part -mulNe.
exact: (@extended_nonnegative_product_positive_part R (-z) b hb).
Qed.

(** Source for [nonnegative_weighted_transport_signed]: supporting
    final signed reconstruction in Federer 3.2.20, p. 257,
    via 2.4.4(6), p. 82. A proved transformation for every
    nonnegative extended weight implies exact equality of the two
    signed integral graphs, including both infinities and undefined
    infinity differences. No unweighted measurability is assumed. *)
Theorem nonnegative_weighted_transport_signed (R : realType)
    (X Y Z : choiceType) (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu)
    (u : X -> Z) (v : Y -> Z) (p : X -> \bar R) (q : Y -> \bar R) :
  (forall x,0<=p x) -> (forall y,0<=q y) ->
  (forall (g : Z -> \bar R),(forall z,0<=g z) -> forall a,
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* p x : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* q y : extended_real_line R)) a) ->
  forall (g : Z -> \bar R) a,
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* p x : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* q y : extended_real_line R)) a.
Proof.
move=> hp hq hNonneg g a.
pose U (x : X) : extended_real_line R := g (u x)* p x.
pose V (y : Y) : extended_real_line R := g (v y)* q y.
have hPos b : is_measure_integral mu
    (partial_extended_function_positive_part (partial_function_total U)) b <->
    is_measure_integral nu (partial_extended_function_positive_part (partial_function_total V)) b.
  rewrite !/partial_extended_function_positive_part !total_postcomposition_integral_iff.
  have hU : (fun x=>extended_positive_part (U x) : extended_real_line R)=
      (fun x=>extended_positive_part (g (u x))* p x : extended_real_line R).
    apply: funext=> x; exact: (@extended_nonnegative_product_positive_part R (g (u x)) (p x) (hp x)).
  have hV : (fun y=>extended_positive_part (V y) : extended_real_line R)=
      (fun y=>extended_positive_part (g (v y))* q y : extended_real_line R).
    apply: funext=> y; exact: (@extended_nonnegative_product_positive_part R (g (v y)) (q y) (hq y)).
  rewrite hU hV.
  exact: (hNonneg (fun z=>extended_positive_part (g z))
    (fun z=>extended_positive_part_nonnegative (g z)) b).
have hNeg b : is_measure_integral mu
    (partial_extended_function_negative_part (partial_function_total U)) b <->
    is_measure_integral nu (partial_extended_function_negative_part (partial_function_total V)) b.
  rewrite !/partial_extended_function_negative_part !total_postcomposition_integral_iff.
  have hU : (fun x=>extended_negative_part (U x) : extended_real_line R)=
      (fun x=>extended_negative_part (g (u x))* p x : extended_real_line R).
    apply: funext=> x; exact: (@extended_nonnegative_product_negative_part R (g (u x)) (p x) (hp x)).
  have hV : (fun y=>extended_negative_part (V y) : extended_real_line R)=
      (fun y=>extended_negative_part (g (v y))* q y : extended_real_line R).
    apply: funext=> y; exact: (@extended_nonnegative_product_negative_part R (g (v y)) (q y) (hq y)).
  rewrite hU hV.
  exact: (hNonneg (fun z=>extended_negative_part (g z))
    (fun z=>extended_negative_part_nonnegative (g z)) b).
change (is_measure_integral mu (partial_function_total U) a <->
  is_measure_integral nu (partial_function_total V) a).
rewrite (measure_integral_parts_iff hm _ a) (measure_integral_parts_iff hn _ a).
split; move=> [P [N [hP [hN hDiff]]]]; exists P,N; split.
- exact: (hPos P).1 hP.
- split; [exact: (hNeg N).1 hN|exact hDiff].
- exact: (hPos P).2 hP.
- split; [exact: (hNeg N).2 hN|exact hDiff].
Qed.
