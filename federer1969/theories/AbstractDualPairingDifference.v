(** Federer (1969), 4.1.5, p. 350:
    linearity and the integral difference underlying
    continuity of the L1 extension. These graph laws
    preserve the exact common partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom PartialFunctionUP PartialNormedArithmetic PartialFunctionPostcomposition
  ExtendedRealPartial PartialExtendedArithmetic AbstractDualPartialPairing MeasureUP MeasureIntegralUP
  MeasureIntegralDifference MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section AbstractDualPairingDifference.
Variable R:realType.
Variable X:choiceType.
Variable Y D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable xi:X->D.

(** Source for [abstract_dual_pairing_subtract_graph]:
    the literal pairing preserves differences on
    their common partial domain, supporting the L1
    extension in Federer 4.1.5, p. 350. *)
Lemma abstract_dual_pairing_subtract_graph (f g:partial_function X Y) x z:
  partial_function_graph (partial_extended_function_subtract
    (abstract_dual_partial_pairing ed xi f) (abstract_dual_partial_pairing ed xi g)) x z <->
  partial_function_graph (abstract_dual_partial_pairing ed xi (partial_vector_subtract f g)) x z.
Proof.
rewrite /partial_extended_function_subtract partial_extended_function_add_graph.
split.
- move=>[a [b [ha [hb he]]]].
  move/abstract_dual_partial_pairing_graph:ha=>[u [hu ea]].
  move:hb=>[c [hc eb]].
  move/abstract_dual_partial_pairing_graph:hc=>[v [hv ec]].
  rewrite -ea -eb -ec /extended_add /= in he.
  have hz:(ed (xi x) u-ed (xi x) v)%:E=z by case:he.
  apply/abstract_dual_partial_pairing_graph; exists (u-v); split.
  + apply/partial_vector_subtract_graph; exists u,v; by split=>//; split.
  + by rewrite linearB.
- move/abstract_dual_partial_pairing_graph=>[w [hw hz]].
  move/partial_vector_subtract_graph:hw=>[u [v [hu [hv ew]]]].
  exists (ed (xi x) u)%:E,(-(ed (xi x) v)%:E)%E; split.
  + apply/abstract_dual_partial_pairing_graph; exists u; by split.
  + split.
    * exists (ed (xi x) v)%:E; split=>//.
      apply/abstract_dual_partial_pairing_graph; exists v; by split.
    * rewrite /extended_add /= ew linearB in hz *.
      by rewrite -EFinD hz.
Qed.

(** Source for [abstract_dual_pairing_difference_integral]:
    finite L1 pair integrals preserve subtraction,
    Federer 4.1.5, p. 350, using
    2.4.4(3), (4), pp. 82–83. *)
Lemma abstract_dual_pairing_difference_integral (mu:set X->\bar R) (hm:is_measure mu)
    (f g:partial_function X Y) (a b:R):
  is_measure_integral mu (abstract_dual_partial_pairing ed xi f) a%:E ->
  is_measure_integral mu (abstract_dual_partial_pairing ed xi g) b%:E ->
  is_measure_integral mu (abstract_dual_partial_pairing ed xi (partial_vector_subtract f g)) (a-b)%:E.
Proof.
move=>hA hB.
exact:(measure_integral_graph_equivalent (abstract_dual_pairing_subtract_graph f g)
  (@measure_integral_finite_difference R X mu hm _ _ a b hA hB)).
Qed.
End AbstractDualPairingDifference.
