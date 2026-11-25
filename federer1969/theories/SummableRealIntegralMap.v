(** Federer (1969), 2.6.4, pp. 118–119: the linear integral maps in the
    corrected tensor diagram. The total-domain convention follows erratum p.
    2, book p. 119 lines 3, 4, 6. Only the abstract sealed real-integral
    functional and its actual integral laws are used. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealArithmetic SummableRealSpace RealIntegralFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Integral.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Variable hm : is_measure mu.

(** Source for [summable_real_integral_map]: the map sending a
    total-domain L1 function to its integral in Federer 2.6.4,
    p. 119, with the erratum's domain correction. *)
Definition summable_real_integral_map (f : summable_real_space hm) : R^o :=
  @lattice_measure_integral R X mu (summable_real_functions mu) (fun _ h => h)
    (summable_real_value f).

(** Source for [summable_real_integral_map_specification]: the
    defining integral identity in Federer 2.6.4, p. 119,
    for each member of the total-domain L1 carrier. *)
Lemma summable_real_integral_map_specification f :
  is_measure_integral mu (real_total_integrand (summable_real_value f))
    (summable_real_integral_map f)%:E.
Proof.
apply: lattice_measure_integral_specification; exact: summable_real_value_summable.
Qed.

(** Source for [summable_real_integral_map_linear]: linearity
    of the maps in Federer's 2.6.4 diagram, p. 119,
    from the actual additive and scalar integral laws. *)
Lemma summable_real_integral_map_linear : linear summable_real_integral_map.
Proof.
move=> c f g.
have hi := @real_total_integral_scale R X mu hm _ _ c
  (summable_real_integral_map_specification f).
have hj := @real_total_integral_add R X mu hm _ _ _ _ hi
  (summable_real_integral_map_specification g).
have hk := summable_real_integral_map_specification (c *: f+g).
have he : summable_real_value (c *: f+g) =
    (fun x => c * summable_real_value f x + summable_real_value g x).
  by rewrite linearP !fctE.
rewrite he in hk; exact: EFin_inj (measure_integral_unique hk hj).
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (summable_real_space hm) R^o
  *:%R summable_real_integral_map summable_real_integral_map_linear.
End Integral.
