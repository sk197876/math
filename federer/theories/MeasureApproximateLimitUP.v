(** Federer (1969), 2.9.12, pp. 158–159: densities and approximate limits of
    functions on partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureSetDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_approximate_limit]: direct definition in Federer
    2.9.12, p. 158, last paragraph Every neighbourhood has an inverse image
    whose complement has density zero. Points outside the actual domain
    belong to that complement. *)
Definition is_measure_approximate_limit (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) (x : X) (y : Y) :=
  forall W : set Y, nbhs y W ->
    partial_function_graph (measure_set_density phi V (~` partial_function_preimage f W)) x 0.

(** Source for [is_measure_approximately_continuous_at]: direct definition
    in Federer 2.9.12, p. 159, first paragraph The point has an actual
    function value and that value is an approximate limit. This predicate
    also makes sense before Hausdorff uniqueness. *)
Definition is_measure_approximately_continuous_at (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) x :=
  exists y, partial_function_graph f x y /\ is_measure_approximate_limit phi V f x y.

(** Source for [approximate_limit_domain_density]: supporting partial-domain
    consequence of Federer 2.9.12, pp. 158–159 Every approximate limit
    requires density zero of the missing domain. *)
Lemma approximate_limit_domain_density (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) x y :
  is_measure_approximate_limit phi V f x y ->
  partial_function_graph (measure_set_density phi V (~` partial_function_domain f)) x 0.
Proof.
move=> hl; have hN : nbhs y setT := @filterT Y (nbhs y) (nbhs_filter y).
have h := hl setT hN.
have he : partial_function_preimage f setT=partial_function_domain f.
  apply/seteqP; split=> z; first by move=> [v [hv _]]; exists v.
  by move=> [v hv]; exists v.
by rewrite he in h.
Qed.
