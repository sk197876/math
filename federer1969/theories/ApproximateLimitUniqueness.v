(** Federer (1969), 2.9.12, pp. 158–159: densities and approximate limits of
    functions on partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureDerivationContext MeasureSetDensity
  MeasureApproximateLimitUP ZeroDensityCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_approximate_limit_unique]: direct Hausdorff
    uniqueness assertion in Federer 2.9.12, p. 158, last paragraph Disjoint
    neighbourhoods have inverse-image complements covering X, contradicting
    their zero densities. *)
Theorem measure_approximate_limit_unique (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) x y z :
  is_measure_derivation_context phi V -> hausdorff_space Y ->
  is_measure_approximate_limit phi V f x y ->
  is_measure_approximate_limit phi V f x z -> y=z.
Proof.
move=> hc hY hy hz; apply/eqP; apply/negP=> hne.
rewrite open_hausdorff in hY.
have hyz : y!=z by apply/negP; exact hne.
have [[U W] [hyU hzW] [hU hW /eqP hdis]] := hY y z hyz.
have hyN : nbhs y U by rewrite openE in hU; apply: hU; by move: hyU; rewrite inE.
have hzN : nbhs z W by rewrite openE in hW; apply: hW; by move: hzW; rewrite inE.
have hcover : (~` partial_function_preimage f U) `|` (~` partial_function_preimage f W)=setT.
  apply/seteqP; split=> a; first by move=> _.
  move=> _.
  case: (pselect (partial_function_preimage f U a))=> hu; last by left.
  right.
  move=> hfW.
  have [v [hv hvW]] := hfW; have [u [hfu huU]] := hu.
  have he := partial_function_single_valued hfu hv.
  have hbad : (U `&` W) u by rewrite he in huU; rewrite he; split.
  by rewrite hdis in hbad.
exact: (@zero_density_cover_impossible R X phi V
  (~` partial_function_preimage f U) (~` partial_function_preimage f W) x hc hcover (hy U hyN) (hz W hzN)).
Qed.

(** Source for [measure_approximate_limit]: direct partial approximate-limit
    function denoted in Federer 2.9.12, p. 158, last display *)
Definition measure_approximate_limit (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) (hc : is_measure_derivation_context phi V)
    (hY : hausdorff_space Y) : partial_function X Y.
Proof.
refine (@Build_partial_function X Y (is_measure_approximate_limit phi V f) _).
move=> x y z hy hz; exact: measure_approximate_limit_unique hc hY hy hz.
Defined.

(** Source for [measure_approximate_limit_graph]: defining
    neighbourhood criterion of Federer 2.9.12, p. 158,
    exposed without selecting a value outside the limit domain. *)
Lemma measure_approximate_limit_graph (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) (hc : is_measure_derivation_context phi V)
    (hY : hausdorff_space Y) x y :
  partial_function_graph (measure_approximate_limit f hc hY) x y <->
    is_measure_approximate_limit phi V f x y.
Proof. by []. Qed.
