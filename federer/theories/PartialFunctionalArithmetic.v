(** Federer (1969), 2.4.12, pp. 87–88: linearity of dual evaluations in the
    vector-integral construction. These supporting graph identities retain
    exact partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition PartialNormedArithmetic
  PartialExtendedArithmetic ExtendedRealPartial MeasureUpperIntegralScale MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_functional_add_graph]: supporting evaluation
    of f+g under a linear functional for Federer 2.4.12,
    pp. 87–88. Real evaluations always have a defined sum. *)
Lemma partial_functional_add_graph (R : realType) (X : Type) (V : lmodType R)
    (f g : partial_function X V) (a : {linear V -> R^o}) x z :
  partial_function_graph (partial_extended_function_add
    (partial_functional_evaluation f a) (partial_functional_evaluation g a)) x z <->
  partial_function_graph (partial_functional_evaluation (partial_vector_add f g) a) x z.
Proof.
rewrite partial_extended_function_add_graph; split.
- move=> [r [s [[u [hu heu]] [[v [hv hev]] hsum]]]].
  exists (u+v)%R; split.
  + apply/partial_vector_add_graph; exists u,v; by split=> //; split.
  + move: hsum; rewrite -heu -hev /extended_add /= -EFinD -linearD; by move=> [].
- move=> [w [/partial_vector_add_graph [u [v [hu [hv ->]]]] hw]].
  exists (a u)%:E,(a v)%:E; split; first by exists u; split.
  split; first by exists v; split.
  by rewrite /extended_add /= -EFinD -linearD hw.
Qed.

(** Source for [partial_functional_scale_graph]: supporting scalar
    homogeneity of the dual evaluation in Federer 2.4.12,
    pp. 87–88. The scalar may be zero because every value
    of the functional is finite. *)
Lemma partial_functional_scale_graph (R : realType) (X : Type) (V : lmodType R)
    (f : partial_function X V) (a : {linear V -> R^o}) (c : R) x z :
  partial_function_graph (partial_extended_function_scale c (partial_functional_evaluation f a)) x z <->
  partial_function_graph (partial_functional_evaluation (partial_vector_scale c f) a) x z.
Proof.
split.
- move=> [r [[u [hu her]] hez]].
  exists (c *: u)%R; split.
  + apply/partial_vector_scale_graph; exists u; by split.
  + by rewrite linearZ /= EFinM her.
- move=> [w [/partial_vector_scale_graph [u [hu ->]] hw]].
  exists (a u)%:E; split; first by exists u; split.
  by rewrite -EFinM -linearZ.
Qed.
