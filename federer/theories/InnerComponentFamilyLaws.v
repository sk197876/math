(** Federer (1969), 4.1.4, pp. 348–349: the actual
    components C_e are connected and open, lie in A and
    grow as e decreases. These properties follow from the
    original component relation and the existing component
    theorems; no new component construction is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormOpenComponents InnerParallelFamilyUP
  InnerParallelFamilyLaws InnerParallelFamilyOpen InnerComponentFamilyUP ComponentInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section InnerComponentFamilyLaws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation T := (real_norm_metric_space hNX).
Variable A:set X.
Variable O:R->set X.
Hypothesis hO:is_inner_parallel_family NX A O.
Variable a:X.
Variable C:R->set X.
Hypothesis hC:@is_inner_component_family R T O a C.

(** Source for [inner_component_connected]: C_e is an actual
    connected component, Federer 4.1.4, pp. 348–349. *)
Lemma inner_component_connected e:0<e ->@connected T (C e).
Proof. move=>he; rewrite (@hC e he); exact:component_connected. Qed.

(** Source for [inner_component_open]: C_e is open in the
    original source topology, used in Federer 4.1.4, p. 349. *)
Lemma inner_component_open e:0<e ->@open T (C e).
Proof.
move=>he; rewrite (@hC e he).
apply:(@norm_open_components_open R X NX hNX (O e) a).
exact:(@inner_parallel_family_open R X NX hNX A O hO e he).
Qed.

(** Source for [inner_component_inside]: the original C_e
    lies inside A, Federer 4.1.4, pp. 348–349. *)
Lemma inner_component_inside e:0<e ->C e `<=` A.
Proof.
move=>he x hx; rewrite (@hC e he) in hx.
apply:(@inner_parallel_inside R X NX A O hO e he x).
exact:(@connected_component_sub T (O e) a x hx).
Qed.

(** Source for [inner_component_reverse_monotone]: decreasing
    epsilon enlarges the actual component of the same centre,
    supporting the limiting argument of Federer 4.1.4, p. 349. *)
Lemma inner_component_reverse_monotone e d:
  0<e ->0<d ->e<=d ->C d `<=` C e.
Proof.
move=>he hd hed; rewrite (@hC d hd) (@hC e he).
apply:(@component_inclusion T (O d) (O e) a).
exact:(@inner_parallel_reverse_monotone R X NX A O hO e d he hd hed).
Qed.
End InnerComponentFamilyLaws.
