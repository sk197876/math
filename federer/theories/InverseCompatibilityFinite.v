(** Federer (1969), 2.6.6, pp. 120–121, inverse-limit paragraph: finite
    compatibility constraints can be realized by projecting a point from a
    common upper index. No bonding map is assumed surjective. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot finmap boolp classical_sets topology.
From Federer Require Import CompactInverseSystemUP DirectedFiniteUpperBounds
  ContinuousEqualizerClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [inverse_compatibility_constraint]: one compatibility
    equation for the inverse-limit paragraph of Federer 2.6.6,
    pp. 120–121. Unordered pairs impose no condition. *)
Definition inverse_compatibility_constraint (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i) (ij : I * I) :=
  [set u : prod_topology Y | le ij.1 ij.2 -> b ij.1 ij.2 (u ij.2)=u ij.1].

(** Source for [inverse_compatibility_constraint_closed]: closed
    compatibility equations, supporting Federer 2.6.6, pp. 120–121. *)
Lemma inverse_compatibility_constraint_closed (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i) :
  is_compact_inverse_system le b -> forall ij, closed (inverse_compatibility_constraint le b ij).
Proof.
move=> hs [i j]; case: (pselect (le i j))=> hij.
- have he : inverse_compatibility_constraint le b (i,j)=
      [set u : prod_topology Y | b i j (u j)=u i].
    apply/seteqP; split=> u hu; [exact: hu hij|by move=> _].
  rewrite he; apply: (@continuous_equalizer_closed (prod_topology Y) (Y i) (fun u=>b i j (u j))
    (fun u=>u i) (@compact_inverse_system_hausdorff I le Y b hs i)).
  + move=> u; exact (continuous_comp (@proj_continuous I Y j u)
      (@compact_inverse_system_continuous I le Y b hs i j hij (u j))).
  + exact: proj_continuous.
- have -> : inverse_compatibility_constraint le b (i,j) = setT.
    apply/seteqP; split=> u hu // h; exact: hij h.
  exact: closedT.
Qed.

(** Source for [inverse_finite_constraints_upper]: a common upper
    index for the endpoints of finitely many compatibility equations,
    supporting Federer 2.6.6, pp. 120–121. *)
Lemma inverse_finite_constraints_upper (I : choiceType) (le : I -> I -> Prop)
    (hd : is_directed_preorder le) (i0 : I) (F : {fset I * I}) :
  exists k, le i0 k /\ forall ij, ij \in F -> le ij.1 k /\ le ij.2 k.
Proof.
have [k [h0 hk]] := directed_list_upper_bound hd i0
  ([seq ij.1 | ij <- F] ++ [seq ij.2 | ij <- F]).
exists k; split=> // ij hij; split; apply: hk; rewrite mem_cat; apply/orP.
- left; by apply/mapP; exists ij.
- right; by apply/mapP; exists ij.
Qed.

(** Source for [inverse_upper_coordinate_family]: supporting partial
    realization of an inverse system below an upper index, Federer
    2.6.6, pp. 120–121. Other coordinates use a supplied point. *)
Definition inverse_upper_coordinate_family (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (u0 : prod_topology Y) k (y : Y k) : prod_topology Y :=
  fun i=>if pselect (le i k) then b i k y else u0 i.

(** Source for [inverse_upper_coordinate_family_evaluation]:
    coordinate evaluation below the upper index, supporting the
    finite intersection proof in Federer 2.6.6, pp. 120–121. *)
Lemma inverse_upper_coordinate_family_evaluation (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (u0 : prod_topology Y) k (y : Y k) i : le i k ->
  inverse_upper_coordinate_family le b u0 y i=b i k y.
Proof. move=> hi; rewrite /inverse_upper_coordinate_family; by case: pselect. Qed.

(** Source for [inverse_upper_family_compatible_pair]: the
    bonding-map composition law solves each finite compatibility
    equation, supporting Federer 2.6.6, pp. 120–121. *)
Lemma inverse_upper_family_compatible_pair (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (hs : is_compact_inverse_system le b) (u0 : prod_topology Y)
    k (y : Y k) i j : le i k -> le j k ->
  inverse_compatibility_constraint le b (i,j) (inverse_upper_coordinate_family le b u0 y).
Proof.
move=> hik hjk hij; rewrite !inverse_upper_coordinate_family_evaluation //.
exact (@compact_inverse_system_composition I le Y b hs i j k hij hjk y).
Qed.
