(** Federer (1969), 2.6.6, p. 120: finite products are obtained by the
    method of 2.6.4. This file integrates one coordinate while leaving the
    others as parameters. It supplies a construction ingredient, not an
    additional axiom about infinite products. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp mathcomp_extra classical_sets reals topology.
From Federer Require Import RealMetricBackground ProductCoordinateReplacement CompactSupportFunctionUP
  CompactProductSections CompactSectionFunctional CompactUniformNorm SubtypeCompactHausdorff
  DaniellIntegralUP DaniellSpaceCompactness FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_daniell_operator]: supporting single-coordinate
    integration for the finite marginals in Federer 2.6.6, p. 120,
    constructed by the successive-section method of 2.6.4, p. 119. *)
Definition coordinate_daniell_operator (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (i : I) (f : prod_topology Y -> R) (x : prod_topology Y) :=
  A i (fun u=>f (dfwith x i u)).

(** Source for [coordinate_replaced_function_compact_support]: supporting
    applicability of the compact-section theorem of 2.6.4, p. 119,
    to a factor of the product in 2.6.6, p. 120. *)
Lemma coordinate_replaced_function_compact_support (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (i : I) (f : prod_topology Y -> R) :
  compact (@setT (Y i)) -> compact (@setT (prod_topology Y)) ->
  compactly_supported_continuous_functions f ->
  compactly_supported_continuous_functions (fun p : Y i * prod_topology Y=>f (product_coordinate_replace p)).
Proof.
move=> hi hX hf; split.
- move=> p; exact: continuous_comp (@product_coordinate_replace_continuous I Y i p) (hf.1 _).
- have hc := compact_setX hi hX.
  have he : (@setT (Y i) `*` @setT (prod_topology Y)) = [set: Y i * prod_topology Y].
    by apply/seteqP; split=> p hp; [|split].
  rewrite he in hc; exact: subclosed_compact (@real_function_support_closed R _ _) hc (@subsetT _ _).
Qed.

(** Source for [coordinate_daniell_operator_preserves_continuity]: one
    coordinate integration preserves K(X), supporting the finite-product
    construction in Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_operator_preserves_continuity (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) (i : I) :
  hausdorff_space (Y i) -> compact (@setT (Y i)) -> compact (@setT (prod_topology Y)) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i) ->
  forall f, compactly_supported_continuous_functions f ->
    compactly_supported_continuous_functions (coordinate_daniell_operator A i f).
Proof.
move=> hi hci hcX hA f hf; split.
- exact: (@compact_section_functional_continuous R (Y i) (prod_topology Y) (A i) _ hi
    (compact_space_locally_compact hci) hA (coordinate_replaced_function_compact_support hci hcX hf)).
- exact: subclosed_compact (@real_function_support_closed R _ _) hcX (@subsetT _ _).
Qed.

(** Source for [coordinate_daniell_section_membership]: every section
    used in the coordinate integrations is in K(X_i), supporting
    Federer 2.6.6, p. 120, via 2.6.4, p. 119. *)
Lemma coordinate_daniell_section_membership (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (i : I) (f : prod_topology Y -> R) (x : prod_topology Y) :
  compact (@setT (Y i)) -> compactly_supported_continuous_functions f ->
  compactly_supported_continuous_functions (fun u=>f (dfwith x i u)).
Proof.
move=> hc hf; split.
- move=> u; exact: continuous_comp (@product_coordinate_section_continuous I Y i x u) (hf.1 _).
- exact: subclosed_compact (@real_function_support_closed R _ _) hc (@subsetT _ _).
Qed.

(** Source for [coordinate_daniell_operator_add]: additivity of a
    coordinate integration, supporting linearity of the finite products
    in Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_operator_add (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) (i : I) :
  compact (@setT (Y i)) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i) ->
  forall f g, compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
  coordinate_daniell_operator A i (fun x=>f x+g x)=
    (fun x=>coordinate_daniell_operator A i f x+coordinate_daniell_operator A i g x).
Proof.
move=> hc hA f g hf hg; apply: funext=> x.
exact (@daniell_integral_add R (Y i) _ (A i) hA _ _
  (@coordinate_daniell_section_membership R I Y i f x hc hf)
  (@coordinate_daniell_section_membership R I Y i g x hc hg)).
Qed.

(** Source for [coordinate_daniell_operator_scale]: real homogeneity
    of coordinate integration, supporting Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_operator_scale (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) (i : I) :
  compact (@setT (Y i)) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i) ->
  forall c f, compactly_supported_continuous_functions f ->
  coordinate_daniell_operator A i (fun x=>c*f x)=
    (fun x=>c*coordinate_daniell_operator A i f x).
Proof.
move=> hc hA c f hf; apply: funext=> x.
exact ((@daniell_compact_support_linear R (Y i) (A i) hA).2 c _
  (@coordinate_daniell_section_membership R I Y i f x hc hf)).
Qed.
