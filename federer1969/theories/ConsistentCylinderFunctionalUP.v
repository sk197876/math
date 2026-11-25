(** Federer (1969), 2.6.6, p. 120: compatibility of the finite marginals and
    the induced linear functional gamma on L. The family is specified by
    linearity, monotonicity, normalization, and consistency under enlarging
    the finite coordinate set. These laws must be proved for the finite
    products; they are not project axioms. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import FunctionLatticeUP CompactSupportFunctionUP ProductCylinderLattice FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [continuous_coordinate_functions]: L_a in Federer
    2.6.6, p. 120, expressed by dependence on the coordinates a. *)
Definition continuous_coordinate_functions (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (F : {fset I}) : set (prod_topology Y -> R) :=
  [set f | compactly_supported_continuous_functions f /\ is_coordinate_determined F f].

(** Source for [is_consistent_cylinder_functional_family]: the
    finite-marginal laws used to define gamma in Federer 2.6.6,
    p. 120. This is an abstract specification, with existence for
    actual finite products to be established separately. *)
Record is_consistent_cylinder_functional_family (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : {fset I} -> (prod_topology Y -> R) -> R) : Prop := {
  (** Source for [cylinder_family_linear]: linearity of the finite
      product integrals in Federer 2.6.6, p. 120. *)
  cylinder_family_linear : forall F, is_linear_functional_on_functions (continuous_coordinate_functions F) (A F);
  (** Source for [cylinder_family_monotone]: monotonicity of each finite
      product integral, Federer 2.6.6, p. 120. *)
  cylinder_family_monotone : forall F f g, continuous_coordinate_functions F f ->
    continuous_coordinate_functions F g -> function_le f g -> A F f<=A F g;
  (** Source for [cylinder_family_one]: total mass one for every finite
      product, including the empty product, Federer 2.6.6, p. 120. *)
  cylinder_family_one : forall F, A F (fun _=>1) = 1;
  (** Source for [cylinder_family_consistent]: the equality of the
      pushed-forward finite marginals, Federer 2.6.6, p. 120. *)
  cylinder_family_consistent : forall F G, {subset F <= G} ->
    forall f, continuous_coordinate_functions F f -> A G f=A F f
}.

(** Source for [is_glued_cylinder_functional]: defining agreement of
    gamma with all finite marginals in Federer 2.6.6, p. 120. *)
Definition is_glued_cylinder_functional (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : {fset I} -> (prod_topology Y -> R) -> R)
    (B : (prod_topology Y -> R) -> R) :=
  forall F f, continuous_coordinate_functions F f -> B f=A F f.

(** Source for [glued_cylinder_functional_unique]: uniqueness of gamma
    on L in Federer 2.6.6, p. 120; ambient values outside L
    are not asserted to be unique. *)
Lemma glued_cylinder_functional_unique (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : {fset I} -> (prod_topology Y -> R) -> R)
    (B C : (prod_topology Y -> R) -> R) :
  is_glued_cylinder_functional A B -> is_glued_cylinder_functional A C ->
  forall f, continuous_product_cylinders f -> B f=C f.
Proof.
move=> hB hC f [hf [F hF]].
by rewrite (hB F f (conj hf hF)) (hC F f (conj hf hF)).
Qed.
