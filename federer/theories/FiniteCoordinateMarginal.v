(** Federer (1969), 2.6.6, p. 120: the finite product mu_a on K(X_a),
    identified with its functional on L_a through the injective pullback
    p_a. The definition uses an abstract consistent family, not its private
    coordinate fold. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP FiniteCoordinateProjection FiniteCoordinatePullback
  ConsistentCylinderFunctionalUP MonotoneCompactSupportFunctional SubtypeCompactHausdorff
  FunctionLatticeUP FunctionLatticeSeminormUP MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_coordinate_marginal]: mu_a on K(X_a)
    in Federer 2.6.6, p. 120, recovered by the pullback map. *)
Definition finite_coordinate_marginal (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (C : {fset I} -> (prod_topology Y -> R) -> R)
    (F : {fset I}) (g : finite_coordinate_space Y F -> R) :=
  C F (g \o finite_coordinate_projection (F:=F)).
Arguments finite_coordinate_marginal {R I Y} C F g.

(** Source for [finite_coordinate_marginal_is_daniell]: the finite
    marginal is a normalized monotone Daniell integral on K(X_a),
    as asserted in Federer 2.6.6, p. 120. *)
Theorem finite_coordinate_marginal_is_daniell (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (x0 : prod_topology Y)
    (C : {fset I} -> (prod_topology Y -> R) -> R) (F : {fset I}) :
  (forall i, hausdorff_space (Y i)) -> compact (@setT (prod_topology Y)) ->
  is_consistent_cylinder_functional_family C ->
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R (finite_coordinate_space Y F))
    (finite_coordinate_marginal C F) /\ finite_coordinate_marginal C F (fun _=>1) = 1.
Proof.
move=> hh hc hC; split; last exact: cylinder_family_one hC F.
have hFh : hausdorff_space (finite_coordinate_space Y F).
  exact: hausdorff_product (fun i=>hh (val i)).
have hFc := @finite_coordinate_product_compact I Y x0 F hc.
apply: (@monotone_compact_support_linear_daniell R (finite_coordinate_space Y F)
  (finite_coordinate_marginal C F) hFh (compact_space_locally_compact hFc)).
- split.
  + move=> f g hf hg; exact: (cylinder_family_linear hC F).1 _ _
      (finite_coordinate_pullback_membership hc hf) (finite_coordinate_pullback_membership hc hg).
  + move=> c f hf; exact: (cylinder_family_linear hC F).2 c _ (finite_coordinate_pullback_membership hc hf).
- move=> f g hf hg hfg; apply: (@cylinder_family_monotone R I Y C hC F _ _
    (finite_coordinate_pullback_membership hc hf) (finite_coordinate_pullback_membership hc hg))=> x.
  exact: hfg.
Qed.
