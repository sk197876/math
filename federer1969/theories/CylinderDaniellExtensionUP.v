(** Federer (1969), 2.6.6, p. 120: the normalized monotone Daniell extension
    is characterized by all its finite marginals. This interface separates
    the marginal specification from the existence construction. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP ConsistentCylinderFunctionalUP MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_cylinder_daniell_extension]: the concluding
    characterization by p_a pushforwards in Federer 2.6.6, p. 120,
    expressed on the corresponding finite-coordinate pullbacks. *)
Definition is_cylinder_daniell_extension (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (C : {fset I} -> (prod_topology Y -> R) -> R)
    (B : (prod_topology Y -> R) -> R) :=
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R (prod_topology Y)) B /\
  B (fun _=>1) = 1 /\ is_glued_cylinder_functional C B.
