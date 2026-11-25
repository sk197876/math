(** Federer (1969), 4.1.19, p. 377: the full L1
    field space used to extend a functional from Omega_m.
    Membership is the original finite total-domain L1
    condition of 2.4.12, pp. 86–87. Raw representatives
    are retained, so no positive-definiteness is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient
  SubspaceCarrier MeasureUP TotalMeasurableFunctionSpace MeasureLpNormTotal
  ExtendedSeminormUP ExtendedSeminormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.

Section SummableFieldUP.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation A := (@total_measurable_normed_subspace R X V N hN mu hm).
Local Notation AT := (subspace_space A).
Local Notation L := (@total_measurable_lp_norm R X V N hN mu hm 1).

(** Source for [summable_field_member]: the finite L1
    locus of the original total measurable field space,
    2.4.12, pp. 86–87, used in the functional
    extension of Federer 4.1.19, p. 377. *)
Definition summable_field_member (f : AT) : Prop := (L f < +oo)%E.

(** Source for [summable_field_subspace]: the finite
    seminorm locus is a vector subspace, 2.4.12,
    p. 86, supporting the L1 extension in
    Federer 4.1.19, p. 377. No compact support
    or quotient by almost equality is required. *)
Definition summable_field_subspace : subspace AT.
Proof.
pose hL := @total_measurable_lp_norm_seminorm R X V N hN mu hm 1 (lexx 1).
refine (@Subspace R AT summable_field_member _ _ _).
- exact: (@extended_seminorm_finite_zero R AT L hL).
- move=> f g; exact: (@extended_seminorm_finite_add R AT L hL f g).
- move=> c f; exact: (@extended_seminorm_finite_scale R AT L hL c f).
Defined.
End SummableFieldUP.
