(** Decomposition laws in Federer (1969), Corollary 2.8.12, pp. 148–149: the
    associated closed-ball family is the union of 2 zeta+1 disjointed
    subfamilies. Parameters are kept until the last passage to balls. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import CountablyClosedFamilyUP ControlledBallParameters
  RadiusCoverSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [associated_closed_ball_family]: the family
    {B(a,r):(a,r) in Q} in Federer 2.8.12, p. 148,
    expressed as an image of the given parameters. *)
Definition associated_closed_ball_family (R : realType) (X : metricType R)
    (Q : set (X*R)) := (@parameter_closed_ball R X) @` Q.

(** Source for [is_radius_parameter_decomposition]: the finite
    collection of separated subsets R_j covering Q in Federer
    2.8.12, p. 149. This intermediate specification is independent
    of the repeated-selection construction. *)
Record is_radius_parameter_decomposition (R : realType) (X : metricType R)
    (Q : set (X*R)) (N : nat) (C : 'I_N -> set (X*R)) : Prop := {
  (** Source for [parameter_decomposition_members]: each selected
      R_j is a subset of Q, Federer 2.8.12, p. 149. *)
  parameter_decomposition_members : forall i, C i `<=` Q;
  (** Source for [parameter_decomposition_separated]: condition
      (1) at each selected stage, Federer 2.8.12, p. 149. *)
  parameter_decomposition_separated : forall i, radius_parameters_separated (C i);
  (** Source for [parameter_decomposition_covers]: the final
      remainder is empty, so the R_j cover Q, Federer 2.8.12,
      p. 149. *)
  parameter_decomposition_covers : Q = \bigcup_(i in @setT 'I_N) C i
}.

(** Source for [is_disjoint_ball_family_decomposition]: the
    conclusion of Federer 2.8.12, p. 148: F is the union
    of N disjointed subfamilies. Empty color classes are allowed;
    no finite or countable bound on each class is imposed. *)
Record is_disjoint_ball_family_decomposition (X : choiceType)
    (F : set (set X)) (N : nat) (G : 'I_N -> set (set X)) : Prop := {
  (** Source for [ball_decomposition_members]: the G_j are
      subfamilies of F, Federer 2.8.12, p. 148. *)
  ball_decomposition_members : forall i, G i `<=` F;
  (** Source for [ball_decomposition_disjoint]: each G_j is
      disjointed, Federer 2.8.12, pp. 148–149. *)
  ball_decomposition_disjoint : forall i, set_family_disjoint (G i);
  (** Source for [ball_decomposition_covers]: F is the union
      of the G_j, Federer 2.8.12, p. 148. *)
  ball_decomposition_covers : F = \bigcup_(i in @setT 'I_N) G i
}.
