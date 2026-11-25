(** Federer (1969), Lemma 2.8.13, pp. 149–150: a bounded positive-radius
    family has a controlled subset covering all original centers. The
    auxiliary class consists of controlled subsets with the printed
    covered-or-separated alternative. The strict book comparisons are
    retained here. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import DirectionalLimitationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_controlled_center_selection]: the conclusion
    of Federer 2.8.13, pp. 149–150: a controlled subset
    whose balls contain every original center. Here Q is the
    eligible set and P the selected subset. *)
Record is_controlled_center_selection (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X*R)) : Prop := {
  (** Source for [controlled_center_selection_members]: the
      selected parameters belong to the original family,
      Federer 2.8.13, p. 149. *)
  controlled_center_selection_members : P `<=` Q;
  (** Source for [controlled_center_selection_controlled]: the
      selected subset is tau-controlled, Federer 2.8.13, p. 149. *)
  controlled_center_selection_controlled : is_controlled_ball_family tau P;
  (** Source for [controlled_center_selection_covers]: each
      original center is in a selected closed ball, Federer
      2.8.13, p. 149. *)
  controlled_center_selection_covers : forall q, Q q -> exists p,
    P p /\ mdist p.1 q.1 <= p.2
}.

(** Source for [is_center_saturated_family]: the class D
    in the proof of Federer 2.8.13, p. 149. Each original
    center is either covered or separated from every selected
    center by more than the selected radius, which is strictly
    larger than the original radius divided by tau. *)
Record is_center_saturated_family (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X*R)) : Prop := {
  (** Source for [center_saturated_members]: membership in
      the original parameter family, Federer 2.8.13, p. 149. *)
  center_saturated_members : P `<=` Q;
  (** Source for [center_saturated_controlled]: controlledness
      in the auxiliary class, Federer 2.8.13, p. 149. *)
  center_saturated_controlled : is_controlled_ball_family tau P;
  (** Source for [center_saturated_alternative]: the printed alternative
    following the definition of the class, Federer 2.8.13, p. 149 *)
  center_saturated_alternative : forall q, Q q ->
    (exists p, P p /\ mdist p.1 q.1 <= p.2) \/
    (forall p, P p -> p.2 < mdist p.1 q.1 /\ q.2/tau < p.2)
}.
