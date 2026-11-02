(** Federer (1969), Theorem 2.8.14, p. 150: cover the directionally limited
    target by finitely many disjointed subfamilies of given small closed
    balls. Centers and positive radii are retained together: a ball may have
    several metric representations. We use Federer's strict r<mu. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import MetricClosedBalls CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_small_closed_ball_family]: F consists of
    closed balls with positive radii less than mu in Federer
    2.8.14, p. 150, following the parameter convention of
    2.8.9, p. 146. Representability does not assert uniqueness
    of the center or radius of a ball. *)
Definition is_small_closed_ball_family (R : realType) (X : metricType R)
    (mu : R) (F : set (set X)) :=
  forall B, F B -> exists a r, 0 < r < mu /\ B = metric_closed_ball a r.

(** Source for [has_small_centered_balls]: each a in A is the center of an
    eligible small ball in Federer 2.8.14, p. 150 The radius bound applies
    to the same centered representation as the witness, retaining the pairs
    used in Federer's proof. *)
Definition has_small_centered_balls (R : realType) (X : metricType R)
    (mu : R) (F : set (set X)) (A : set X) :=
  forall a, A a -> exists r, 0 < r < mu /\ F (metric_closed_ball a r).

(** Source for [is_finite_disjoint_ball_cover]: the conclusion
    of Federer 2.8.14, p. 150: A is contained in the union
    of N disjointed subfamilies of F. The predicates on the
    eligible family are separate; the cover laws do not encode
    a particular construction. *)
Record is_finite_disjoint_ball_cover (X : choiceType) (F : set (set X))
    (A : set X) (N : nat) (G : 'I_N -> set (set X)) : Prop := {
  (** Source for [finite_ball_cover_members]: each color class
      belongs to F, Federer 2.8.14, p. 150. *)
  finite_ball_cover_members : forall i, G i `<=` F;
  (** Source for [finite_ball_cover_disjoint]: each color class
      is disjointed, Federer 2.8.14, p. 150. *)
  finite_ball_cover_disjoint : forall i, set_family_disjoint (G i);
  (** Source for [finite_ball_cover_covers]: A lies in the union
      of all selected balls, Federer 2.8.14, p. 150. *)
  finite_ball_cover_covers : A `<=` \bigcup_(i in @setT 'I_N) \bigcup_(B in G i) B
}.
