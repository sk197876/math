(** Federer (1969), 2.8.2, pp. 142–143: the local countable contraction
    hypothesis and the finite selections made in successively smaller open
    sets. These records express laws of selections and exhaustions; they
    introduce no project axioms or selected implementations. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_contraction_cover_selection]: the local
    subfamily in the hypothesis and finite-selection step of
    Federer 2.8.2, pp. 142–143. Countability or finiteness
    is stated separately, allowing the same four geometric and
    measure laws to describe both families. *)
Record is_contraction_cover_selection (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A W : set X)
    (q : R) (G : set (set X)) : Prop := {
  (** Source for [contraction_selection_members]: the selected
      family is contained in F, Federer 2.8.2, p. 142. *)
  contraction_selection_members : G `<=` F;
  (** Source for [contraction_selection_disjoint]: the selected
      family is disjointed, Federer 2.8.2, p. 142. *)
  contraction_selection_disjoint : set_family_disjoint G;
  (** Source for [contraction_selection_within]: union G lies
      in the open W, Federer 2.8.2, pp. 142–143. *)
  contraction_selection_within : (\bigcup_(B in G) B) `<=` W;
  (** Source for [contraction_selection_bound]: the uncovered
      measure is at most q times mu(W intersect A), Federer
      2.8.2, p. 142. The initial family uses q=sigma(A),
      the finite family uses q=sqrt(sigma(A)). *)
  contraction_selection_bound :
    mu ((W `&` A) `\` \bigcup_(B in G) B) <= q%:E * mu (W `&` A)
}.

(** Source for [has_local_cover_contraction]: the hypothesis
    of Federer 2.8.2, p. 142, for one target A and
    one prescribed scalar sigma. Its bounds 0<sigma<1
    are separate hypotheses, as in the printed theorem. *)
Definition has_local_cover_contraction (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X)) (A : set X)
    (sigma : R) : Prop :=
  forall W, open W -> exists H,
    countable H /\ is_contraction_cover_selection mu F A W sigma H.

(** Source for [is_cover_contraction_exhaustion]: the open
    sets W_j and finite families G_j of Federer 2.8.2,
    pp. 142–143. We omit the initial empty family corrected
    by the erratum p. 3, book p. 142 line 33: formal W_0
    is the printed W_1=V, and formal G_0 is the printed G_1.
    Thus natural index zero is the first actual selection.
    The contraction factors q_n are supplied abstractly. *)
Record is_cover_contraction_exhaustion (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F : set (set X))
    (A : nat -> set X) (q : nat -> R) (V : set X)
    (W : nat -> set X) (G : nat -> set (set X)) : Prop := {
  (** Source for [contraction_exhaustion_initial]: the initial
      open set is V, Federer 2.8.2, p. 142, with the
      empty preliminary step suppressed as explained above. *)
  contraction_exhaustion_initial : W 0%N = V;
  (** Source for [contraction_exhaustion_open]: all remainders
      W_j are open, Federer 2.8.2, pp. 142–143. *)
  contraction_exhaustion_open : forall n, open (W n);
  (** Source for [contraction_exhaustion_finite]: each selected
      family G_j is finite, Federer 2.8.2, pp. 142–143. *)
  contraction_exhaustion_finite : forall n, finite_set (G n);
  (** Source for [contraction_exhaustion_selection]: each G_j
      is eligible, disjointed, contained in W_j, and gives the
      required contraction, Federer 2.8.2, pp. 142–143. *)
  contraction_exhaustion_selection : forall n,
    is_contraction_cover_selection mu F (A n) (W n) (q n) (G n);
  (** Source for [contraction_exhaustion_next]: remove the
      finite closed selected union to obtain the next remainder,
      Federer 2.8.2, pp. 142–143. *)
  contraction_exhaustion_next : forall n,
    W n.+1 = W n `\` \bigcup_(B in G n) B
}.
