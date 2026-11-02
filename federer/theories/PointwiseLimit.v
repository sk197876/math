(** Federer (1969), 2.2.15, p. 70: pointwise limits of sequences of maps.
    This supporting predicate uses convergence in the target topology; it
    makes sense for arbitrary topological targets, although Federer's Baire
    classes below use metric targets. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_pointwise_limit]: supporting convergence
    predicate for the displayed formula in Federer 2.2.15,
    p. 70. Each source point has its own convergent
    target sequence; no uniform convergence is required. *)
Definition is_pointwise_limit (X : Type) (Y : topologicalType)
    (f : nat -> X -> Y) (g : X -> Y) : Prop :=
  forall x, (fun n => f n x) @ \oo --> g x.

(** Source for [pointwise_limit_continuous_postcomposition]: supporting
    passage through a continuous target map for the Baire-function
    algebra in Federer 2.2.15, pp. 70–71. This
    is a general-topology continuity argument, not a separate
    assertion about Baire ranks or uniform convergence. *)
Lemma pointwise_limit_continuous_postcomposition (X : Type) (Y Z : topologicalType)
    (f : nat -> X -> Y) (g : X -> Y) (h : Y -> Z) :
  is_pointwise_limit f g -> continuous h ->
  is_pointwise_limit (fun n => h \o f n) (h \o g).
Proof.
move=> hlim hh x V hV; exact: (hlim x _ (hh (g x) _ hV)).
Qed.

(** Source for [pointwise_limit_constant]: supporting stationary
    sequence in the Baire-class arguments of Federer 2.2.15,
    pp. 70–71. A constant sequence converges at each point. *)
Lemma pointwise_limit_constant (X : Type) (Y : topologicalType) (f : X -> Y) :
  is_pointwise_limit (fun _ : nat => f) f.
Proof. move=> x; exact: cvg_cst. Qed.

(** Source for [pointwise_limit_pair]: supporting product
    convergence for the Baire-function algebra in Federer 2.2.15,
    pp. 70–71. Coordinatewise convergence into a binary
    product is exactly convergence in the Cartesian product topology. *)
Lemma pointwise_limit_pair (X : Type) (Y Z : topologicalType)
    (f : nat -> X -> Y) (g : nat -> X -> Z) (a : X -> Y) (b : X -> Z) :
  is_pointwise_limit f a -> is_pointwise_limit g b ->
  is_pointwise_limit (fun n x => (f n x,g n x)) (fun x => (a x,b x)).
Proof. move=> hf hg x; exact: cvg_pair (hf x) (hg x). Qed.
