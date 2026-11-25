(** Federer (1969), 3.1.20, pp. 232–233: the eventual domain and
    local stabilization laws in the limit of the patched maps. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormRegularity LocalRetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [eventual_open_domain]: A is the union over j of
    the intersections of W_i for i>=j, the displayed domain in
    Federer 3.1.20, p. 232. Openness is a theorem, not part of
    this set definition. *)
Definition eventual_open_domain (X:Type) (W:nat->set X) : set X :=
  fun x=>exists d, forall i, (d<=i)%N -> W i x.

(** Source for [stationary_map_graph]: the eventual value of f_i,
    supporting the limiting map in Federer 3.1.20, p. 233. This
    graph records actual eventual membership as well as exact values. *)
Definition stationary_map_graph (X Y:Type) (W:nat->set X) (f:nat->X->Y) x y :=
  exists d, forall i, (d<=i)%N -> W i x /\ f i x=y.

(** Source for [stationary_map_graph_unique]: exact stabilization
    makes the limiting value unique, supporting the last paragraph
    of the forward proof of Federer 3.1.20, p. 233. *)
Lemma stationary_map_graph_unique (X Y:Type) (W:nat->set X) (f:nat->X->Y) x y z :
  stationary_map_graph W f x y -> stationary_map_graph W f x z -> y=z.
Proof.
move=>[d hd] [e he].
have hd':=(hd (maxn d e) (leq_maxl d e)).2.
have he':=(he (maxn d e) (leq_maxr d e)).2.
exact (eq_trans (esym hd') he').
Qed.
