(** Federer (1969), 2.2.10(2), p. 67, last displayed inclusion: a point in
    every closure f(C intersect E(prefix)) is itself f(x) for the unique
    closed-branch point x. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import CompleteMetricUP ClosedShrinkingIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [shrinking_closed_image_limit]: supporting final inclusion
    for Federer 2.2.10(2), p. 67. A common closure point of the images of
    nested shrinking closed sets equals the image of their common point.
    Nonemptiness follows from the closure-point hypothesis. *)
Lemma shrinking_closed_image_limit (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (F : nat -> set T) y :
  is_complete_metric_space T -> hausdorff_space Y -> continuous f ->
  (forall n, closed (F n)) ->
  (forall n m, (n <= m)%N -> F m `<=` F n) ->
  (forall e : R, 0 < e -> exists n, forall u v, F n u -> F n v -> mdist u v < e) ->
  (forall n, closure (f @` F n) y) ->
  exists x, (forall n, F n x) /\ f x = y.
Proof.
move=> hT hY hf hclosed hnested hsmall hy.
have hne n : F n !=set0.
  have [z [[x hx _] _]] := hy n setT (@filterT _ (nbhs y) (nbhs_filter y)).
  by exists x.
have [x hx] := closed_shrinking_metric_intersection hT hne hclosed hnested hsmall.
exists x; split=> //; apply: contrapT=> hneq.
have hne' : f x != y by apply/negP=> /eqP he; exact: hneq he.
rewrite open_hausdorff in hY.
have [[U V] [hfx hyV] [hU hV /eqP hUV]] := hY (f x) y hne'.
have hfx' : U (f x) by move: hfx; rewrite inE.
have hyV' : V y by move: hyV; rewrite inE.
have hnU : nbhs x (f @^-1` U).
  apply: hf; have ho := hU; rewrite openE in ho; exact: ho _ hfx'.
have hnV : nbhs y V by have ho := hV; rewrite openE in ho; exact: ho _ hyV'.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x _) hnU.
have [k hk] := hsmall e he.
have [z [[a ha hfa] hzV]] := hy k V hnV.
have hzU : U z.
  rewrite -hfa; apply: hb; exact: hk x a (hx k) ha.
have hh : (U `&` V) z by split.
by rewrite hUV in hh.
Qed.

(** Source for [successive_set_inclusions_nested]: general
    set-theoretic support for the branch intersections in Federer
    2.2.10(2), p. 67: successive inclusion implies inclusion
    between every earlier and later member. *)
Lemma successive_set_inclusions_nested (T : Type) (F : nat -> set T) :
  (forall n, F n.+1 `<=` F n) -> forall n m, (n <= m)%N -> F m `<=` F n.
Proof.
move=> hs n m hnm; elim: m hnm=> [|m IH] hnm.
- have -> : n = 0%N by apply/eqP; rewrite -leqn0.
  exact: subset_refl.
- case: (eqVneq n m.+1)=> [->|hne]; first exact: subset_refl.
  have hle : (n <= m)%N by move: hnm; rewrite leq_eqVlt (negbTE hne) /= ltnS.
  exact: subset_trans (hs m) (IH hle).
Qed.
