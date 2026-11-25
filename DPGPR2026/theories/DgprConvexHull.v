(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    lem:hull: the convex hull of a compact subset of a finite dimensional
    normed space is compact. Federer's [finite_norm_compact_convex_hull]
    (supporting 2.10.21) proves the case of a nonempty set; the empty set
    has the empty hull. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerConvex ConvexHull LinearBasis
  FiniteNormCompactHull EuclideanCompactConvexHullAll.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [dgpr_hull_compact]: blueprint lem:hull, with Federer
    2.10.2(1), p. 171, for the convex hull and 2.10.21, p. 184, for its
    compactness. The space V with the norm N is finite dimensional
    because it has the finite basis e. *)
Theorem dgpr_hull_compact (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    d (e : 'I_d -> V) (A : set (real_norm_metric_space hN)) :
  is_basis e -> compact A -> compact (@convex_hull R V A : set (real_norm_metric_space hN)).
Proof.
move=> he hA; have [hne|h0] := pselect (A !=set0).
  exact: finite_norm_compact_convex_hull he hA hne.
have hA0 : A = set0.
  by apply/seteqP; split=> [x hx|x []]; apply: h0; exists x.
by rewrite hA0 convex_hull_empty; exact: compact0.
Qed.
