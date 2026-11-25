(** Federer (1969), 2.10.2(1), p. 171: replacement by convex hulls in a
    normed vector space. This private existence proof supports the
    least-convex-superset laws already specified for 1.8.1, p. 38. The
    intersection construction is hidden behind ConvexHullSealed.v. it is not
    needed for this existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerConvex ConvexHullUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [convex_hull_exists]: supporting existence
    of the hull used in Federer 2.10.2(1), p. 171.
    Intersect all convex supersets and prove the universal
    laws; no closure or finite-dimensionality is imposed. *)
Theorem convex_hull_exists (R : realFieldType) (V : lmodType R) (A : set V) :
  exists C, is_convex_hull A C.
Proof.
exists [set x | forall D : set V, A `<=` D -> is_inner_convex D -> D x].
constructor.
- by move=> x hx D hAD hD; exact: hAD x hx.
- move=> x y hx hy t ht ht1 D hAD hD.
  exact: hD x y (hx D hAD hD) (hy D hAD hD) t ht ht1.
- by move=> D hAD hD x hx; exact: hx D hAD hD.
Qed.
