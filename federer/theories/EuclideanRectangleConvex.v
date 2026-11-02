(** Federer (1969), 2.10.46, p. 203: the covering argument uses products of
    a closed first-factor ball and closed convex second-factor generators
    from 2.10.4(2), p. 172. The following admissibility facts are
    consequences of the ordinary block coordinates of 2.6.5, p. 120. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanBlockCoordinates MetricProductRectangles TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_rectangle_closed]: supporting closed
    generator admissibility in the product covering argument of
    2.10.46, p. 203. Closed sets need not be bounded. *)
Lemma euclidean_rectangle_closed (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  closed S -> closed T -> closed (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) S T).
Proof.
move=> hS hT.
pose X := [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)].
pose Y := [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)].
have hprod : closed (S `*` T).
  change (closed ((@fst X Y @^-1` S) `&` (@snd X Y @^-1` T))).
  apply: closedI.
  - exact: (continuous_closedP (@fst X Y)).1 (@first_projection_continuous X Y) S hS.
  - exact: (continuous_closedP (@snd X Y)).1 (@second_projection_continuous X Y) T hT.
change (closed ((@euclidean_block_split R m n) @^-1` (S `*` T))).
exact: (continuous_closedP (@euclidean_block_split R m n)).1
  (@euclidean_block_split_continuous R m n) (S `*` T) hprod.
Qed.

(** Source for [euclidean_rectangle_convex]: supporting convex
    generator admissibility in 2.10.46, p. 203. Convex
    combinations are evaluated in the specified block coordinates,
    including empty factors and zero-dimensional blocks. *)
Lemma euclidean_rectangle_convex (R : realType) m n
    (S : set (R_n R m)) (T : set (R_n R n)) :
  is_inner_convex S -> is_inner_convex T -> is_inner_convex
    (metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
      (fun z=>(@euclidean_block_split R m n z).2) S T).
Proof.
move=> hS hT x y [hxS hxT] [hyS hyT] t ht ht1.
have hl : (@euclidean_block_split R m n ((1-t)*:x+t*:y)).1=
    (1-t)*:(@euclidean_block_split R m n x).1+t*:(@euclidean_block_split R m n y).1.
  by apply/ffunP=> i; rewrite /euclidean_block_split !ffunE.
have hr : (@euclidean_block_split R m n ((1-t)*:x+t*:y)).2=
    (1-t)*:(@euclidean_block_split R m n x).2+t*:(@euclidean_block_split R m n y).2.
  by apply/ffunP=> i; rewrite /euclidean_block_split !ffunE.
change (S ((@euclidean_block_split R m n ((1-t)*:x+t*:y)).1) /\
  T ((@euclidean_block_split R m n ((1-t)*:x+t*:y)).2)).
rewrite hl hr; split; [exact: hS|exact: hT].
Qed.
