(** Federer (1969), 3.2.36, p. 273: the actual
    coordinate box has the hypotheses of the convex product theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerConvex InnerNorm InnerNormedTopology InnerFiniteCompactness InnerBoundedness
  EuclideanCoordinateTopology EuclideanLebesgueHaar CompactSetDistanceProfile CompactMetricBounded CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_edge_box]: the rectangular box with the
    given edge lengths in Federer 3.2.36, p. 273, expressed in
    the standard coordinates of 2.7.16, p. 136. Its carrier
    is specified by the original coordinate inequalities; zero widths
    and the empty coordinate family are retained. *)
Definition coordinate_edge_box (R:realType) n (c:'I_n->R):
    set (inner_metric_space (@euclidean_inner_productP R n)):=
  [set x|forall i,0<=x i<=c i].

(** Source for [coordinate_edge_box_nonempty]: the origin belongs to
    the box with nonnegative edges in Federer 3.2.36, p. 273,
    including all zero widths and the single R^0 point. *)
Lemma coordinate_edge_box_nonempty (R:realType) n (c:'I_n->R):
  (forall i,0<=c i) ->coordinate_edge_box c!=set0.
Proof.
move=>hc; exists 0=>i; by rewrite ffunE lexx /=; exact:hc.
Qed.

(** Source for [coordinate_edge_box_convex]: the box in the elementary
    symmetric-function consequence of Federer 3.2.36, p. 273,
    is convex by its actual coordinate inequalities. Degenerate or
    empty boxes are allowed; no positivity of an edge is required. *)
Lemma coordinate_edge_box_convex (R:realType) n (c:'I_n->R):
  is_inner_convex (coordinate_edge_box c).
Proof.
move=>x y hx hy t ht0 ht1 i.
have /andP[hx0 hxc]:=hx i.
have /andP[hy0 hyc]:=hy i.
have hOne:0<=1-t by rewrite subr_ge0.
rewrite /coordinate_edge_box /= !ffunE.
apply/andP; split.
- exact:addr_ge0 (mulr_ge0 hOne hx0) (mulr_ge0 ht0 hy0).
- have hFirst:(1-t)*x i<=(1-t)*c i by rewrite ler_wpM2l.
  have hSecond:t*y i<=t*c i by rewrite ler_wpM2l.
  have h:=lerD hFirst hSecond.
  have hSum:(1-t)*c i+t*c i=c i by ring.
  by rewrite hSum in h.
Qed.

(** Source for [coordinate_edge_box_closed]: the actual coordinate
    box is closed, supporting the finite convex product induction
    of Federer 3.2.36, p. 273. Continuous coordinates and closed
    scalar interval inequalities give the result through an arbitrary
    closed intersection. No measurability assumption is added. *)
Lemma coordinate_edge_box_closed (R:realType) n (c:'I_n->R):
  @closed (inner_metric_space (@euclidean_inner_productP R n)) (coordinate_edge_box c).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hEq:coordinate_edge_box c=\bigcap_(i:'I_n) [set x:X|0<=x i<=c i].
  apply/seteqP; split=>x hx.
  - by move=>i _; exact:hx.
  - by move=>i; exact:hx i I.
rewrite hEq; apply:closed_bigI=>i _.
have hInterval:closed [set y:R^o|0<=y<=c i].
  have hSet:[set y:R^o|0<=y<=c i]=[set y:R^o|0<=y] `&` [set y:R^o|y<=c i].
    apply/seteqP; split=>y; [by move/andP|by move=>h; apply/andP].
  rewrite hSet; apply:closedI; [exact:closed_ge|exact:closed_le].
exact:((@continuous_closedP X R^o (fun x:X=>x i)).1 (@euclidean_coordinate_continuous R n i)
  _ hInterval).
Qed.

(** Source for [coordinate_edge_box_compact]: finite bounded compactness
    from 1.7.1, p. 28, for the box in Federer 3.2.36,
    p. 273. Its actual norm is bounded by the sum of its
    nonnegative coordinate bounds on each member. The proof retains
    zero widths, empty boxes and the zero-dimensional point. *)
Lemma coordinate_edge_box_compact (R:realType) n (c:'I_n->R):
  @compact (inner_metric_space (@euclidean_inner_productP R n)) (coordinate_edge_box c).
Proof.
have hCompact:=@inner_finite_basis_boundedly_compact R (R_n R n) _ (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
apply:hCompact; first exact:coordinate_edge_box_closed.
exists (\sum_i c i)=>x hx.
change (inner_norm (@euclidean_inner_productP R n) x<=\sum_i c i).
rewrite -inner_norm_topologyE.
apply:le_trans (@euclidean_norm_coordinate_sum R n x) _.
apply:ler_sum=>i _; have /andP[hx0 hxc]:=hx i.
by rewrite (ger0_norm hx0).
Qed.

(** Source for [coordinate_edge_box_bounded]: the bounded original
    source needed for the product deduction of Federer 3.2.36,
    p. 273, follows from actual box compactness and nonemptiness.
    All nonnegative edge vectors, including the zero vector, remain. *)
Lemma coordinate_edge_box_bounded (R:realType) n (c:'I_n->R):
  (forall i,0<=c i) ->metric_set_bounded (coordinate_edge_box c).
Proof.
move=>hc.
pose C:compact_metric_set (inner_metric_space (@euclidean_inner_productP R n)):=
  exist _ (coordinate_edge_box c)
    (mem_set (conj (@coordinate_edge_box_compact R n c) (coordinate_edge_box_nonempty hc))).
exact:compact_metric_diameter_finite C.
Qed.
