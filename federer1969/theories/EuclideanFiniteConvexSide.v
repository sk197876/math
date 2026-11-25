(** Federer (1969), 3.3.19, p. 303: actual
    finite subsets of a convex set avoiding a point
    lie strictly to one side of a unit-normal hyperplane
    through that point. Use only the existing sealed
    hull laws and proved compact nearest-point criterion. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  InnerConvex ConvexHull CompactHullDirectionalCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_finite_convex_strict_side]:
    supporting halfplane choice for actual hit points
    in 3.3.19, p. 303. Every finite set
    of original points in the original convex source
    is strictly separated from an original point outside
    it. The unit normal is derived and remains local. *)
Theorem euclidean_finite_convex_strict_side (R:realType) n
    (S A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (c:inner_metric_space (@euclidean_inner_productP R n)):
  is_inner_convex S ->~S c ->finite_set A ->A!=set0 ->A `<=` S ->
  exists u:inner_metric_space (@euclidean_inner_productP R n),
    inner_norm (@euclidean_inner_productP R n) u= 1 /\
    forall a,A a ->0<euclidean_inner_product u (a-c).
Proof.
move=>hS hc hFinite hNonempty hInside.
apply:contrapT=>hNone.
have hAll u:euclidean_inner_product u u= 1 ->
    exists a,A a /\euclidean_inner_product u (a-c)<=0.
  move=>hu;apply:contrapT=>hBad;apply:hNone.
  exists u;split.
  - apply:inner_norm_value;first exact:ler01.
    by rewrite expr1n.
  - move=>a ha;case:(ltP 0 (euclidean_inner_product u (a-c)))=>[h|h];first by [].
    exfalso;apply:hBad;by exists a;split.
have hHull:=@compact_hull_directional_criterion R n A c (finite_compact hFinite) hNonempty hAll.
exact:hc (@convex_hull_least R (R_n R n) A S hInside hS c hHull).
Qed.
