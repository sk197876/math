(** Federer (1969), 3.3.19, p. 303: an
    actual convex source avoiding the original centre lies
    in a unit-normal closed halfspace through that centre.
    Prove finite constraints by the existing sealed convex
    hull, then all constraints by compactness of unit normals. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  InnerConvex InnerBoundedness InnerFiniteCompactness ConstrainedUnitSphere
  OrthonormalFamilies InnerCoordinateContinuity CompactClosedFamilyIntersection EuclideanFiniteConvexSide.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_convex_unit_halfspace]: actual
    halfspace containment used when c(B) is outside S
    in 3.3.19, p. 303. The original S need
    only be nonempty and convex; openness, boundedness,
    measurability and a supplied separating normal are
    unnecessary. All auxiliary finite hulls and normals
    remain local, with no external separation theorem. *)
Theorem euclidean_convex_unit_halfspace (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (c:inner_metric_space (@euclidean_inner_productP R n)):
  S!=set0 ->is_inner_convex S ->~S c ->
  exists u:inner_metric_space (@euclidean_inner_productP R n),
    inner_norm (@euclidean_inner_productP R n) u= 1 /\
    forall x,S x ->0<=euclidean_inner_product u (x-c).
Proof.
move=>[x0 hx0] hS hc.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose hE:=@euclidean_inner_productP R n.
pose Q:set E:=[set u|inner_norm hE u= 1].
have hQClosed:closed Q by exact:inner_unit_sphere_closed.
have hQCompact:compact Q.
  apply:(@inner_finite_basis_boundedly_compact R (R_n R n) (@euclidean_inner_product R n) hE
    n (@coordinate_basis R n) (@coordinate_basisP R n));first exact hQClosed.
  exists 1=>u hu;by rewrite hu.
have hHalf x:closed [set u:E|0<=euclidean_inner_product u (x-c)].
  have hEq:[set u:E|0<=euclidean_inner_product u (x-c)]=
      [set u:E|0<=inner_coordinate hE (x-c) u].
    apply:funext=>u.
    exact:(congr1 (fun a:R=>is_true (0<=a))
      (esym (@inner_coordinateE R (R_n R n) (@euclidean_inner_product R n) hE (x-c) u))).
  rewrite hEq.
  change (closed ((fun u:E=>inner_coordinate hE (x-c) u) @^-1` [set t:R^o|0<=t])).
  apply:preimage_closed;last exact:closed_ge.
  by move=>u _;exact:inner_coordinate_continuous.
pose C:=fun x:E=>Q `&` [set u:E|0<=euclidean_inner_product u (x-c)].
have hClosed x:S x ->closed (C x).
  move=>_;apply:closedI;[exact hQClosed|exact:hHalf].
have hCompact:compact (C x0) by exact:(compact_closedI hQCompact (hHalf x0)).
have hFinite (F:{fset E}):(forall x,x \in F ->S x) ->
    exists u:E,forall x,x \in F ->C x u.
  move=>hF.
  pose A:set E:=[set` (x0|`F)%fset].
  have hAFinite:finite_set A by apply/finite_fsetP;by exists (x0|`F)%fset.
  have hANonempty:A!=set0 by exists x0;change (is_true (x0 \in (x0|`F)%fset));by rewrite !inE eqxx.
  have hAInside:A `<=` S.
    move=>x hx;have hxF:x \in (x0|`F)%fset:=hx.
    move/fset1UP:hxF=>[->|hx'];first exact hx0.
    exact:hF x hx'.
  have [u [hu hPositive]]:=@euclidean_finite_convex_strict_side R n S A c
    hS hc hAFinite hANonempty hAInside.
  exists u=>x hx;split;first exact hu.
  apply:ltW;apply:hPositive;change (is_true (x \in (x0|`F)%fset));by rewrite !inE hx orbT.
have [u hAll]:=@compact_closed_family_intersection E E S C x0 hx0 hCompact hClosed hFinite.
exists u;split;first exact:(hAll x0 hx0).1.
move=>x hx;exact:(hAll x hx).2.
Qed.
