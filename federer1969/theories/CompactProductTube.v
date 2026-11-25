(** General topology supporting the open convex comparison of Federer
    (1969), 2.10.4(2), p. 172. An open set containing {p} times a compact
    set contains a product of an open neighbourhood of p and an open
    neighbourhood of the compact set. This expands the finite-cover
    principle of 2.2.5, p. 63, for the continuous family of projections; it
    is not a separately printed measure assertion. Source context and
    supporting topology context: CompactFiniteCover.v and
    MetricCompactNeighbourhood.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactFiniteCover ProductCoordinateNeighborhoods
  MetricOpenThickening MetricCompactNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_open_tube]: supporting
    compact product-neighbourhood argument for Federer
    2.10.4(2), p. 172. Finite rectangle subcovers
    give the two open neighbourhoods; empty compact
    sets are permitted without choosing one of their points. *)
Theorem compact_product_open_tube (P X : topologicalType) (p : P)
    (K : set X) (U : set (P*X)) : compact K -> open U ->
  (forall x, K x -> U (p,x)) ->
  exists V W, open V /\ V p /\ open W /\ K `<=` W /\ V `*` W `<=` U.
Proof.
move=> hK hU hKU.
pose J := [the choiceType of (set P*set X)%type].
pose D : set J := [set z | open z.1 /\ open z.2 /\ z.1 p /\ z.1 `*` z.2 `<=` U].
have hcover : K `<=` \bigcup_(z in D) z.2.
  move=> x hx.
  have hn : nbhs (p,x) U by rewrite openE in hU; exact: hU _ (hKU x hx).
  have [[V W] [hV hW] hsub] := hn.
  exists (V°,W°); last exact hW.
  split; first exact: open_interior.
  split; first exact: open_interior.
  split; first exact hV.
  move=> [q y] [hq hy]; apply: hsub; split; exact: interior_subset.
have [F hF hcov] := @compact_open_finite_cover X J D (fun z => z.2) K hK
  (fun z hz => hz.2.1) hcover.
pose V : set P := \bigcap_(z in [set` F]) z.1.
pose W : set X := \bigcup_(z in [set` F]) z.2.
have hVo : open V.
  apply: fset_bigcap_open=> z hz; have hd : D z := set_mem (hF z hz); exact hd.1.
have hp : V p by move=> z hz; have hd : D z := set_mem (hF z hz); exact hd.2.2.1.
have hWo : open W.
  apply: bigcup_open=> z hz; have hd : D z := set_mem (hF z hz); exact hd.2.1.
exists V,W; split=> //; split=> //; split=> //; split; first exact: hcov.
move=> [q x] [hq [z hz hx]].
have hd : D z := set_mem (hF z hz); exact: hd.2.2.2 (conj (hq z hz) hx).
Qed.

(** Source for [compact_parameter_image_neighbourhood]: supporting
    parameter neighbourhood and positive source radius for
    Federer 2.10.4(2), p. 172. Joint continuity
    and compactness make the entire nearby image lie
    in the chosen open target neighbourhood. *)
Theorem compact_parameter_image_neighbourhood (R : realType) (P : topologicalType)
    (X : metricType R) (Y : topologicalType) (F : P*X -> Y)
    (p : P) (K : set X) (U : set Y) : continuous F -> compact K -> open U ->
  (forall x, K x -> U (F (p,x))) ->
  exists (V : set P) (r : R), open V /\ V p /\ 0<r /\
    forall q x, V q -> metric_open_thickening K r x -> U (F (q,x)).
Proof.
move=> hF hK hU hKU.
have ho : open (F @^-1` U) by apply: open_comp hU=> z _; exact: hF.
have [V [W [hV [hp [hW [hKW hsub]]]]]] := compact_product_open_tube hK ho hKU.
have [r [hr hthick]] := compact_metric_open_thickening hK hW hKW.
exists V,r; split=> //; split=> //; split=> // q x hq hx.
exact (hsub (q,x) (conj hq (hthick x hx))).
Qed.
