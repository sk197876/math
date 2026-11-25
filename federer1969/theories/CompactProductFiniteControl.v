(** Federer (1969), 2.6.6, p. 120: finite-coordinate functions are uniformly
    dense in the continuous functions on a compact product. This supporting
    lemma obtains uniform control from finitely many coordinates by a finite
    open cover. the argument here permits an arbitrary index set. The
    working erratum has no correction to book pp. 120–121 concerning this
    item. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactFiniteCover ProductCoordinateNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_continuous_finite_control]: supporting
    finite-coordinate uniform-oscillation estimate for density of L
    in K(X), Federer 2.6.6, p. 120. Compactness
    of the whole product is the only compactness premise; a
    nonempty product is not needed for this estimate. *)
Theorem compact_product_continuous_finite_control (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (f : prod_topology Y -> real_line_metric R) (e : R) :
  compact [set: prod_topology Y] -> continuous f -> 0<e ->
  exists F : {fset I}, forall x y, (forall i, i \in F -> x i=y i) -> `|f x-f y|<e.
Proof.
move=> hX hf he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have hchoice x : exists W : set (prod_topology Y), exists F : {fset I},
    open W /\ W x /\ W `<=` f @^-1` ball (f x) (e/2) /\
    forall y z, (forall i, i \in F -> y i=z i) -> W y -> W z.
  have hn : nbhs x (f @^-1` ball (f x) (e/2)).
    apply: (hf x); exact: nbhsx_ballx he2.
  have [W [hW [hx [hsub [F hdet]]]]] := @prod_nbhs_finitely_determined I Y x _ hn.
  by exists W,F.
pose W x := sval (cid (hchoice x)).
pose G x := sval (cid (svalP (cid (hchoice x)))).
have hW x := svalP (cid (svalP (cid (hchoice x)))).
have hcover : [set: prod_topology Y] `<=` \bigcup_(x in setT) W x.
  move=> x _; exists x=> //; exact: (hW x).2.1.
have [D hD hcov] := @compact_open_finite_cover (prod_topology Y) (prod_topology Y) setT W setT
  hX (fun x _ => (hW x).1) hcover.
pose F : {fset I} := (\bigcup_(x <- D) G x)%fset.
exists F=> x y hxy.
have [z hz hx] := hcov x Logic.I.
have hy : W z y.
  apply: (hW z).2.2.2 _ _ _ hx=> i hi; apply: hxy.
  apply/bigfcupP; exists z; by rewrite ?andbT.
have hxb := (hW z).2.2.1 x hx.
have hyb := (hW z).2.2.1 y hy.
have hh := ball_triangle (ball_sym hxb) hyb.
by rewrite real_line_ball_distance -splitr in hh.
Qed.
