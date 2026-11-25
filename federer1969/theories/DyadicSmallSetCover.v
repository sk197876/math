(** Federer (1969), 2.10.47, p. 204: a subset of the root cube with diameter
    at most 2^(-j) is covered by at most 2^n level-j cubes. Choose two cells
    containing each coordinate range, then take their finite products.
    Boolean coordinate functions index the 2^n choices; repetitions are
    harmless and are removed by set-valued covering sums. Source context:
    DyadicCubeGridUP.v and TwoCellIntervalCover.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP CompactCoordinateExtremes TwoCellIntervalCover MetricDiameter MetricDiameterClosure
  EuclideanLebesgueHaar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dyadic_binary_choice_count]: the number
    2^n in the small-set covering argument of 2.10.47,
    p. 204; the empty coordinate family gives one choice. *)
Lemma dyadic_binary_choice_count n : #|{ffun 'I_n -> bool}|=(2^n)%N.
Proof. by rewrite card_ffun card_bool card_ord. Qed.

(** Source for [dyadic_compact_small_set_cover]: supporting
    compact form of the 2^n covering assertion in
    2.10.47, p. 204, including diameter-zero sets.
    No positive degree or boundary-null hypothesis is used. *)
Theorem dyadic_compact_small_set_cover (R : realType) n (a : R_n R n) Q j
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_dyadic_cube_grid a Q -> compact S -> S!=set0 ->
  (forall x, S x -> forall i, a i<=x i<=a i+1) ->
  (extended_metric_diameter S<=(((2^j)%N)%:R^-1)%:E)%E ->
  exists F : {ffun 'I_n -> bool} -> dyadic_cube_indices n j,
    S `<=` \bigcup_b @Q j (F b).
Proof.
move=> hQ hS hne hroot hdiam.
have hk : (0<(2^j))%N by rewrite expn_gt0.
have hex i : exists pq : ('I_((2^j)%N)*'I_((2^j)%N))%type,
    forall x, S x ->
    pq.1%:R/((2^j)%N)%:R<=x i-a i<=pq.1.+1%:R/((2^j)%N)%:R \/
    pq.2%:R/((2^j)%N)%:R<=x i-a i<=pq.2.+1%:R/((2^j)%N)%:R.
  have [l [u [hl hu hbounds hwidth]]] := @compact_euclidean_coordinate_extremes R n S i _ hS hne hdiam.
  have /andP [hl0 hl1] := hroot l hl i.
  have /andP [hu0 hu1] := hroot u hu i.
  have /andP [hlu _] := hbounds u hu.
  have hl' : 0<=l i-a i by lra.
  have hlu' : l i-a i<=u i-a i by lra.
  have hu' : u i-a i<=1 by lra.
  have hw' : (u i-a i)-(l i-a i)<=((2^j)%N)%:R^-1 by lra.
  have [p [q hpq]] := @two_grid_cells_cover_short_interval R (2^j) (l i-a i) (u i-a i) hk hl' hlu' hu' hw'.
  exists (p,q)=> x hx; apply: hpq.
  have /andP [hlo hhi] := hbounds x hx; apply/andP; split; lra.
pose pq i := projT1 (cid (hex i)).
have hpair i := projT2 (cid (hex i)).
pose F (b : {ffun 'I_n -> bool}) : dyadic_cube_indices n j :=
  [ffun i=> if b i then (pq i).1 else (pq i).2].
exists F=> x hx.
have hbool i : exists c : bool,
    (if c then (pq i).1 else (pq i).2)%:R/((2^j)%N)%:R<=x i-a i<=
    (if c then (pq i).1 else (pq i).2).+1%:R/((2^j)%N)%:R.
  case: (hpair i x hx)=> hh; [by exists true | by exists false].
pose b : {ffun 'I_n -> bool} := [ffun i=>projT1 (cid (hbool i))].
exists b=> //; apply/(hQ j (F b))=> i.
rewrite /F /b !ffunE.
have /andP [hlo hhi] := projT2 (cid (hbool i)); apply/andP; split; lra.
Qed.

(** Source for [dyadic_small_set_cover]: the arbitrary-set
    2^n covering assertion of 2.10.47, p. 204.
    Pass to the compact closure inside the root cube;
    the diameter is unchanged. No measurability or
    closedness of the original covering set is required. *)
Theorem dyadic_small_set_cover (R : realType) n (a : R_n R n) Q j
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_dyadic_cube_grid a Q -> S!=set0 ->
  (forall x, S x -> forall i, a i<=x i<=a i+1) ->
  (extended_metric_diameter S<=(((2^j)%N)%:R^-1)%:E)%E ->
  exists F : {ffun 'I_n -> bool} -> dyadic_cube_indices n j,
    S `<=` \bigcup_b @Q j (F b).
Proof.
move=> hQ hne hroot hdiam.
pose C := [set x : inner_metric_space (@euclidean_inner_productP R n) | forall i, a i<=x i<=a i+1].
have hC : compact C := @euclidean_closed_box_compact R n a (fun i=>a i+1).
have hclosed : closed C := compact_closed (@metric_hausdorff R _) hC.
have hsub : closure S `<=` C.
  rewrite (proj1 (closure_id C) hclosed); exact: closureS hroot.
have hcomp : compact (closure S) := @subclosed_compact _ (closure S) C (@closed_closure _ S) hC hsub.
have hclne : closure S!=set0 by have [x hx] := hne; exists x; exact: subset_closure hx.
have hcldiam : (extended_metric_diameter (closure S)<=(((2^j)%N)%:R^-1)%:E)%E.
  by rewrite extended_metric_diameter_closure.
have [F hF] := @dyadic_compact_small_set_cover R n a Q j (closure S) hQ hcomp hclne hsub hcldiam.
exists F=> x hx; exact: hF _ (subset_closure hx).
Qed.
