(** Federer (1969), 2.10.47, p. 204: the finite closed cube subdivisions
    cover the initial unit cube and have diameter at most sqrt(n) times
    2^(-j). These consequences use only the abstract coordinate law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNorm EuclideanLebesgueHaar EuclideanCubeRadius DyadicCubeGridUP
  ScalarIntervalPartition ScalarIntervalPartitionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Grid.
Variable R : realType.
Variable n : nat.
Variable a : R_n R n.
Variable Q : forall j, dyadic_cube_indices n j ->
  set (inner_metric_space (@euclidean_inner_productP R n)).
Arguments Q j _ _ : clear implicits.
Hypothesis hQ : is_dyadic_cube_grid a Q.

(** Source for [dyadic_cube_compact]: compactness of each
    member of H_j in 2.10.47, p. 204, from
    the closed coordinate-box theorem. *)
Lemma dyadic_cube_compact j s : compact (Q j s).
Proof.
have -> : Q j s = [set x : inner_metric_space (@euclidean_inner_productP R n) |
    forall i, a i+(s i)%:R/((2^j)%N)%:R<=x i<=a i+((s i).+1)%:R/((2^j)%N)%:R].
  apply/seteqP; split=> x hx.
  - exact (proj1 (@hQ j s x) hx).
  - exact (proj2 (@hQ j s x) hx).
exact: euclidean_closed_box_compact.
Qed.

(** Source for [dyadic_cube_nonempty]: supporting nonemptiness
    of every level-j cube in 2.10.47, p. 204;
    its lower corner belongs to it, including when n=0. *)
Lemma dyadic_cube_nonempty j s : Q j s !=set0.
Proof.
exists ([ffun i=> a i+(s i)%:R/((2^j)%N)%:R] : R_n R n).
apply/(@hQ j s)=> i; rewrite ffunE lexx /= lerD2l.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
by rewrite ler_nat leqnSn.
Qed.

(** Source for [dyadic_cube_within_unit_cube]: supporting
    containment in C of every H_j member in 2.10.47,
    p. 204, derived from the bounds on its finite index. *)
Lemma dyadic_cube_within_unit_cube j s x : Q j s x ->
  forall i, a i<=x i<=a i+1.
Proof.
move/(@hQ j s)=> hx i; have /andP [hlo hhi] := hx i.
have hd : (0 : R)<((2^j)%N)%:R by rewrite ltr0n expn_gt0.
have h0 : (0 : R)<=(s i)%:R/((2^j)%N)%:R by apply: mulr_ge0; rewrite ?invr_ge0 ler0n.
have h1 : (((s i).+1)%:R : R)/((2^j)%N)%:R<=1.
  by rewrite ler_pdivrMr // mul1r ler_nat; exact: ltn_ord.
apply/andP; split; lra.
Qed.

(** Source for [dyadic_cube_level_covers]: each finite H_j
    covers C in 2.10.47, p. 204. Closed endpoints
    can belong to both adjacent cubes. The proof uses
    the already sealed equal interval partition, not a
    new floor-function construction. *)
Lemma dyadic_cube_level_covers j (x : inner_metric_space (@euclidean_inner_productP R n)) :
  (forall i, a i<=x i<=a i+1) -> exists s, Q j s x.
Proof.
move=> hx.
have hk : (0<(2^j))%N by rewrite expn_gt0.
pose node := @equal_interval_partition R 1 (2^j) ler01 hk.
have hp := @equal_interval_partition_specification R 1 (2^j) ler01 hk.
have hcell i : exists k : 'I_((2^j)%N),
    a i+k%:R/((2^j)%N)%:R<=x i<=a i+(k.+1)%:R/((2^j)%N)%:R.
  have /andP [hl hu] := hx i.
  have hi : 0<=x i-a i<=1 by apply/andP; split; lra.
  have [k /andP [hlo hhi]] := equal_interval_cell_cover hp hi.
  rewrite (equal_interval_node_expansion hp (ltnW (ltn_ord k))) mul1r in hlo.
  rewrite (equal_interval_node_expansion hp (ltn_ord k)) mul1r in hhi.
  exists k; apply/andP; split; lra.
pose s i := projT1 (cid (hcell i)).
exists [ffun i=>s i]; apply/(@hQ j _)=> i; rewrite ffunE.
exact: (projT2 (cid (hcell i))).
Qed.

(** Source for [dyadic_cube_distance_bound]: supporting
    diameter bound sqrt(n) 2^(-j) in the first
    comparison of 2.10.47, p. 204. It includes
    the singleton cube in ambient dimension zero. *)
Lemma dyadic_cube_distance_bound j s x y : Q j s x -> Q j s y ->
  mdist x y<=Num.sqrt n%:R/((2^j)%N)%:R.
Proof.
move/(@hQ j s)=> hx; move/(@hQ j s)=> hy.
rewrite inner_metric_distanceE.
apply: euclidean_coordinate_cube_norm_bound; first by rewrite invr_ge0 ler0n.
move=> i; have /andP [hxl hxu] := hx i; have /andP [hyl hyu] := hy i.
have he : (((s i).+1)%:R : R)/((2^j)%N)%:R =
    (s i)%:R/((2^j)%N)%:R + ((2^j)%N)%:R^-1.
  by rewrite -addn1 natrD mulrDl mul1r.
rewrite he in hxu.
rewrite he in hyu.
rewrite !ffunE.
rewrite ler_norml; apply/andP; split; lra.
Qed.
End Grid.
