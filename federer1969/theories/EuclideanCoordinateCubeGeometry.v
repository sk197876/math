(** Federer (1969), 3.2.38, pp. 274--275: actual compactness,
    volume, diameter and convexity of the source cubes. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm
  InnerNormedTopology InnerConvex EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLebesgueBoxes
  EuclideanCoordinateCubeUP EuclideanBoxUP OrthonormalFamilies CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Cube.
Variable R:realType.
Variable n:nat.
Variable a:R_n R n.
Variable h:R.
Variable Q:set (inner_metric_space (@euclidean_inner_productP R n)).
Hypothesis hQ:is_euclidean_coordinate_cube a h Q.

(** Source for [coordinate_cube_nonempty]: the lower corner belongs
    to every cube of Federer 3.2.38, p. 274, including the R^0 atom. *)
Lemma coordinate_cube_nonempty:Q!=set0.
Proof. exists a; apply:(hQ.2 a).2=>i; by rewrite lexx /= lerDl; exact:hQ.1. Qed.

(** Source for [coordinate_cube_compact]: the finite closed cubes in
    Federer 3.2.38, p. 274, are compact by finite bounded compactness. *)
Lemma coordinate_cube_compact:compact Q.
Proof.
have ->:Q=[set x|forall i,a i<=x i<=a i+h].
  by apply/seteqP; split=>x; [exact:(hQ.2 x).1|exact:(hQ.2 x).2].
exact:euclidean_closed_box_compact.
Qed.

(** Source for [coordinate_cube_volume]: actual Lebesgue volume h^n
    of the source cubes in Federer 3.2.38, pp. 274--275.
    The empty coordinate product gives mass one in dimension zero. *)
Lemma coordinate_cube_volume:@euclidean_lebesgue_measure R n Q=(h^+n)%:E.
Proof.
have ->:Q=[set x|forall i,a i<=x i<=a i+h].
  by apply/seteqP; split=>x; [exact:(hQ.2 x).1|exact:(hQ.2 x).2].
rewrite (@euclidean_closed_box R n (fun i=>a i) (fun i=>a i+h)); last first.
  by move=>i; rewrite lerDl; exact:hQ.1.
have ->:(\prod_(i<n) (a i+h-a i))=\prod_(i<n) h.
  by apply:eq_bigr=>i _; rewrite addrAC subrr add0r.
by rewrite prodr_const card_ord.
Qed.

(** Source for [coordinate_cube_distance_bound]: diam K <= n h
    in Federer 3.2.38, p. 274, from the actual coordinate bounds.
    This deliberately uses the printed loose n h bound rather than
    requiring a positive dimension or a square-root normalization. *)
Lemma coordinate_cube_distance_bound x y:Q x ->Q y ->mdist x y<=n%:R*h.
Proof.
move=>hx hy; rewrite inner_metric_distanceE -inner_norm_topologyE.
apply:le_trans (@euclidean_norm_coordinate_sum R n (x-y)) _.
have hCoord i:`|(x-y) i|<=h.
  have /andP[hxl hxu]:=(hQ.2 x).1 hx i.
  have /andP[hyl hyu]:=(hQ.2 y).1 hy i.
  rewrite !ffunE ler_norml; apply/andP; split; lra.
have hSum:(\sum_(i<n) `|(x-y) i|)<=\sum_(i<n) h.
  apply:ler_sum=>i _; exact:hCoord.
apply:le_trans hSum _.
by rewrite sumr_const card_ord -(@mulr_natl R h n).
Qed.

(** Source for [coordinate_cube_convex]: source cubes are convex in
    the affine comparison with g(K), Federer 3.2.38, pp. 274--275. *)
Lemma coordinate_cube_convex:is_inner_convex Q.
Proof.
move=>x y hx hy t ht0 ht1; apply:(hQ.2 _).2=>i.
have /andP[hxl hxu]:=(hQ.2 x).1 hx i.
have /andP[hyl hyu]:=(hQ.2 y).1 hy i.
have hOne:0<=1-t by rewrite subr_ge0.
rewrite !ffunE; apply/andP; split.
- have h1:=ler_wpM2l hOne hxl; have h2:=ler_wpM2l ht0 hyl.
  have hCombined:=lerD h1 h2.
  have hWeighted:(1-t)*a i+t*a i=a i by ring.
  by rewrite hWeighted in hCombined.
- have h1:=ler_wpM2l hOne hxu; have h2:=ler_wpM2l ht0 hyu.
  have hCombined:=lerD h1 h2.
  have hWeighted:(1-t)*(a i+h)+t*(a i+h)=a i+h by ring.
  by rewrite hWeighted in hCombined.
Qed.

(** Source for [coordinate_cube_rectangular_box]: identification with
    the independently specified orthonormal box of 2.7.16, p. 136,
    supporting the affine-volume step in Federer 3.2.38, p. 275. *)
Lemma coordinate_cube_rectangular_box:
  is_euclidean_rectangular_box a (@coordinate_basis R n) (fun _=>h) Q.
Proof.
constructor.
- by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
- by move=>i; exact:hQ.1.
- move=>x; split=>hx.
  + move=>i; have /andP[hl hu]:=(hQ.2 x).1 hx i.
    rewrite euclidean_inner_basis !ffunE; apply/andP; split; lra.
  + apply:(hQ.2 x).2=>j.
    have hh:=hx j; rewrite euclidean_inner_basis !ffunE in hh.
    have /andP[hl hu]:=hh; apply/andP; split; lra.
Qed.
End Cube.
