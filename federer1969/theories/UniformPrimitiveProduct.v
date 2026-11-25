(** Supporting product rule for the elementary primitive calculations in
    Federer (1969), 2.6.3(2), pp. 117–118 The proof uses finite increments,
    uniform continuity and bounds on a compact segment, with no imported
    differentiation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology normedtype ring lra.
From Federer Require Import UniformPrimitiveUP SegmentUniformContinuity ContinuousSegmentBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [uniform_primitive_product_bounded]: supporting product rule
    for the rational primitive evaluations in Federer 2.6.3(2), pp. 117–118
    All bounds and uniform increment laws are premises subsequently proved
    for the actual rational functions. *)
Lemma uniform_primitive_product_bounded (R : realType) (f F g G : R -> R) (a b M : R) :
  continuous F -> continuous G -> 0 < M ->
  (forall x, a <= x <= b -> [/\ `|f x| <= M, `|F x| <= M, `|g x| <= M & `|G x| <= M]) ->
  is_uniform_primitive_on f F a b -> is_uniform_primitive_on g G a b ->
  is_uniform_primitive_on (fun x => f x*G x+F x*g x) (fun x => F x*G x) a b.
Proof.
move=> hFc hGc hM hbound hF hG e he.
pose eps := e/(4*M).
have h4M : 0 < 4*M by rewrite mulr_gt0 // ltr0n.
have heps : 0 < eps by rewrite /eps divr_gt0.
have [d1 [hd1 h1]] := hF _ heps; have [d2 [hd2 h2]] := hG _ heps.
have [d3 [hd3 h3]] := @segment_uniform_continuity R F a b eps hFc heps.
have [d4 [hd4 h4]] := @segment_uniform_continuity R G a b eps hGc heps.
exists (Order.min d1 (Order.min d2 (Order.min d3 d4))).
split; first by rewrite !lt_min hd1 hd2 hd3 hd4.
move=> s u t has hsu hut htb ht.
move: ht; rewrite !lt_min=> /andP[ht1 /andP[ht2 /andP[ht3 ht4]]].
have hs : a <= s <= b by rewrite has /=; exact: le_trans hsu (le_trans hut htb).
have hu : a <= u <= b by rewrite (le_trans has hsu) /=; exact: le_trans hut htb.
have hT : a <= t <= b by rewrite htb andbT; exact: le_trans has (le_trans hsu hut).
have hlen : 0 <= t-s by rewrite subr_ge0; exact: le_trans hsu hut.
have hFcell := h1 s u t has hsu hut htb ht1.
have hGcell := h2 s u t has hsu hut htb ht2.
have hFdiff : `|F s-F u| <= eps.
  apply: ltW; apply: (h3 s u hs hu).
  rewrite ler0_norm; last by rewrite subr_le0.
  have hsu' : -(s-u) <= t-s by lra.
  exact: le_lt_trans hsu' ht3.
have hGdiff : `|G t-G u| <= eps.
  apply: ltW; apply: (h4 t u hT hu).
  rewrite ger0_norm; last by rewrite subr_ge0.
  have htu : t-u <= t-s by lra.
  exact: le_lt_trans htu ht4.
have [hfs hFs hgs hGs] := hbound s hs.
have [hfu hFu hgu hGu] := hbound u hu.
have [hft hFt hgt hGt] := hbound t hT.
have hb1 : `|G t*(F t-F s-f u*(t-s))| <= M*eps*(t-s).
  rewrite normrM -mulrA; apply: ler_pM=> //; exact: normr_ge0.
have hb2 : `|F s*(G t-G s-g u*(t-s))| <= M*eps*(t-s).
  rewrite normrM -mulrA; apply: ler_pM=> //; exact: normr_ge0.
have hb3 : `|f u*(G t-G u)*(t-s)| <= M*eps*(t-s).
  rewrite !normrM (ger0_norm hlen); apply: (ler_wpM2r hlen).
  apply: ler_pM=> //; exact: normr_ge0.
have hb4 : `|g u*(F s-F u)*(t-s)| <= M*eps*(t-s).
  rewrite !normrM (ger0_norm hlen); apply: (ler_wpM2r hlen).
  apply: ler_pM=> //; exact: normr_ge0.
have heq : F t*G t-F s*G s-(f u*G u+F u*g u)*(t-s) =
    G t*(F t-F s-f u*(t-s))+F s*(G t-G s-g u*(t-s))+
    f u*(G t-G u)*(t-s)+g u*(F s-F u)*(t-s) by ring.
rewrite heq; apply: le_trans (ler_normD _ _) _.
apply: le_trans (lerD (ler_normD _ _) (lexx _)) _.
apply: le_trans (lerD (lerD (ler_normD _ _) (lexx _)) (lexx _)) _.
have hsum := lerD (lerD (lerD hb1 hb2) hb3) hb4.
have hcoef : M*eps*(t-s)+M*eps*(t-s)+M*eps*(t-s)+M*eps*(t-s)=e*(t-s).
  rewrite /eps; by field; rewrite (gt_eqF hM).
by rewrite hcoef in hsum.
Qed.

(** Source for [uniform_primitive_product]: supporting product rule on a
    compact interval for Federer 2.6.3(2), pp. 117–118 Continuity supplies
    the bounds needed by the finite-increment argument, rather than adding
    them as unproved assumptions. *)
Lemma uniform_primitive_product (R : realType) (f F g G : R -> R) (a b : R) :
  continuous f -> continuous F -> continuous g -> continuous G ->
  is_uniform_primitive_on f F a b -> is_uniform_primitive_on g G a b ->
  is_uniform_primitive_on (fun x => f x*G x+F x*g x) (fun x => F x*G x) a b.
Proof.
move=> hfc hFc hgc hGc hF hG.
have [M1 [h1 hb1]] := @continuous_positive_segment_bound R f a b hfc.
have [M2 [h2 hb2]] := @continuous_positive_segment_bound R F a b hFc.
have [M3 [h3 hb3]] := @continuous_positive_segment_bound R g a b hgc.
have [M4 [h4 hb4]] := @continuous_positive_segment_bound R G a b hGc.
pose M := M1+M2+M3+M4.
have hM : 0 < M by rewrite /M; lra.
apply: (@uniform_primitive_product_bounded R f F g G a b M hFc hGc hM _ hF hG).
move=> x hx; have b1 := hb1 x hx; have b2 := hb2 x hx; have b3 := hb3 x hx; have b4 := hb4 x hx.
rewrite /M; split; lra.
Qed.
