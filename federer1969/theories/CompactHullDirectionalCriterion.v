(** Federer (1969), 2.10.40, printed p. 200: no hyperplane strictly
    separates the minimum centre from the compact contact-centre set, so the
    centre belongs to its convex hull. This supporting lemma proves the
    implication by a nearest point in the compact convex hull, using 1.7.13,
    p. 37. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric InnerNormalization InnerNearestUP
  CompactNearest NearestConvexVariational InnerCompactConvexHull ConvexHull
  Bilinear BilinearNegation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_hull_directional_criterion]: supporting
    last convex-hull step in 2.10.40, p. 200.
    If each unit direction has a generator on its
    nonpositive side relative to b, then b belongs
    to the actual sealed convex hull of that compact set. *)
Theorem compact_hull_directional_criterion (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (b : inner_metric_space (@euclidean_inner_productP R n)) :
  compact A -> A !=set0 ->
  (forall u, euclidean_inner_product u u= 1 ->
    exists a, A a /\ euclidean_inner_product u (a-b)<=0) -> convex_hull A b.
Proof.
move=> hA hne hdir.
pose H := convex_hull A.
have hH : compact H := @inner_compact_convex_hull R _ _ (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) A (@coordinate_basisP R n) hA hne.
have hHne : H !=set0.
  have [a ha] := hne; exists a; exact: convex_hull_includes ha.
have [z hz] := @compact_inner_nearest_exists R _ _ (@euclidean_inner_productP R n) b H hHne hH.
apply: contrapT=> hbnot.
pose v := z-b.
have hv : v!=0.
  apply/eqP=> hv0; apply: hbnot.
  have he : z=b.
    apply/eqP; rewrite -subr_eq0.
    change (is_true (v==0)); by rewrite hv0 eqxx.
  rewrite -he; exact: inner_nearest_member_law hz.
pose u := inner_normalize (@euclidean_inner_productP R n) v.
have hu : euclidean_inner_product u u= 1 := inner_normalize_square _ hv.
have [a [ha hsign]] := hdir u hu.
have haH : H a := convex_hull_includes ha.
have hvar := @inner_nearest_convex_variational R _ _ (@euclidean_inner_productP R n)
  H (@convex_hull_convex R _ A) b z hz a haH.
rewrite -[b-z]opprB (bilNl (@euclidean_inner_bilinear R n)) oppr_le0 in hvar.
have hvar' : 0<=euclidean_inner_product v (a-z) := hvar.
have hnorm : 0<inner_norm (@euclidean_inner_productP R n) v by rewrite inner_norm_gt0.
have hinv : 0<(inner_norm (@euclidean_inner_productP R n) v)^-1 by rewrite invr_gt0.
rewrite /u /inner_normalize (bilZl (@euclidean_inner_bilinear R n)) in hsign.
change (is_true ((inner_norm (@euclidean_inner_productP R n) v)^-1*
  euclidean_inner_product v (a-b)<=0)) in hsign.
rewrite (pmulr_rle0 _ hinv) in hsign.
have hsplit : a-b=(a-z)+v by rewrite /v addrA subrK.
rewrite hsplit (bilDr (@euclidean_inner_bilinear R n)) in hsign.
have hself : 0<euclidean_inner_product v v by rewrite (inner_positive (@euclidean_inner_productP R n)).
have hpositive := ler_ltD hvar' hself.
rewrite add0r in hpositive.
have hfalse := lt_le_trans hpositive hsign; by rewrite ltxx in hfalse.
Qed.
