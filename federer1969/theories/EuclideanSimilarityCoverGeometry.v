(** Federer (1969), 3.2.26(2), p. 261: translating
    and positively scaling a convex unit neighbourhood gives
    an open convex cover near w, with its diameter scaled
    by r. These are supporting affine and metric calculations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerNormedTopology
  NormMetricScaleContinuity InnerConvex MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_positive_similarity_open]: openness
    of the translated thin convex generators in 3.2.26(2),
    p. 261. Positive scaling has the continuous inverse
    x maps to (x-a)/r. *)
Lemma euclidean_positive_similarity_open (R:realType) n
    (U:set (inner_metric_space (@euclidean_inner_productP R n))) (a:R_n R n) (r:R):
  0<r ->open U ->@open (inner_metric_space (@euclidean_inner_productP R n))
    ((fun x=>(a+r*:x)%R) @` U).
Proof.
move=>hr hU.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose F (x:X):X:=a+r*:x.
pose G (x:X):X:=r^-1*:(x-a).
have hNonzero:r!=0 by rewrite gt_eqF.
have hGF x:G (F x)=x.
  by rewrite /G /F addrAC subrr add0r scalerA mulVf // scale1r.
have hFG x:F (G x)=x.
  by rewrite /G /F scalerA mulfV // scale1r addrC subrK.
have hG:continuous G.
  apply:(@metric_fixed_lipschitz_continuous R X X G `|r^-1| (normr_ge0 _))=>x y.
  rewrite !inner_metric_distanceE /G -scalerBr inner_normZ.
  have hSubtract:(x-a)-(y-a)=x-y by rewrite opprB addrA subrK.
  by rewrite hSubtract.
have hImage:F @` U=G @^-1` U.
  apply/seteqP; split=>x.
  - move=>[y hy <-]; by rewrite /= hGF.
  - move=>hx; exists (G x); first exact hx; exact:hFG x.
change (@open X (F @` U)); rewrite hImage.
apply:open_comp hU=>x _; exact:hG.
Qed.

(** Source for [euclidean_similarity_convex]: convexity of
    the translated thin generators C(w,r), 3.2.26(2),
    p. 261. The affine map preserves every segment;
    this part also allows zero or negative scaling. *)
Lemma euclidean_similarity_convex (R:realType) n (U:set (R_n R n)) (a:R_n R n) (r:R):
  is_inner_convex U ->is_inner_convex ((fun x=>(a+r*:x)%R) @` U).
Proof.
move=>hU x y [u hu <-] [v hv <-] s hs0 hs1.
exists ((1-s)*:u+s*:v); first exact:hU u v hu hv s hs0 hs1.
symmetry.
rewrite !scalerDr !scalerA addrACA -scalerDl subrK scale1r.
by rewrite (mulrC r (1-s)) (mulrC r s).
Qed.

(** Source for [euclidean_positive_similarity_diameter_bound]:
    the small-diameter condition on C(w,r) in 3.2.26(2),
    p. 261. A unit neighbourhood of diameter at most
    d gives a generator of diameter at most r*d,
    retaining empty sets and dimension zero. *)
Lemma euclidean_positive_similarity_diameter_bound (R:realType) n
    (U:set (inner_metric_space (@euclidean_inner_productP R n))) (a:R_n R n) (r d:R):
  0<=r ->0<=d ->(extended_metric_diameter U<=d%:E)%E ->
  (@extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n)) ((fun x=>(a+r*:x)%R) @` U)<=(r*d)%:E)%E.
Proof.
move=>hr hd hU.
apply:(metric_diameter_least (extended_metric_diameter_specification _)).
- rewrite lee_fin; exact:mulr_ge0 hr hd.
- move=>x y [u hu <-] [v hv <-].
  have hOriginal:=le_trans (metric_diameter_upper (extended_metric_diameter_specification U) hu hv) hU.
  rewrite lee_fin inner_metric_distanceE in hOriginal.
  rewrite lee_fin inner_metric_distanceE.
  have hDifference:(a+r*:u)-(a+r*:v)=r*:(u-v).
    by rewrite opprD addrACA subrr add0r -scalerBr.
  rewrite hDifference inner_normZ (ger0_norm hr).
  exact (ler_wpM2l hr hOriginal).
Qed.
