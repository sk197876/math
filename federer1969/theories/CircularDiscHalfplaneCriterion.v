(** Federer (1969), 3.3.19, p. 302: actual
    meeting of an original child disc with a closed
    halfplane gives the precise cosine condition for its
    original cyclic index. The radius cancels by proved
    identities, not an extra angular hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  InnerProductUP Bilinear CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors
  CircularDiscRefinement InnerHalfplaneBallCentre.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Criterion.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).

(** Source for [circular_child_meets_halfplane]: original
    closed-disc meeting of the halfplane with unit normal u
    and boundary through z, as in 3.3.19, p. 302.
    Closed boundary contacts are explicitly included. *)
Definition circular_child_meets_halfplane (z u:E) (r:R) n (k:'I_n):Prop:=
  exists x:E,metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x /\
    0<=euclidean_inner_product u (x-z).

(** Source for [circular_disc_halfplane_cosine_bound]: actual
    halfplane intersection forces cos(2pi k/n-t)>=-1/(n-1),
    supporting the n/2+1 count in 3.3.19, p. 302.
    The original r, centre, index and orientation remain. *)
Lemma circular_disc_halfplane_cosine_bound (z:E) (r:R) n (k:'I_n) (t:R):
  0<r ->(4<=n)%N ->circular_child_meets_halfplane z (circular_unit_vector t) r k ->
  -(n%:R-1)^-1<=C (2* p* k%:R/n%:R-t).
Proof.
move=>hr hn [x [hx hHalf]].
have hCentre:=@inner_halfplane_ball_centre_bound R (R_n R 2)
  (@euclidean_inner_product R 2) (@euclidean_inner_productP R 2)
  (circular_unit_vector t) z (circular_disc_child_center z r k) x (r/n%:R)
  (@circular_unit_vector_norm R t) hx hHalf.
pose c:R:=(1-n%:R^-1)* r.
have hDifference:circular_disc_child_center z r k-z=
    c*:circular_unit_vector (2* p* k%:R/n%:R).
  by rewrite /circular_disc_child_center -/c addrAC subrr add0r.
rewrite hDifference (bilZr (inner_bilinear (@euclidean_inner_productP R 2)))
  circular_unit_vector_inner in hCentre.
have hAngle:t-2* p* k%:R/n%:R= -(2* p* k%:R/n%:R-t) by ring.
rewrite hAngle (circular_trig_cosine_even ht) in hCentre.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hNP:(0<n%:R:>R) by lra.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hNm1:(0<n%:R-1:>R) by lra.
have hNm1N:(n%:R-1:R)!= 0 by rewrite gt_eqF.
have hRadius:0<r/n%:R by rewrite divr_gt0.
have hScale:c=(r/n%:R)*(n%:R-1).
  have hBudget:(n%:R:R)*n%:R^-1= 1 by rewrite mulfV.
  rewrite /c;nra.
have hc:0<c by rewrite hScale;exact:mulr_gt0 hRadius hNm1.
have hCancel:c*(n%:R-1)^-1=r/n%:R by rewrite hScale -mulrA mulfV // mulr1.
rewrite -(ler_pM2l hc) mulrN hCancel.
exact:hCentre.
Qed.
End Criterion.
