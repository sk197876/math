(** Federer (1969), 3.3.19, p. 302: exact
    minimum between original child centres, proved for
    every positive parent radius and n>=4. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric CircularTrigonometrySealed
  CircularUnitVectors CircularRegularDirections CircularRegularMinimum CircularDiscRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Centres.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_disc_centre_distance_scale]:
    the original child-centre distances scale the actual
    unit cyclic distances by (1-1/n)r, supporting
    the first displayed minimum in 3.3.19, p. 302. *)
Lemma circular_disc_centre_distance_scale (z:E) (r:R) n (k l:'I_n):
  0<r ->(4<=n)%N ->
  mdist (circular_disc_child_center z r k) (circular_disc_child_center z r l)=
    ((1-n%:R^-1)* r)*mdist (@circular_regular_direction R n k) (@circular_regular_direction R n l).
Proof.
move=>hr hn.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hNP:(0<n%:R:>R) by lra.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hInv:(0<n%:R^-1:>R) by rewrite invr_gt0.
have hCancel:(n%:R:R)*n%:R^-1= 1 by rewrite mulfV.
have hOne:(0<1-n%:R^-1:>R) by nra.
have hScale:0<=((1-n%:R^-1)* r) by exact:ltW (mulr_gt0 hOne hr).
rewrite !inner_metric_distanceE /circular_disc_child_center /circular_regular_direction.
have hDifference:
  (z+((1-n%:R^-1)* r)*:circular_unit_vector (2* p* k%:R/n%:R))-
  (z+((1-n%:R^-1)* r)*:circular_unit_vector (2* p* l%:R/n%:R))=
  ((1-n%:R^-1)* r)*:(circular_unit_vector (2* p* k%:R/n%:R)-circular_unit_vector (2* p* l%:R/n%:R)).
  by rewrite opprD addrACA subrr add0r -scalerBr.
by rewrite hDifference inner_normZ (ger0_norm hScale).
Qed.

(** Source for [circular_disc_centre_minimum]: every two
    distinct original child centres are separated by at
    least 2(1-1/n)r sin(pi/n), 3.3.19, p. 302. *)
Lemma circular_disc_centre_minimum (z:E) (r:R) n (k l:'I_n):
  0<r ->(4<=n)%N ->k!=l ->
  2*((1-n%:R^-1)* r)* S (p/n%:R)<=
    mdist (circular_disc_child_center z r k) (circular_disc_child_center z r l).
Proof.
move=>hr hn hne;rewrite (@circular_disc_centre_distance_scale z r n k l hr hn).
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hNP:(0<n%:R:>R) by lra.
have hInv:(0<n%:R^-1:>R) by rewrite invr_gt0.
have hCancel:(n%:R:R)*n%:R^-1= 1 by rewrite mulfV // gt_eqF.
have hOne:(0<1-n%:R^-1:>R) by nra.
have hScale:0<=((1-n%:R^-1)* r):=ltW (mulr_gt0 hOne hr).
have hPair:=@circular_regular_pair_distance R n k l (leq_trans (erefl true : (2<=4)%N) hn) hne.
have hScaled:=ler_wpM2l hScale hPair;nra.
Qed.

(** Source for [circular_disc_centre_minimum_attained]:
    original adjacent children attain the displayed minimum
    centre distance, 3.3.19, p. 302. The actual
    original indices, not an abstract packing, are used. *)
Lemma circular_disc_centre_minimum_attained (z:E) (r:R) n:
  0<r ->(4<=n)%N ->exists k l:'I_n,k!=l /\
  mdist (circular_disc_child_center z r k) (circular_disc_child_center z r l)=
    2*((1-n%:R^-1)* r)* S (p/n%:R).
Proof.
move=>hr hn;have [k [l [hKL hDistance]]]:=@circular_regular_minimum_attained R n
  (leq_trans (erefl true : (2<=4)%N) hn).
exists k,l;split=>//.
by rewrite (@circular_disc_centre_distance_scale z r n k l hr hn) hDistance;ring.
Qed.
End Centres.
