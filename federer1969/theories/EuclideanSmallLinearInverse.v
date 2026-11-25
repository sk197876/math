(** Federer (1969), 3.1.23, p. 237: a differential
    uniformly closer than one to identity is invertible. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanLinearMaps NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_small_linear_inverse]: the linear
    inverse needed for the local openness of f in Federer
    3.1.23, p. 237. The norm inequality implies
    injectivity, and the proved finite-dimensional linear inverse
    supplies a bounded two-sided inverse, including dimension zero. *)
Lemma euclidean_small_linear_inverse (R:realType) n
    (D:Hom (R_n R n) (R_n R n)) c :
  c<1 -> (forall v,inner_norm (@euclidean_inner_productP R n) (D v-v)<=
    c*inner_norm (@euclidean_inner_productP R n) v) ->
  exists E:Hom (R_n R n) (R_n R n),
    norm_bounded_linear (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R n)) E /\ cancel D E /\ cancel E D.
Proof.
move=>hc hb.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hi:injective (hom_as_linear D).
  move=>x z heq.
  have hz:D (x-z)=0 by rewrite linearB heq subrr.
  have hh:N (x-z)<=c*N (x-z).
    have hh0:=hb (x-z); by rewrite hz sub0r inner_normN in hh0.
  have hn:0<=N (x-z):=inner_norm_nonnegative (@euclidean_inner_productP R n) (x-z).
  have hn0:N (x-z)=0 by nra.
  exact: subr0_eq (hN.2 _ hn0).
have [g [hDg hgD]]:=euclidean_linear_inverse hi.
exists (hom_of_linear g); split.
- exact (@norm_finite_linear_bounded R X X N N hN hN n
    (@coordinate_basis R n) (@coordinate_basisP R n) (hom_of_linear g)).
- by split.
Qed.
