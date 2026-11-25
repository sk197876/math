(** Federer (1969), 3.4.8(1), p. 326:
    the original coordinate germ image is a subring.
    Its independent image membership laws and the actual
    ring homomorphism prove every closure property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticGermUP AnalyticGermRing
  CommutativeSubringUP AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RingLaws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Variable j:nat.
Hypothesis hjn:(j<=n)%N.
Local Notation Y:=(R_n R j).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R j)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R j)).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega j hjn).
Local Notation p:=(@AnalyticPrefixCoordinates.projection R X n omega j hjn).


(** Source for [analytic_prefix_germ_subring_laws]: zero,
    one, addition, negation, and multiplication belong to
    the original Q_j, 3.4.8(1), p. 326. *)
Theorem analytic_prefix_germ_subring_laws:
  is_commutative_subring (@analytic_prefix_germ_subring R X NX hNX n e he omega j hjn).
Proof.
constructor.
- apply/analytic_prefix_germ_subring_membership;exists 0;exact:rmorph0.
- apply/analytic_prefix_germ_subring_membership;exists 1;exact:rmorph1.
- move=>alpha beta /analytic_prefix_germ_subring_membership[x <-]
    /analytic_prefix_germ_subring_membership[y <-].
  apply/analytic_prefix_germ_subring_membership;exists (x+y);exact:rmorphD.
- move=>alpha /analytic_prefix_germ_subring_membership[x <-].
  apply/analytic_prefix_germ_subring_membership;exists (-x);exact:rmorphN.
- move=>alpha beta /analytic_prefix_germ_subring_membership[x <-]
    /analytic_prefix_germ_subring_membership[y <-].
  apply/analytic_prefix_germ_subring_membership;exists (x*y);exact:rmorphM.
Qed.
End RingLaws.
