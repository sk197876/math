(** Federer (1969), 4.1.8, p. 360: the original
    pairings determine phi_S uniquely in the actual test
    space. The proof uses the earlier exterior-form pairing
    and original test extensionality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  AlternatingForms AlternatingPairing CurrentSpaces SmoothTestEvaluation
  CurrentCartesianDomain CurrentCartesianSliceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceUnique.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Variable A:set (R_n R m).
Variable B:set (R_n R n).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation DB := (@current_test_space R h2 n B hB j).

(** Source for [current_cartesian_slice_unique]: the displayed
    scalar pairings in Federer 4.1.8, p. 360 determine
    the actual linear slice operator uniquely. The output
    is compared on its original open domain B. *)
Theorem current_cartesian_slice_unique (S:CA) (H G:Hom DC DB):
  @is_current_cartesian_slice R h2 m n i j A B hA hB S H->
  @is_current_cartesian_slice R h2 m n i j A B hA hB S G->H=G.
Proof.
move=>hH hG;apply:hom_ext=>phi.
apply:(smooth_test_values_extensional (@current_smooth_space_laws R h2 n B hB j))=>b hb.
change (@current_test_value R h2 n B hB j (H phi) b=
  @current_test_value R h2 n B hB j (G phi) b).
apply:pairing_ext=>eta.
exact:(eq_trans (@hH phi b hb eta) (esym (@hG phi b hb eta))).
Qed.
End CurrentCartesianSliceUnique.
