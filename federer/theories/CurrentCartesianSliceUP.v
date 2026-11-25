(** Federer (1969), 4.1.8, p. 360: independent
    specification of the original phi_S. Its values are
    defined by applying S to the actual first-variable
    test. Continuity of this linear map is a separate theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap ExteriorGrading
  AlternatingForms AlternatingPairing CurrentSpaces CurrentCartesianDomain
  CurrentCartesianSliceTestSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation Y := (R_n R n).
Variable A:set (R_n R m).
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation slice := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

(** Source for [is_current_cartesian_slice]: the displayed
    characterisation of phi_S by every eta, every b in B
    and the original first-variable S action, Federer 4.1.8,
    p. 360. Existence, smooth parameter dependence and continuity
    are conclusions to prove, not assumptions of this definition. *)
Definition is_current_cartesian_slice (S:CA) (H:Hom DC DB):Prop:=
  forall phi b (hb:B b) (eta:exterior_power Y j),
    pairing eta (@current_test_value R h2 n B hB j (H phi) b)=
      @current_value R h2 m A hA i S (slice b hb eta phi).
End CurrentCartesianSliceUP.
