(** Federer (1969), 4.1.8, p. 360: the displayed
    pairings define an actual covector at each b in B.
    This supporting algebraic existence result reuses the original
    exterior-form identification of 1.4.1, p. 17. Smoothness
    and compact support of the output field remain to prove. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap ExteriorGrading
  AlternatingForms AlternatingIsomorphism AlternatingPairing CurrentSpaces
  CurrentCartesianDomain CurrentCartesianSliceTestSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSlicePoint.
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
Local Notation DA := (@current_test_space R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

(** Source for [current_cartesian_slice_point_exists]: the
    original S action on the actual first-variable slice
    determines a covector phi_S(b), supporting Federer 4.1.8,
    p. 360. This statement concerns every current S and
    requires no integral representation or separability premise. *)
Theorem current_cartesian_slice_point_exists (S:CA) (phi:DC) b (hb:B b):
  exists theta:A_m Y R^o j,forall eta,
    pairing eta theta=@current_value R h2 m A hA i S (F b hb eta phi).
Proof.
have hF:=@CartesianSliceTest.laws R h2 m n A B hA hB i j.
pose L:=@HomMap R (exterior_power Y j) DA (fun eta=>F b hb eta phi)
  (introT (asboolP _) (((@hF b hb).1).1 phi)).
pose H:=hom_comp (@current_value R h2 m A hA i S) L.
exists (hom_to_form H)=>eta.
exact:(@pairing_hom_identification R Y R^o j eta H).
Qed.

(** Source for [current_cartesian_slice_point_unique]: all
    original eta pairings determine the covector phi_S(b)
    uniquely, supporting Federer 4.1.8, p. 360, by the
    original exterior-form pairing in 1.4.1, p. 17. *)
Theorem current_cartesian_slice_point_unique (S:CA) (phi:DC) b (hb:B b)
    (theta omega:A_m Y R^o j):
  (forall eta,pairing eta theta=@current_value R h2 m A hA i S (F b hb eta phi))->
  (forall eta,pairing eta omega=@current_value R h2 m A hA i S (F b hb eta phi))->
  theta=omega.
Proof.
move=>hTheta hOmega;apply:pairing_ext=>eta.
exact:(eq_trans (hTheta eta) (esym (hOmega eta))).
Qed.
End CurrentCartesianSlicePoint.
