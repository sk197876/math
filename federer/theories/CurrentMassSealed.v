(** Federer (1969), 4.1.7, p. 358: the
    opaque original current mass. Its independent
    supremum laws, rather than the existence
    witness, are public. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentMassUP CurrentMassExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentMassSignature.
(** Source for [value]: the original M(T),
    Federer 4.1.7, p. 358. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x),
  @current_space R h2 n U hU m->\bar R.
(** Source for [laws]: exactly the original
    unit-comass test supremum, Federer 4.1.7, p. 358. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
  (T:@current_space R h2 n U hU m),
  @is_current_mass R h2 n m U hU T (@value R h2 n m U hU T).
End CurrentMassSignature.
Module CurrentMass:CurrentMassSignature.
(** Source for [value]: hide the proved
    mass-supremum witness, supporting Federer
    4.1.7, p. 358. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m): \bar R:=
  projT1 (cid (@current_mass_exists R h2 n m U hU T)).
(** Source for [laws]: the hidden value
    satisfies the independent original mass law,
    supporting Federer 4.1.7, p. 358. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  @is_current_mass R h2 n m U hU T (@value R h2 n m U hU T).
Proof. exact:(projT2 (cid (@current_mass_exists R h2 n m U hU T))). Qed.
End CurrentMass.
