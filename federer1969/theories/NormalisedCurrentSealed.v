(** Federer (1969), 4.1.7, p. 357: the
    original variation measure of a representable
    current and an auxiliary normalized multivector
    density. The original maximal ball-limit orienting
    field is defined separately. The public laws retain
    the literal scalar-test gauge of 4.1.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces
  CurrentIntegrationCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type NormalisedCurrentSignature.
(** Source for [measure]: the original Radon measure
    ||T||, defined here only for representable
    currents, Federer 4.1.7, p. 357. *)
Parameter measure:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T),set (current_domain R n U)->\bar R.
(** Source for [auxiliary_density]: an actual normalized
    density given by 4.1.5, used to prove the
    original ball formula in Federer 4.1.7,
    p. 357. This is not the maximal orienting field. *)
Parameter auxiliary_density:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T),current_domain R n U->exterior_power (R_n R n) m.
(** Source for [laws]: the original Radon representation,
    exact scalar-test gauge, mass-one almost-everywhere
    density and global unit bound, supporting Federer
    4.1.7, p. 357. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T),
  @is_normalised_current_representation R h2 n m U hU T
    (@measure R h2 n m U hU T hT) (@auxiliary_density R h2 n m U hU T hT).
End NormalisedCurrentSignature.
Module NormalisedCurrent:NormalisedCurrentSignature.
(** Source for [representation_data]: private existence
    witness from the actual original 4.1.5 theorem,
    supporting Federer 4.1.7, p. 357. The
    module signature hides this choice. *)
Definition representation_data (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T):=
  cid (@normalised_current_representation_exists R h2 n m U hU T hT).
(** Source for [measure]: seal the original Radon
    variation measure witness, supporting Federer
    4.1.7, p. 357. *)
Definition measure (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T):set (current_domain R n U)->\bar R:=
  projT1 (@representation_data R h2 n m U hU T hT).
(** Source for [auxiliary_density]: seal the normalized
    weak-density witness, supporting Federer 4.1.7,
    p. 357. Its pointwise values are not exposed. *)
Definition auxiliary_density (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T):current_domain R n U->exterior_power (R_n R n) m:=
  projT1 (cid (projT2 (@representation_data R h2 n m U hU T hT))).
(** Source for [laws]: the opaque witnesses satisfy
    the independently specified original Radon and
    gauge laws, supporting Federer 4.1.7, p. 357. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T):
  @is_normalised_current_representation R h2 n m U hU T
    (@measure R h2 n m U hU T hT) (@auxiliary_density R h2 n m U hU T hT).
Proof. exact:(projT2 (cid (projT2 (@representation_data R h2 n m U hU T hT)))). Qed.
End NormalisedCurrent.
