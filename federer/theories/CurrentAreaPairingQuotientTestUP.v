(** Federer (1969), 4.1.25, p. 383: the scalar
    quotient for the original current action uses the
    target form evaluated at f(x). The auxiliary retains
    every actual differential point, including J_m f=0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ExteriorGrading AlternatingForms PartialFunctionUP PartialFunctionExtensionality
  CurrentAreaPairingQuotientUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_current_area_pairing_quotient_test]:
    the scalar quotient in the proof of the two displays
    of 4.1.25, p. 383, paired with the original
    variable target form. This independent graph uses
    its exact differentiability domain. *)
Definition is_current_area_pairing_quotient_test (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m)
    (q:partial_function (R_n R m) (extended_real_line R)) : Prop :=
  forall x z,partial_function_graph q x z <->
    exists D:Hom (R_n R m) (R_n R n),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT f x D /\
      (current_area_pairing_quotient_coefficient xi (phi (f x)) x D)%:E=z.

(** Source for [current_area_pairing_quotient_test_unique]:
    uniqueness of the auxiliary for the original target
    form in 4.1.25, p. 383, from its actual graph. *)
Theorem current_area_pairing_quotient_test_unique (R:realType) (m n:nat)
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m)
    (q p:partial_function (R_n R m) (extended_real_line R)) :
  is_current_area_pairing_quotient_test f xi phi q ->
  is_current_area_pairing_quotient_test f xi phi p -> q=p.
Proof.
move=>hQ hP;apply:partial_function_graph_extensionality=>x z.
by rewrite (hQ x z) (hP x z).
Qed.
