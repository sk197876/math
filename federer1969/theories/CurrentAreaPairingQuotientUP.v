(** Federer (1969), 4.1.25, p. 383: the scalar
    quotient used to apply the weighted area formula.
    This auxiliary quotient retains the full original
    differential domain, assigning scalar zero when its
    Jacobian is zero. The original normalized vector
    summand remains undefined at those points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ExteriorGrading ExteriorMaps AlternatingForms AlternatingPairing
  EuclideanLinearJacobian ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_area_pairing_quotient_coefficient]:
    the scalar paired numerator divided by J_m f
    in the area-formula proof of 4.1.25, p. 383.
    This auxiliary scalar is zero when the Jacobian
    vanishes; it does not redefine the vector summand. *)
Definition current_area_pairing_quotient_coefficient (R:realType) m n
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m) (x:R_n R m)
    (D:Hom (R_n R m) (R_n R n)) : R :=
  (@euclidean_linear_jacobian R m n m D)^-1 *
    pairing (exterior_power_map (hom_as_linear D) m (xi x)) a.

(** Source for [is_current_area_pairing_quotient]: the
    scalar auxiliary quotient has exactly the original
    differentiability domain in the proof of 4.1.25,
    p. 383, so it has a conull Lebesgue domain
    even if the critical set has positive measure. *)
Definition is_current_area_pairing_quotient (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m)
    (q:partial_function (R_n R m) (extended_real_line R)) : Prop :=
  forall x z,partial_function_graph q x z <->
    exists D:Hom (R_n R m) (R_n R n),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT f x D /\
      (current_area_pairing_quotient_coefficient xi a x D)%:E=z.

(** Source for [current_area_pairing_quotient_unique]:
    the actual differential determines one auxiliary scalar
    quotient in 4.1.25, p. 383. Original partial
    domains and their critical points remain unchanged. *)
Theorem current_area_pairing_quotient_unique (R:realType) (m n:nat)
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m)
    (q p:partial_function (R_n R m) (extended_real_line R)) :
  is_current_area_pairing_quotient f xi a q ->
  is_current_area_pairing_quotient f xi a p -> q=p.
Proof.
move=>hQ hP;apply:partial_function_graph_extensionality=>x z.
by rewrite (hQ x z) (hP x z).
Qed.
