(** Federer (1969), 4.1.6, p. 354: existence
    of the original linear divergence map. The
    actual three earlier universal maps prove this
    existence; their composite is sealed separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom TensorUP TensorProduct TensorMaps HomTensor
  GrassmannAbbreviations FiniteCoordinates ExteriorGrading DivergenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [divergence_map_exists]: the original
    Hom-to-tensor-to-interior composite is a linear
    map, Federer 4.1.6, p. 354. *)
Theorem divergence_map_exists (R:realType) (h2:(1+1:R)!=0) n p:
  exists d:Hom (Hom (R_n R n) (exterior_power (R_n R n) p.+1))
      (exterior_power (R_n R n) p),
    forall L,is_divergence_value h2 L (d L).
Proof.
exists (hom_of_linear (linear_comp (@divergence_tensor_map R h2 n p)
  (linear_comp (@tensor_swap R (Hom (R_n R n) R^o) (exterior_power (R_n R n) p.+1))
    (@Hom_tensor R (R_n R n) (exterior_power (R_n R n) p.+1) _
      (@coordinate_basis R n) (@coordinate_basisP R n)))))=>L.
by [].
Qed.
