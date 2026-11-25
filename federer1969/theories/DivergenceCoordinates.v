(** Federer (1969), 4.1.6, p. 354: the
    original coordinate formula for divergence follows
    from its independently specified tensor composite.
    Input degree is written p+1; every positive
    original degree is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom TensorUP TensorProduct TensorMaps HomTensor FiniteDualDimension
  GrassmannAbbreviations FiniteCoordinates Alternating OneFormIdentification
  EuclideanCoordinateForms ExteriorDifferentialTensor LeftInterior OneCovectorInterior
  DivergenceUP DivergenceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [divergence_coordinate_formula]:
    div xi=sum_j D_j xi contracted by DX_j,
    Federer 4.1.6, p. 354, with the
    actual original coordinate covectors. *)
Theorem divergence_coordinate_formula (R:realType) (h2:(1+1:R)!=0) n p
    (L:Hom (R_n R n) (exterior_power (R_n R n) p.+1)):
  @Divergence.value R h2 n p L=
    \sum_(j:'I_n) positive_one_covector_interior h2
      (L (@coordinate_basis R n j)) (euclidean_coordinate_form j).
Proof.
have hValue:=@Divergence.laws R h2 n p L.
rewrite /is_divergence_value /Hom_tensor in hValue.
apply:eq_trans hValue _.
have hSwap:
  @tensor_swap R (Hom (R_n R n) R^o) (exterior_power (R_n R n) p.+1) (\sum_(j:'I_n) tensor_inj (dual_basis (@coordinate_basisP R n) j)
      (L (@coordinate_basis R n j)))=
    \sum_(j:'I_n) tensor_inj (L (@coordinate_basis R n j))
      (dual_basis (@coordinate_basisP R n) j).
  rewrite linear_sum; apply:eq_bigr=>j _; exact:tensor_swapE.
rewrite hSwap linear_sum.
apply:eq_bigr=>j _.
change (@divergence_tensor_map R h2 n p
  (tensor_inj (L (@coordinate_basis R n j)) (dual_basis (@coordinate_basisP R n) j))=
  positive_one_covector_interior h2 (L (@coordinate_basis R n j)) (euclidean_coordinate_form j)).
have hPure:@divergence_tensor_map R h2 n p
    (tensor_inj (L (@coordinate_basis R n j)) (dual_basis (@coordinate_basisP R n) j))=
  positive_one_covector_interior h2 (L (@coordinate_basis R n j))
    (one_form (dual_basis (@coordinate_basisP R n) j)).
  exact:tensor_liftE.
by rewrite hPure euclidean_coordinate_dual_basis.
Qed.
