(** Federer (1969), 4.1.6, p. 353: the
    original Hom-to-tensor-to-wedge characterization.
    Use the proved finite-source isomorphism of
    1.1.4 and the actual product of 1.4.3;
    the omitted general item 1.1.3 is not needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom TensorUP TensorProduct Bilinear LinearBasis Annihilator
  FiniteDualDimension DualityAnnihilator HomTensor
  GrassmannAbbreviations FiniteCoordinates EuclideanScalarCoordinateMaps
  Alternating OneFormIdentification EuclideanCoordinateForms ScalarTensorContraction
  MixedAlternatingProduct ExteriorDifferentialSealed ExteriorDerivativeCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_dual_basis]: the
    original coordinate covectors are the actual dual
    basis used in 1.1.4, as recalled in
    Federer 4.1.6, p. 353. *)
Lemma euclidean_coordinate_dual_basis (R:realType) n (i:'I_n):
  dual_basis (@coordinate_basisP R n) i=@euclidean_scalar_coordinate_map R n i.
Proof.
apply:esym.
apply:(@biorthogonal_basis_unique R (R_n R n) n (@coordinate_basis R n)
  (@coordinate_basisP R n) (@euclidean_scalar_coordinate_map R n)).
by move=>j k; rewrite /euclidean_scalar_coordinate_map /= /coordinate_basis ffunE eq_sym.
Qed.

(** Source for [exterior_tensor_wedge_bilinear]: the
    original exterior multiplication induces a linear
    tensor map, Federer 4.1.6, p. 353. *)
Lemma exterior_tensor_wedge_bilinear (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R) m:
  bilinear (fun (a:Hom (R_n R n) R^o) (b:A_m (R_n R n) W m)=>
    mixed_form_product h2 (@scalar_action_bilinear R W) (one_form a) b).
Proof.
split.
- move=>b c a a'; rewrite (linearP (@one_form R (R_n R n) R^o)).
  exact:((@mixed_form_product_bilinear R h2 (R_n R n) R^o W W _ (@scalar_action_bilinear R W) 1 m).1).
- move=>a; exact:((@mixed_form_product_bilinear R h2 (R_n R n) R^o W W _ (@scalar_action_bilinear R W) 1 m).2).
Qed.

(** Source for [exterior_tensor_wedge]: the linear map
    induced by the original alternating product,
    Federer 4.1.6, p. 353. *)
Definition exterior_tensor_wedge (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R) m:
    {linear tensor_space (Hom (R_n R n) R^o) (A_m (R_n R n) W m)->A_m (R_n R n) W m.+1}:=
  tensor_lift (@exterior_tensor_wedge_bilinear R h2 n W m).

(** Source for [exterior_differential_tensor_characterization]:
    the last displayed composite on p. 353,
    Federer 4.1.6, with arbitrary vector
    coefficients, including degree and dimension zero. *)
Theorem exterior_differential_tensor_characterization (R:realType) (h2:(1+1:R)!=0)
    n (W:lmodType R) m (L:Hom (R_n R n) (A_m (R_n R n) W m)):
  @ExteriorDifferential.value R h2 n W m L=
    @exterior_tensor_wedge R h2 n W m (Hom_tensor (@coordinate_basisP R n) L).
Proof.
rewrite exterior_differential_coordinate_formula /Hom_tensor linear_sum.
apply:eq_bigr=>j _.
change (mixed_form_product h2 (@scalar_action_bilinear R W)
  (euclidean_coordinate_form j) (L (@coordinate_basis R n j))=
  @exterior_tensor_wedge R h2 n W m
    (tensor_inj (dual_basis (@coordinate_basisP R n) j) (L (@coordinate_basis R n j)))).
have hPure:@exterior_tensor_wedge R h2 n W m
    (tensor_inj (dual_basis (@coordinate_basisP R n) j) (L (@coordinate_basis R n j)))=
  mixed_form_product h2 (@scalar_action_bilinear R W)
    (one_form (dual_basis (@coordinate_basisP R n) j)) (L (@coordinate_basis R n j)).
  exact:tensor_liftE.
by rewrite hPure euclidean_coordinate_dual_basis.
Qed.
