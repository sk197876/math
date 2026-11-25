(** Federer (1969), 4.1.6, p. 354: the
    original relation between exterior and interior
    differentiation, including the sign (-1)^(n-p).
    The duality top form and coordinate fields are
    the actual original Euclidean choices. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear ExteriorIndices CovectorProducts GrassmannCoordinates Alternating AlternatingProduct
  ScalarCoefficients GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateForms
  ScalarTensorContraction MixedAlternatingProduct MixedOrdinaryFormProduct
  DualityMaps FormDualityContraction OneCovectorInterior
  ExteriorDifferentialSealed ExteriorDerivativeCoordinates DivergenceSealed DivergenceCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_differential_duality_divergence]:
    d(D_p xi)=(-1)^(n-p) D_(p-1)(div xi),
    Federer 4.1.6, p. 354, at the
    level of the actual first differential. Equal
    result degrees are identified in A^*. *)
Theorem exterior_differential_duality_divergence (R:realType) (h2:(1+1:R)!=0)
    n p (hp:(p.+1<=n)%N)
    (L:Hom (R_n R n) (exterior_power (R_n R n) p.+1)):
  let volume:=@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) n (Lambda_top n) in
  form_include (@ExteriorDifferential.value R h2 n R^o (n-p.+1)
    (hom_comp (hom_of_linear (@D_p R (R_n R n) n volume p.+1 hp)) L))=
    (-1:R)^+(n-p.+1)*:form_include
      (D_p volume (leq_trans (leqnSn p) hp) (@Divergence.value R h2 n p L)).
Proof.
move=>volume.
rewrite exterior_differential_coordinate_formula divergence_coordinate_formula !linear_sum.
apply:eq_bigr=>j _.
change (form_include (mixed_form_product h2 (@scalar_action_bilinear R R^o)
    (euclidean_coordinate_form j) (D_p volume hp (L (@coordinate_basis R n j))))=
  (-1:R)^+(n-p.+1)*:form_include
    (D_p volume (leq_trans (leqnSn p) hp)
      (positive_one_covector_interior h2 (L (@coordinate_basis R n j)) (euclidean_coordinate_form j)))).
rewrite mixed_real_form_product form_wedge_include.
have hComm:=@alternating_wedge_anticommutative R h2 (R_n R n) R^o _ (scalar_bilinear R)
  (@mulrC R) 1 (n-p.+1)%N (form_include (euclidean_coordinate_form j))
  (form_include (D_p volume hp (L (@coordinate_basis R n j))))
  (form_include_homogeneous (euclidean_coordinate_form j))
  (form_include_homogeneous (D_p volume hp (L (@coordinate_basis R n j)))).
rewrite mul1n in hComm; rewrite hComm.
congr (_*: _).
rewrite -form_wedge_include.
exact:(@duality_one_covector_contraction R h2 (R_n R n) n (@coordinate_basis R n)
  (@euclidean_coordinate_form R n) (@coordinate_basisP R n) (@euclidean_coordinate_form_dual R n)
  p hp (L (@coordinate_basis R n j)) (euclidean_coordinate_form j)).
Qed.
