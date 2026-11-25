(** Federer (1969), 4.1.6, pp. 351–352: the original
    coordinate functions have the constant one-form
    differentials X_j. Their increasing alternating
    products and the standard exterior words are dual. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP ExteriorIndices GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness EuclideanScalarCoordinateMaps NormDifferentialUP NormDifferentialLinear
  NormOpenDomainLaws AlternatingForms AlternatingPairing OneFormIdentification
  CovectorProducts GrassmannCoordinates FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_form]: the constant
    one-covector X_j=DX_j, Federer 4.1.6,
    p. 351, using the actual earlier coordinate map. *)
Definition euclidean_coordinate_form (R:realType) n (i:'I_n):A_m (R_n R n) R^o 1:=
  one_form (@euclidean_scalar_coordinate_map R n i).
Arguments euclidean_coordinate_form {R n} i.

(** Source for [euclidean_coordinate_form_dual]: the
    original coordinate covectors and standard vectors
    are dual bases, Federer 4.1.6, p. 351. *)
Lemma euclidean_coordinate_form_dual (R:realType) n (i j:'I_n):
  euclidean_coordinate_form i [tuple @coordinate_basis R n j]=if i==j then 1 else 0.
Proof. by rewrite /euclidean_coordinate_form one_formE /euclidean_scalar_coordinate_map /= /coordinate_basis ffunE eq_sym. Qed.

(** Source for [euclidean_coordinate_original_differential]:
    DX_j(x)=X_j at every x, Federer 4.1.6,
    p. 351. The graph is the actual norm
    differential; no differential identity is assumed. *)
Theorem euclidean_coordinate_original_differential (R:realType) n (i:'I_n) (x:R_n R n):
  has_norm_differential (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|)
    (fun _=>True) (@euclidean_scalar_coordinate_map R n i) x (@euclidean_scalar_coordinate_map R n i).
Proof.
apply:(norm_differential_linear (inner_norm_real_norm (@euclidean_inner_productP R n))
  (@scalar_absolute_value_norm R) (@norm_full_domain_interior R _ _ x)).
exact:euclidean_scalar_coordinate_bounded.
Qed.

(** Source for [euclidean_coordinate_products_dual]: the
    two original increasing product families are dual
    bases, Federer 4.1.6, pp. 351–352,
    by the already proved 1.4.3 pairing. *)
Theorem euclidean_coordinate_products_dual (R:realType) (h2:(1+1:R)!=0) n m
    (lambda mu:Lambda n m):
  pairing (e_lambda (@coordinate_basis R n) (val lambda))
    (@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m mu)=
      if mu==lambda then 1 else 0.
Proof. exact:(pairing_e_omega h2 (@euclidean_coordinate_form_dual R n)). Qed.

(** Source for [euclidean_real_form_coordinate_expansion]:
    the original sum phi=sum_lambda <e_lambda,phi> DX_lambda,
    Federer 4.1.6, p. 352, follows from 1.4.3
    and retains every exterior degree. *)
Theorem euclidean_real_form_coordinate_expansion (R:realType) (h2:(1+1:R)!=0) n m
    (phi:A_m (R_n R n) R^o m):
  phi=\sum_(lambda:Lambda n m)
    pairing (e_lambda (@coordinate_basis R n) (val lambda)) phi *:
      (@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m lambda).
Proof.
exact:(@covector_Grassmann_expansion R h2 (R_n R n) n m (@coordinate_basis R n)
  (@euclidean_coordinate_form R n) (@coordinate_basisP R n) (@euclidean_coordinate_form_dual R n) phi).
Qed.
