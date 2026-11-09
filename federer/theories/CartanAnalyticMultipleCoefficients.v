(** Federer (1969), 3.4.5, p. 321: actual
    transverse coefficients of an analytic multiple of the
    original adapted surface equation in the cited example. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormAnalyticUP FlatExponentialSealed CartanSurfaceEquation CartanCoordinateGeometry
  CartanEquationFirstCoefficients CartanEquationMixedCoefficients CartanEquationMixedFields
  CartanSparseCoefficientConvolution AnalyticDirectionalCoefficient AnalyticIteratedCoefficientProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section MultipleCoefficients.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation j:=(Ordinal (isT:(1<3)%N)).
Local Notation AN f:=(@norm_analytic R X R^o NX N hNX hN U f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X R^o NX N hNX hN).

(** Source for [cartan_analytic_multiple_coefficient]: actual
    iterated Taylor coefficients of an analytic surface-equation
    multiple obey the exact two quadratic and one cubic
    shift identity, supporting 3.4.5, p. 321.
    Every quotient coefficient is an actual analytic differential. *)
Theorem cartan_analytic_multiple_coefficient (q:X->R) (C:nat->X->R) (P:nat->nat->X->R)
    i k (E H:X->R) (z:R):
  AN q ->(forall r,Coefficient U q r (@coordinate_basis R 3 ord0) (C r)) ->
  (forall r s,Coefficient U (C r) s (@coordinate_basis R 3 j) (P r s)) ->
  Coefficient U (fun v=>q v*cartan_surface_equation v) i (@coordinate_basis R 3 ord0) E ->
  Coefficient U E k (@coordinate_basis R 3 j) H ->z<1 ->
  H (cartan_axis_point z)=
    z*(if (2<=i)%N then P (i-2)%N k (cartan_axis_point z) else 0)+
    z*(if (2<=k)%N then P i (k-2)%N (cartan_axis_point z) else 0)-
    FlatExponential.value (1-z)*(if (3<=i)%N then P (i-3)%N k (cartan_axis_point z) else 0).
Proof.
move=>hq hC hP hE hH hz.
have [Q hQ]:=@cartan_equation_mixed_fields_exist R.
have hU:U (cartan_axis_point z) by rewrite /U /= (cartan_axis_point_coordinates z).2.2.
have hProduct:=@analytic_iterated_coefficient_product R X NX hNX U q (@cartan_surface_equation R)
  (@coordinate_basis R 3 ord0) (@coordinate_basis R 3 j) (cartan_axis_point z)
  C (@cartan_surface_first_coefficient R) P Q i k E H hU hq (@cartan_surface_original_equation_analytic R)
  hC (@cartan_surface_first_coefficient_laws R) (fun r s=>hP r s) (fun r s=>(hQ r s).1) hE hH.
have hValues:(\sum_(r<i.+1) \sum_(s<k.+1) P (i-r)%N (k-s)%N (cartan_axis_point z)*Q r s (cartan_axis_point z))=
    \sum_(r<i.+1) \sum_(s<k.+1) P (i-r)%N (k-s)%N (cartan_axis_point z)*cartan_surface_mixed_coefficient r s z.
  apply:eq_bigr=>r _;apply:eq_bigr=>s _;by rewrite ((hQ r s).2.2 z hz).
rewrite hProduct hValues.
exact:(@cartan_sparse_coefficient_convolution R (fun r s=>P r s (cartan_axis_point z)) i k z).
Qed.
End MultipleCoefficients.
