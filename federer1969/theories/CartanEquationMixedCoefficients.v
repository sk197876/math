(** Federer (1969), 3.4.5, p. 321: the
    three actual transverse Taylor coefficients of the
    adapted original surface equation, supporting the real
    coefficient proof of the cited analytic example. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness FlatExponentialSealed CartanSurfaceEquation CartanCoordinateGeometry
  CartanEquationFirstCoefficients AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section MixedCoefficients.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation j:=(Ordinal (isT:(1<3)%N)).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X R^o NX N hNX hN).

(** Source for [cartan_surface_mixed_coefficient]: the
    original equation has coefficients z at (2,0) and
    (0,2), and -a(z) at (3,0), on its original
    axis, supporting the example in 3.4.5, p. 321. *)
Definition cartan_surface_mixed_coefficient (p q:nat) (z:R):R:=
  (if ((p==2)&&(q==0))%N then z else 0)+
  (if ((p==0)&&(q==2))%N then z else 0)-
  (if ((p==3)&&(q==0))%N then FlatExponential.value (1-z) else 0).

(** Source for [cartan_surface_mixed_coefficient_line]: the
    actual first-coordinate coefficient restricted to an original
    second-coordinate line on the axis has precisely the
    displayed finite polynomial, supporting 3.4.5, p. 321. *)
Lemma cartan_surface_mixed_coefficient_line p (z t:R):
  cartan_surface_first_coefficient p
    (cartan_axis_point z+t*:(@coordinate_basis R 3 j))=
    \sum_(q<3) t^+q*:(cartan_surface_mixed_coefficient p q z:R^o).
Proof.
have [hAX [hAY hAZ]]:=@cartan_axis_point_coordinates R z.
have [hX [hY hZ]]:=cartan_second_coordinate_line (cartan_axis_point z) t.
rewrite hAX in hX;rewrite hAY add0r in hY;rewrite hAZ in hZ.
have hScale (a b:R):a*:(b:R^o)=a*b:=erefl _.
rewrite !big_ord_recl big_ord0 /=.
case:p=>[|[|[|[|p]]]];rewrite /cartan_surface_first_coefficient /cartan_surface_equation
  ?hX ?hY ?hZ /cartan_surface_mixed_coefficient /=;rewrite !hScale /bump /=;ring.
Qed.

(** Source for [cartan_surface_mixed_coefficient_laws]: every
    actual divided second-coordinate coefficient of an original
    first-coordinate coefficient has the stated sparse axis
    value, supporting the example in 3.4.5, p. 321.
    These are actual derivatives on z<1. *)
Theorem cartan_surface_mixed_coefficient_laws p q (c:X->R) (z:R):
  z<1 ->Coefficient U (cartan_surface_first_coefficient p) q (@coordinate_basis R 3 j) c ->
  c (cartan_axis_point z)=cartan_surface_mixed_coefficient p q z.
Proof.
move=>hz hc.
have hU:U (cartan_axis_point z) by rewrite /U /= (cartan_axis_point_coordinates z).2.2.
have hValue:=@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN U
  (cartan_surface_first_coefficient p) q (@coordinate_basis R 3 j) (cartan_axis_point z) c 3%N
  (fun k=>cartan_surface_mixed_coefficient p k z) 1 hU (cartan_surface_first_coefficient_analytic p) hc ltr01
  (fun t _=>cartan_surface_mixed_coefficient_line p z t).
have hPadding k:(if (k<3)%N then cartan_surface_mixed_coefficient p k z else 0)=
    cartan_surface_mixed_coefficient p k z.
  by case:k=>[|[|[|n]]];rewrite /cartan_surface_mixed_coefficient /= ?andbF ?add0r ?subrr ?oppr0.
by rewrite (hPadding q) in hValue.
Qed.
End MixedCoefficients.
