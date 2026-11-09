(** Federer (1969), 3.4.5, p. 321: actual
    first-coordinate Taylor coefficients of the adapted surface
    equation in the real proof of the cited example. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormAnalyticUP FlatExponentialSealed CartanSurfaceEquation CartanCoordinateGeometry
  AnalyticDirectionalCoefficient AnalyticDirectionalCoefficientAgreement AnalyticDirectionalPolynomialLine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficients.
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

(** Source for [cartan_surface_first_coefficient]: the
    four finite first-coordinate coefficients of the original
    cubic equation, supporting 3.4.5, p. 321. *)
Definition cartan_surface_first_coefficient (i:nat) (v:X):R:=
  match i with
  | 0%N=>cartan_surface_equation v
  | 1%N=>2*v ord_max*v ord0-3*FlatExponential.value (1-v ord_max)*(v ord0)^+2
  | 2%N=>v ord_max-3*FlatExponential.value (1-v ord_max)*v ord0
  | 3%N=>-FlatExponential.value (1-v ord_max)
  | _=>0
  end.

(** Source for [cartan_surface_first_coefficient_line]: the
    actual translated cubic equals its displayed finite
    first-coordinate polynomial for every real increment,
    supporting the example cited in 3.4.5, p. 321. *)
Lemma cartan_surface_first_coefficient_line (v:X) (t:R):
  cartan_surface_equation (v+t*:(@coordinate_basis R 3 ord0))=
    \sum_(i<4) t^+i*:(cartan_surface_first_coefficient i v:R^o).
Proof.
have [hX [hY hZ]]:=cartan_first_coordinate_line v t.
rewrite /cartan_surface_equation hX hY hZ !big_ord_recl big_ord0 /=
  /cartan_surface_first_coefficient /cartan_surface_equation.
change (v ord_max*((v ord0+t)^+2+(v j)^+2)-(v ord0+t)^+3*FlatExponential.value (1-v ord_max)=
  t^+0*(v ord_max*((v ord0)^+2+(v j)^+2)-(v ord0)^+3*FlatExponential.value (1-v ord_max))+
  (t^+1*(2*v ord_max*v ord0-3*FlatExponential.value (1-v ord_max)*(v ord0)^+2)+
  (t^+2*(v ord_max-3*FlatExponential.value (1-v ord_max)*v ord0)+
  (t^+3*(-FlatExponential.value (1-v ord_max))+0)))).
ring.
Qed.

(** Source for [cartan_surface_first_coefficient_laws]: each
    displayed finite coefficient is the actual divided
    differential in the original first-coordinate direction,
    supporting 3.4.5, p. 321. Finite orders above
    three give zero by actual Taylor uniqueness. *)
Theorem cartan_surface_first_coefficient_laws i:
  Coefficient U (@cartan_surface_equation R) i (@coordinate_basis R 3 ord0)
    (cartan_surface_first_coefficient i).
Proof.
have hf:=@cartan_surface_original_equation_analytic R.
have [c [hc hAnalyticC]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN U
  (@cartan_surface_equation R) i (@coordinate_basis R 3 ord0) hf.
move=>v hv z hz.
have hValue:=@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN U
  (@cartan_surface_equation R) i (@coordinate_basis R 3 ord0) v c 4%N
  (fun k=>cartan_surface_first_coefficient k v) 1 hv hf hc ltr01
  (fun t _=>cartan_surface_first_coefficient_line v t).
have hPadding k (w:X):(if (k<4)%N then cartan_surface_first_coefficient k w else 0)=
    cartan_surface_first_coefficient k w.
  by case:k=>[|[|[|[|n]]]].
rewrite (hPadding i v) in hValue;rewrite -hValue;exact:(hc v hv z hz).
Qed.

(** Source for [cartan_surface_first_coefficient_analytic]:
    every original first-coordinate coefficient is analytic
    on z<1, supporting 3.4.5, p. 321. *)
Lemma cartan_surface_first_coefficient_analytic i:AN (cartan_surface_first_coefficient i).
Proof.
exact:(@analytic_directional_coefficient_analytic R X R^o NX N hNX hN U
  (@cartan_surface_equation R) i (@coordinate_basis R 3 ord0) (cartan_surface_first_coefficient i)
  (@cartan_surface_original_equation_analytic R) (@cartan_surface_first_coefficient_laws i)).
Qed.
End Coefficients.

Arguments cartan_surface_first_coefficient {R} i v.
Arguments cartan_surface_first_coefficient_laws {R} i.
Arguments cartan_surface_first_coefficient_analytic {R} i.
