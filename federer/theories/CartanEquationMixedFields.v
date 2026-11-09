(** Federer (1969), 3.4.5, p. 321: actual
    analytic representative fields for the original surface's
    transverse coefficients in the cited counterexample proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormAnalyticUP CartanCoordinateGeometry CartanEquationFirstCoefficients
  CartanEquationMixedCoefficients AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cartan_equation_mixed_fields_exist]: every
    actual second-coordinate coefficient field of the original
    first-coordinate coefficient exists analytically, and has
    the proved original sparse axis values, supporting
    3.4.5, p. 321. All representatives remain local. *)
Theorem cartan_equation_mixed_fields_exist (R:realType):
  exists Q:nat->nat->R_n R 3->R,forall r s,
    @is_analytic_directional_coefficient R (R_n R 3) R^o
      (inner_norm (@euclidean_inner_productP R 3)) (fun t=>`|t|)
      (inner_norm_real_norm (@euclidean_inner_productP R 3)) (@scalar_absolute_value_norm R)
      [set v|v ord_max<1] (cartan_surface_first_coefficient r) s
      (@coordinate_basis R 3 (Ordinal (isT:(1<3)%N))) (Q r s) /\
    @norm_analytic R (R_n R 3) R^o (inner_norm (@euclidean_inner_productP R 3)) (fun t=>`|t|)
      (inner_norm_real_norm (@euclidean_inner_productP R 3)) (@scalar_absolute_value_norm R)
      [set v|v ord_max<1] (Q r s) /\
    forall z:R,z<1 ->Q r s (cartan_axis_point z)=cartan_surface_mixed_coefficient r s z.
Proof.
pose X:=R_n R 3.
pose NX:=inner_norm (@euclidean_inner_productP R 3).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3).
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose U:=[set v:X|v ord_max<1].
have hex (rs:nat*nat):exists c:X->R,
    @is_analytic_directional_coefficient R X R^o NX N hNX hN U
      (cartan_surface_first_coefficient rs.1) rs.2 (@coordinate_basis R 3 (Ordinal (isT:(1<3)%N))) c /\
    @norm_analytic R X R^o NX N hNX hN U c.
  exact:(@analytic_directional_coefficient_exists R X R^o NX N hNX hN U
    (cartan_surface_first_coefficient rs.1) rs.2 (@coordinate_basis R 3 (Ordinal (isT:(1<3)%N)))
    (cartan_surface_first_coefficient_analytic rs.1)).
have [Q hQ]:=choice hex.
exists (fun r s=>Q (r,s))=>r s.
have [hc hAnalytic]:=hQ (r,s);split;first exact:hc.
split;first exact:hAnalytic.
move=>z hz;exact:(@cartan_surface_mixed_coefficient_laws R r s (Q (r,s)) z hz hc).
Qed.
