(** Federer (1969), 3.4.5, p. 321: the closed
    locally analytic example has no nonzero global analytic
    vanishing function. The adapted surface follows Cartan
    (1957), pp. 97–99; this proof uses real Taylor
    coefficients and the actual flat endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets ring.
From Federer Require Import RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormAnalyticUP CartanSurfaceUP CartanSurfaceSealed CartanCoordinateGeometry
  AnalyticDirectionalCoefficient CartanAxisCoefficientTransport CartanAxisClearedRemainders
  ClearedFlatCoefficientIndependence QuadraticSubstitutionParameterCoefficients QuadraticParameterInjectivity AnalyticDirectionalLineUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Rigidity.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation j:=(Ordinal (isT:(1<3)%N)).
Local Notation AN f:=(@norm_analytic R X R^o NX N hNX hN setT f).

(** Source for [cartan_global_analytic_vanisher_zero]: every
    actual globally real analytic function zero on the
    actual adapted proper surface is identically zero,
    proving the obstruction cited in 3.4.5, p. 321.
    Every axis coefficient is derived from actual derivatives;
    no rigidity or infinite quotient is assumed. *)
Theorem cartan_global_analytic_vanisher_zero (f:X->R):
  AN f ->(forall v,CartanSurface.set v ->f v=0) ->forall v,f v=0.
Proof.
move=>hf hZero.
have [C [P [hC [hP hAxis]]]]:=cartan_iterated_axis_coefficients_exist hf.
have hParameter parity (hParity:parity=0%N \/parity= 1%N) order ell z:
    quadratic_substitution_parameter_coefficient parity order ell
      (fun i k=>P i (2*k+parity)%N (cartan_axis_point z))=0.
  apply:(@cleared_flat_parameter_coefficients_zero R parity order
    (fun i k z=>P i (2*k+parity)%N (cartan_axis_point z))
    (fun i k=>hAxis i (2*k+parity)%N)).
  exact:(@cartan_axis_cleared_remainders_zero R f C P parity order hf hZero hC hP hParity).
have hCoefficients i k z:P i k (cartan_axis_point z)=0.
  apply:(@quadratic_parameter_coefficients_injective R (fun i k=>P i k (cartan_axis_point z))).
  exact:(fun parity hParity order ell=>hParameter parity hParity order ell z).
have hFirst i y z:C i (cartan_axis_point z+y*:(@coordinate_basis R 3 j))=0.
  apply:(@analytic_directional_line_zero R X NX hNX (C i) (P i) (cartan_axis_point z)
    (@coordinate_basis R 3 j) (hC i).2 (fun k=>(hP i k).1)).
  exact:(fun k=>hCoefficients i k z).
move=>v.
pose a:=cartan_axis_point (v ord_max)+(v j)*:(@coordinate_basis R 3 j).
have hLine:=@analytic_directional_line_zero R X NX hNX f C a (@coordinate_basis R 3 ord0)
  hf (fun i=>(hC i).1) (fun i=>hFirst i (v j) (v ord_max)) (v ord0).
have hPoint:a+(v ord0)*:(@coordinate_basis R 3 ord0)=v.
  apply/ffunP=>idx.
  have hCases:idx=ord0 \/idx=j \/idx=ord_max.
    case:idx=>idx hi;case:idx hi=>[|[|[|idx]]] hi.
    - left;apply:val_inj;reflexivity.
    - right;left;apply:val_inj;reflexivity.
    - right;right;apply:val_inj;reflexivity.
    - by [].
  case:hCases=>[->|[->|->]].
  - rewrite /a /cartan_axis_point /coordinate_basis !ffunE /=.
    change (v ord_max*0+v j*0+v ord0*1=v ord0).
    by rewrite !mulr0 mulr1 !add0r.
  - rewrite /a /cartan_axis_point /coordinate_basis !ffunE /=.
    change (v ord_max*0+v j*1+v ord0*0=v j).
    by rewrite !mulr0 mulr1 add0r addr0.
  - rewrite /a /cartan_axis_point /coordinate_basis !ffunE /=.
    change (v ord_max*1+v j*0+v ord0*0=v ord_max).
    by rewrite !mulr0 mulr1 !addr0.
by rewrite hPoint in hLine.
Qed.
End Rigidity.
