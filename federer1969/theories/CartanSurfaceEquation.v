(** Federer (1969), 3.4.5, p. 321: actual
    defining equation and its nonzero coefficient on the
    analytic part z<1 of the adapted cited example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric NormDifferentialUP NormBoundedLinearTopology NormAnalyticUP NormAnalyticLocal
  NormAnalyticDomain NormAnalyticComposition NormAnalyticOperations EuclideanScalarCoordinateAnalytic
  FlatExponentialSealed CartanAxisCoordinate CartanSurfaceOffEndpoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Equation.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation AN f:=(@norm_analytic R X R^o NX N hNX hN U f).

(** Source for [cartan_surface_equation]: the exact actual
    adapted cubic equation, supporting the example cited
    in 3.4.5, p. 321. *)
Definition cartan_surface_equation (v:X):R:=
  v ord_max*((v ord0)^+2+(v (Ordinal (isT:(1<3)%N)))^+2)-
    (v ord0)^+3*FlatExponential.value (1-v ord_max).

(** Source for [cartan_inverse_coefficient_analytic]: the
    actual reciprocal coefficient is analytic on precisely
    the original lower domain z<1, supporting 3.4.5, p. 321. *)
Lemma cartan_inverse_coefficient_analytic:AN (fun v=>(FlatExponential.value (1-v ord_max))^-1).
Proof.
have hComposite:=norm_analytic_composition (@euclidean_scalar_coordinate_analytic R 3 ord_max)
  (@cartan_axis_inverse_coefficient_analytic R).
move=>v hv;apply:(norm_analytic_at_domain_enlargement _ (hComposite v (conj Logic.I hv))).
by move=>w [_ hw].
Qed.

(** Source for [cartan_lower_domain_interior]: the actual
    analytic domain z<1 is open, supporting 3.4.5, p. 321. *)
Lemma cartan_lower_domain_interior v:U v ->norm_domain_interior NX U v.
Proof.
move=>hv;apply:(@norm_domain_interior_neighbourhood R X NX hNX U v).2.
exact:(open_nbhs_nbhs (conj (norm_analytic_domain_open cartan_inverse_coefficient_analytic) hv)).
Qed.

(** Source for [cartan_surface_original_equation_analytic]:
    the actual original surface equation is analytic on
    z<1, supporting the cited example in 3.4.5, p. 321. *)
Lemma cartan_surface_original_equation_analytic:AN cartan_surface_equation.
Proof.
apply:(norm_analytic_open_restriction _ cartan_lower_domain_interior
  (@cartan_surface_equation_off_endpoint R))=>v hv.
change (is_true (v ord_max!=1));by rewrite lt_eqF.
Qed.
End Equation.
