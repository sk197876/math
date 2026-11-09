(** Federer (1969), 3.4.5, p. 321, citing Cartan
    (1957), p. 97: off the flat plane the actual
    surface is given by its single original analytic equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetric NormDifferentialUP NormBoundedLinearTopology NormAnalyticUP NormAnalyticLocal NormAnalyticDomain
  NormAnalyticComposition NormAnalyticOperations NormAnalyticScalarProducts EuclideanScalarCoordinateAnalytic
  FlatExponentialSealed CartanCoefficientAnalytic CartanSurfaceUP CartanSurfaceSealed FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OffEndpoint.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max!=1]).
Local Notation AN f:=(@norm_analytic R X R^o NX N hNX hN U f).

(** Source for [cartan_surface_coefficient_off_endpoint]:
    the actual composed coefficient a(z) is analytic off
    the flat plane, supporting 3.4.5, p. 321. *)
Lemma cartan_surface_coefficient_off_endpoint:AN (fun v=>FlatExponential.value (1-v ord_max)).
Proof.
have hCoordinate:=@euclidean_scalar_coordinate_analytic R 3 ord_max.
have hComp:=@norm_analytic_composition R X R^o R^o NX N N hNX hN hN
  setT [set z|z!=1] (fun v=>v ord_max) (fun z=>FlatExponential.value (1-z))
  hCoordinate (@cartan_coefficient_off_endpoint_analytic R).
move=>a ha;apply:(@norm_analytic_at_domain_enlargement R X R^o NX N hNX hN
  (fun v=>setT v /\ v ord_max!=1) U _ a (fun v hv=>hv.2) (hComp a (conj Logic.I ha))).
Qed.

(** Source for [cartan_surface_off_endpoint_open]: the
    original equation domain is open, supporting the actual
    local varieties in the example cited at 3.4.5, p. 321. *)
Lemma cartan_surface_off_endpoint_open:@open (real_norm_metric_space hNX) U.
Proof. exact:(norm_analytic_domain_open cartan_surface_coefficient_off_endpoint). Qed.

(** Source for [cartan_surface_equation_off_endpoint]: the
    actual cubic equation is analytic on its original domain,
    supporting the example cited in 3.4.5, p. 321. *)
Lemma cartan_surface_equation_off_endpoint:AN (fun v=>
  v ord_max*((v ord0)^+2+(v (Ordinal (isT:(1<3)%N)))^+2)-
  (v ord0)^+3*FlatExponential.value (1-v ord_max)).
Proof.
have hOpen v (hv:U v):norm_domain_interior NX U v.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX U v).2
    (open_nbhs_nbhs (conj cartan_surface_off_endpoint_open hv))).
have hCoordinate i:AN (fun v=>v i).
  exact:(norm_analytic_open_restriction (fun v (_:U v)=>Logic.I) hOpen
    (@euclidean_scalar_coordinate_analytic R 3 i)).
exact:(norm_analytic_subtract
  (norm_analytic_scalar_product (hCoordinate ord_max)
    (norm_analytic_add (norm_analytic_scalar_power 2%N (hCoordinate ord0))
      (norm_analytic_scalar_power 2%N (hCoordinate (Ordinal (isT:(1<3)%N))))))
  (norm_analytic_scalar_product (norm_analytic_scalar_power 3%N (hCoordinate ord0))
    cartan_surface_coefficient_off_endpoint)).
Qed.

(** Source for [cartan_surface_off_endpoint_variety]: the
    actual original surface intersected with the original open
    equation domain is an analytic subvariety, supporting
    the example cited in 3.4.5, p. 321. *)
Theorem cartan_surface_off_endpoint_variety:
  is_finite_analytic_variety hNX U (U `&` @CartanSurface.set R).
Proof.
split;first exact:cartan_surface_off_endpoint_open.
exists (Finite.clone 'I_1 _),(fun (_:'I_1) (v:X)=>
  v ord_max*((v ord0)^+2+(v (Ordinal (isT:(1<3)%N)))^+2)-
  (v ord0)^+3*FlatExponential.value (1-v ord_max));split.
- move=>_;exact:cartan_surface_equation_off_endpoint.
- move=>v;split.
  + move=>[hv hS];split;first exact:hv.
    move=>_;apply/eqP;rewrite subr_eq0;apply/eqP.
    exact:(cartan_surface_membership (@CartanSurface.laws R) v).1 hS.
  + move=>[hv hZero];split;first exact:hv.
    apply/(cartan_surface_membership (@CartanSurface.laws R)).
    have hEquation:=hZero ord0.
    by move/eqP:hEquation;rewrite subr_eq0=>/eqP.
Qed.
End OffEndpoint.
