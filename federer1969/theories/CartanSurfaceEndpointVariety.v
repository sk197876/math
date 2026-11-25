(** Federer (1969), 3.4.5, p. 321, citing Cartan
    (1957), p. 97: an actual neighbourhood of the
    flat axis point has the two polynomial equations x=y=0.
    Thus local analyticity is retained at the flat endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra ring.
From Federer Require Import RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetric NormDifferentialUP NormOpenDomainLaws NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticOperations NormAnalyticScalarProducts EuclideanScalarCoordinateAnalytic EuclideanCoordinateMetric
  FlatExponentialSealed CartanSurfaceUP CartanSurfaceSealed CartanSurfaceGeometry FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cartan_surface_endpoint_variety]: the
    actual adapted surface has finite analytic local equations
    at its flat endpoint, supporting the counterexample cited
    in 3.4.5, p. 321. The neighbourhood is
    an actual Euclidean ball, with no local-equation premise. *)
Theorem cartan_surface_endpoint_variety (R:realType) (a:R_n R 3):
  CartanSurface.set a ->a ord_max= 1 ->
  exists U:set (R_n R 3),U a /\
    is_finite_analytic_variety (inner_norm_real_norm (@euclidean_inner_productP R 3))
      U (U `&` @CartanSurface.set R).
Proof.
move=>hS hz.
pose X:=R_n R 3.
pose NX:=inner_norm (@euclidean_inner_productP R 3).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3).
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
have [hx hy]:=(@cartan_surface_flat_plane R a hz).1 hS.
pose U:set X:=fun v=>NX (v-a)<1/4.
have hRadius:0<(1/4:R) by rewrite divr_gt0 // ltr0n.
have hUa:U a by rewrite /U subrr /NX (real_seminorm_zero hNX.1).
have hInterior v (hv:U v):norm_domain_interior NX U v.
  exact:(@norm_open_ball_domain_interior R X NX hNX a (1/4) v hv).
have hOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>v hv;exact:((@norm_domain_interior_neighbourhood R X NX hNX U v).1 (hInterior v hv)).
have hCoordinates i:@norm_analytic R X R^o NX N hNX hN U (fun v=>v i).
  exact:(norm_analytic_open_restriction (fun v (_:U v)=>Logic.I) hInterior
    (@euclidean_scalar_coordinate_analytic R 3 i)).
have hEquationAnalytic:=norm_analytic_add
  (norm_analytic_scalar_power 2%N (hCoordinates ord0))
  (norm_analytic_scalar_power 2%N (hCoordinates (Ordinal (isT:(1<3)%N)))).
have hAxis v (hv:U v):CartanSurface.set v <->v ord0=0 /\v (Ordinal (isT:(1<3)%N))=0.
  have hXBound:=@euclidean_coordinate_norm_bound R 3 ord0 (v-a).
  have hZBound:=@euclidean_coordinate_norm_bound R 3 ord_max (v-a).
  rewrite !ffunE hx subr0 in hXBound.
  rewrite !ffunE hz in hZBound.
  have hQuarter:(1/4:R)<1/2 by lra.
  have hX:`|v ord0|<1/2:=lt_trans (le_lt_trans hXBound hv) hQuarter.
  have hZSmall:`|v ord_max-1|<1/4:=le_lt_trans hZBound hv.
  have hLower:=ler_norm (1-v ord_max).
  have hNorm:`|1-v ord_max|=`|v ord_max-1| := real_seminorm_subtract hN.1 1 (v ord_max).
  rewrite hNorm in hLower.
  have hZ:1/2<v ord_max by lra.
  exact:(@cartan_surface_near_flat_axis R v hZ hX).
exists U;split;first exact:hUa.
split;first exact:hOpen.
exists (Finite.clone 'I_1 _),(fun (_:'I_1) (v:X)=>(v ord0)^+2+(v (Ordinal (isT:(1<3)%N)))^+2);split.
- move=>_;exact:hEquationAnalytic.
- move=>v;split.
  + move=>[hv hSv];have [hX hY]:=(hAxis v hv).1 hSv;split;first exact:hv.
    move=>_;rewrite hX hY;ring.
  + move=>[hv hZero];split;first exact:hv;apply/(hAxis v hv).
    have hSum:=hZero ord0.
    have hX:=sqr_ge0 (v ord0).
    have hY:=sqr_ge0 (v (Ordinal (isT:(1<3)%N))).
    have hXUpper:=lerD (lexx ((v ord0)^+2)) hY.
    rewrite addr0 hSum in hXUpper.
    have hYUpper:=lerD hX (lexx ((v (Ordinal (isT:(1<3)%N)))^+2)).
    rewrite add0r hSum in hYUpper.
    have hXZero:(v ord0)^+2=0 by apply/eqP;rewrite eq_le hXUpper hX.
    have hYZero:(v (Ordinal (isT:(1<3)%N)))^+2=0 by apply/eqP;rewrite eq_le hYUpper hY.
    split;apply/eqP;[move/eqP:hXZero|move/eqP:hYZero];by rewrite sqrf_eq0.
Qed.
