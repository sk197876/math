(** Federer (1969), 3.4.5, p. 321: actual
    analytic arcs on the adapted cubic surface, supporting
    the example cited to Cartan (1957), pp. 97–99.
    Every coordinate is an actual analytic function. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormAnalyticUP NormAnalyticOperations NormAnalyticArithmetic NormAnalyticDomain
  NormAnalyticComposition NormAnalyticScalarProducts ScalarAffineAnalytic ScalarVectorLineAnalytic
  ScalarReciprocalAnalytic FlatExponentialSealed FlatExponentialOrder CartanCoefficientAnalytic
  CartanSurfaceUP CartanSurfaceSealed CartanRationalArcPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Arcs.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation A:=([set z:R^o|z<1]).
Local Notation AN Y NY hNY f:=(@norm_analytic R R^o Y N NY hN hNY A f).

(** Source for [cartan_arc_domain_interior]: the original
    parameter range z<1 of the real arcs is open,
    supporting the local/global example in 3.4.5, p. 321. *)
Lemma cartan_arc_domain_interior (z:R^o):A z ->norm_domain_interior N A z.
Proof.
move=>hz;exists (1-z);split;first by rewrite subr_gt0.
move=>h hh;change (is_true (`|h|<1-z)) in hh.
change (is_true (z+h<1)).
have hb:=ler_norm h;lra.
Qed.

(** Source for [cartan_rational_arcs_analytic_exist]: the
    actual arcs meet the origin and lie in the actual
    surface throughout their original parameter range, supporting
    the example cited in 3.4.5, p. 321. *)
Theorem cartan_rational_arcs_analytic_exist (t:R):
  exists u:R->X,
    AN X NX hNX u /\
    (forall z,(u z) ord0=z*(1+t^+2)/FlatExponential.value (1-z)) /\
    (forall z,(u z) (Ordinal (isT:(1<3)%N))=t*(z*(1+t^+2)/FlatExponential.value (1-z))) /\
    (forall z,(u z) ord_max=z) /\u 0=0 /\forall z:R,z<1 ->CartanSurface.set (u z).
Proof.
have hIdWhole:@norm_analytic R R^o R^o N N hN hN setT (fun z=>z).
  move=>z _.
  have hAffine:=@scalar_affine_analytic_at R 1 0 z.
  apply:(norm_analytic_at_domain_agreement _ hAffine)=>y _;by rewrite mul1r ?add0r ?addr0.
have hId:AN R^o N hN (fun z=>z).
  exact:(norm_analytic_open_restriction (fun y (_:A y)=>Logic.I)
    cartan_arc_domain_interior hIdWhole).
have hCoefficient:AN R^o N hN (fun z=>FlatExponential.value (1-z)).
  apply:(norm_analytic_open_restriction _ cartan_arc_domain_interior
    (@cartan_coefficient_off_endpoint_analytic R)).
  move=>z hz;change (is_true (z!=1));by rewrite lt_eqF.
have hInverse:AN R^o N hN (fun z=>(FlatExponential.value (1-z))^-1).
  apply:(norm_analytic_compose_on _ hCoefficient (@scalar_reciprocal_analytic R)).
  move=>z hz;change (is_true (FlatExponential.value (1-z)!=0)).
  have hp:0<FlatExponential.value (1-z) by rewrite flat_exponential_positive subr_gt0.
  by rewrite gt_eqF.
pose x:=fun z:R=>z*(1+t^+2)/FlatExponential.value (1-z).
have hNumerator:AN R^o N hN (fun z=>z*(1+t^+2)).
  move=>z hz.
  have hScale:=@norm_analytic_at_scale R R^o R^o N N hN hN A (fun z=>z) z (1+t^+2) (hId z hz).
  apply:(norm_analytic_at_domain_agreement _ hScale)=>y _;exact:mulrC.
have hX:AN R^o N hN x:=norm_analytic_scalar_product hNumerator hInverse.
have hY:AN R^o N hN (fun z=>t*x z).
  move=>z hz;exact:(@norm_analytic_at_scale R R^o R^o N N hN hN A x z t (hX z hz)).
have hLine (v:X) (g:R->R):AN R^o N hN g ->AN X NX hNX (fun z=>g z*:v).
  move=>hg;exact:(norm_analytic_compose_on (fun z (_:A z)=>Logic.I) hg
    (@scalar_vector_line_analytic R X NX hNX v)).
pose v:=fun z:R=>x z*:(@coordinate_basis R 3 ord0)+
  (t*x z)*:(@coordinate_basis R 3 (Ordinal (isT:(1<3)%N)))+
  z*:(@coordinate_basis R 3 ord_max).
have hV:AN X NX hNX v:=norm_analytic_add
  (norm_analytic_add (hLine _ _ hX) (hLine _ _ hY)) (hLine _ _ hId).
have [u [hUX [hUY [hUZ [hU0 hUS]]]]]:=@cartan_rational_arc_points_exist R t.
have hEqual:forall z,v z=u z.
  move=>z;apply/ffunP=>i.
  rewrite /v /coordinate_basis !ffunE.
  have hCases:i=ord0 \/i=Ordinal (isT:(1<3)%N) \/i=ord_max.
    have hi:=ltn_ord i;case hiVal:(val i) hi=>[|[|[|j]]] hi.
    - left;apply:val_inj;exact:hiVal.
    - right;left;apply:val_inj;exact:hiVal.
    - right;right;apply:val_inj;exact:hiVal.
    - by [].
  case:hCases=>[->|[->|->]].
  - rewrite hUX /=.
    change (x z*1+(t*x z)*0+z*0=x z).
    by rewrite mulr1 !mulr0 !addr0.
  - rewrite hUY /=.
    change (x z*0+(t*x z)*1+z*0=t*x z).
    by rewrite mulr1 !mulr0 add0r addr0.
  - rewrite hUZ /=.
    change (x z*0+(t*x z)*0+z*1=z).
    by rewrite mulr1 !mulr0 !add0r.
exists u;split.
- exact:(norm_analytic_domain_agreement (fun z (_:A z)=>hEqual z) hV).
- by split;first exact:hUX;split;first exact:hUY;split;first exact:hUZ;split.
Qed.
End Arcs.
