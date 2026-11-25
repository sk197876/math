(** Federer (1969), 3.4.5, p. 321: actual analytic
    normalization of the adapted local/global counterexample
    cited to Cartan (1957), pp. 97–99. Its coordinate
    laws precede the local existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormBoundedLinearTopology NormOpenDomainLaws
  NormHigherCurveDerivativeUP NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialChain
  NormDifferentialLocal NormDifferentialFiniteCalculus NormedPrimitiveCell
  NormAnalyticUP NormAnalyticLocal NormAnalyticDomain NormAnalyticOperations NormAnalyticArithmetic
  NormAnalyticComposition EuclideanScalarCoordinateMaps EuclideanScalarCoordinateAnalytic
  ScalarVectorLineAnalytic FlatExponentialSealed CartanAxisCoordinate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Normalization.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation AN Y NY hNY f:=(@norm_analytic R X Y NX NY hNX hNY U f).
Local Notation j:=(Ordinal (isT:(1<3)%N)).

(** Source for [cartan_normalization_map_exist]: the actual
    analytic coordinate change preserves the first two coordinates
    and replaces the last by z/a(z). Its actual
    differential at zero is injective; no local inverse
    is supplied as a hypothesis, supporting 3.4.5, p. 321. *)
Theorem cartan_normalization_map_exist:
  exists T:X->X,exists L:Hom X X,
    AN X NX hNX T /\T 0=0 /\
    (forall v,(T v) ord0=v ord0) /\
    (forall v,(T v) j=v j) /\
    (forall v,(T v) ord_max=cartan_axis_coordinate (v ord_max)) /\
    has_norm_differential NX NX U T 0 L /\injective L.
Proof.
pose e:=@coordinate_basis R 3.
pose p:=fun i:'I_3=>@euclidean_scalar_coordinate_map R 3 i.
pose E:=fun i:'I_3=>@scalar_coefficient_linear_map R X (e i).
pose c:=(FlatExponential.value (1:R))^-1.
pose M:=@scalar_coefficient_linear_map R R^o (c:R^o).
have hWhole i:@norm_analytic R X R^o NX N hNX hN setT (fun v=>v i).
  exact:(euclidean_scalar_coordinate_analytic i).
have hLast0:@norm_analytic R X R^o NX N hNX hN
    (fun v=>setT v /\v ord_max<1) (fun v=>cartan_axis_coordinate (v ord_max)).
  exact:(norm_analytic_composition (hWhole ord_max) (@cartan_axis_coordinate_analytic R)).
have hLast:AN R^o N hN (fun v=>cartan_axis_coordinate (v ord_max)).
  move=>v hv;apply:(norm_analytic_at_domain_enlargement _ (hLast0 v (conj Logic.I hv))).
  by move=>w [_ hw].
have hOpen v (hv:U v):norm_domain_interior NX U v.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX U v).2.
  exact:(open_nbhs_nbhs (conj (norm_analytic_domain_open hLast) hv)).
have hCoordinate i:AN R^o N hN (fun v=>v i).
  exact:(norm_analytic_open_restriction (fun v (_:U v)=>Logic.I) hOpen (hWhole i)).
have hLine i (g:X->R):AN R^o N hN g ->AN X NX hNX (fun v=>g v*:e i).
  move=>hg;exact:(norm_analytic_compose_on (fun v (_:U v)=>Logic.I) hg
    (@scalar_vector_line_analytic R X NX hNX (e i))).
pose T:=fun v:X=>v ord0*:e ord0+v j*:e j+cartan_axis_coordinate (v ord_max)*:e ord_max.
have hT:AN X NX hNX T:=norm_analytic_add
  (norm_analytic_add (hLine ord0 _ (hCoordinate ord0)) (hLine j _ (hCoordinate j)))
  (hLine ord_max _ hLast).
have hX v:(T v) ord0=v ord0.
  rewrite /T /e /coordinate_basis !ffunE /=.
  change (v ord0*1+v j*0+cartan_axis_coordinate (v ord_max)*0=v ord0).
  by rewrite mulr1 !mulr0 !addr0.
have hY v:(T v) j=v j.
  rewrite /T /e /coordinate_basis !ffunE /=.
  change (v ord0*0+v j*1+cartan_axis_coordinate (v ord_max)*0=v j).
  by rewrite mulr1 !mulr0 add0r addr0.
have hZ v:(T v) ord_max=cartan_axis_coordinate (v ord_max).
  rewrite /T /e /coordinate_basis !ffunE /=.
  change (v ord0*0+v j*0+cartan_axis_coordinate (v ord_max)*1=cartan_axis_coordinate (v ord_max)).
  by rewrite mulr1 !mulr0 !add0r.
have hT0:T 0=0.
  by rewrite /T !ffunE cartan_axis_coordinate_origin !scale0r !add0r.
have hU0:U 0 by rewrite /= ffunE;exact:ltr01.
have hP i:norm_bounded_linear NX N (p i):=euclidean_scalar_coordinate_bounded i.
have hE i:norm_bounded_linear N NX (E i):=scalar_coefficient_linear_bound hNX (e i).
have hFirst i:has_norm_differential NX NX U (fun v=>v i*:e i) 0 (hom_comp (E i) (p i)).
  exact:(@norm_differential_linear R X X NX NX hNX hNX U 0
    (hom_comp (E i) (p i)) (hOpen 0 hU0) (norm_bounded_linear_compose (hP i) (hE i))).
have hP2:=@norm_differential_linear R X R^o NX N hNX hN setT 0 (p ord_max)
  (norm_full_domain_interior NX 0) (hP ord_max).
have hB:has_norm_differential N N [set z:R^o|z<1] (@cartan_axis_coordinate R) ((p ord_max) 0) M.
  have hPZero:(p ord_max) 0=0 by rewrite /p /euclidean_scalar_coordinate_map /= ffunE.
  rewrite hPZero;exact:(@cartan_axis_coordinate_differential_origin R).
have hChain:=norm_differential_chain hNX hN hN hP2 hB.
have hChainU:has_norm_differential NX N U
    (fun v=>cartan_axis_coordinate (v ord_max)) 0 (hom_comp M (p ord_max)).
  apply:(norm_differential_restrict _ (hOpen 0 hU0) hChain).
  by move=>v hv;split.
have hThird:=norm_differential_postcompose hNX hChainU (hE ord_max).
pose L:=hom_comp (E ord0) (p ord0)+hom_comp (E j) (p j)+
  hom_comp (E ord_max) (hom_comp M (p ord_max)).
have hL:has_norm_differential NX NX U T 0 L:=
  norm_differential_add hNX (norm_differential_add hNX (hFirst ord0) (hFirst j)) hThird.
have hLX v:(L v) ord0=v ord0.
  rewrite /L !hom_addE !hom_compE /p /E /M /e /euclidean_scalar_coordinate_map /=.
  rewrite /coordinate_basis !ffunE /=.
  change (v ord0*1+v j*0+(v ord_max*c)*0=v ord0).
  by rewrite mulr1 !mulr0 !addr0.
have hLY v:(L v) j=v j.
  rewrite /L !hom_addE !hom_compE /p /E /M /e /euclidean_scalar_coordinate_map /=.
  rewrite /coordinate_basis !ffunE /=.
  change (v ord0*0+v j*1+(v ord_max*c)*0=v j).
  by rewrite mulr1 !mulr0 add0r addr0.
have hLZ v:(L v) ord_max=v ord_max*c.
  rewrite /L !hom_addE !hom_compE /p /E /M /e /euclidean_scalar_coordinate_map /=.
  rewrite /coordinate_basis !ffunE /=.
  change (v ord0*0+v j*0+(v ord_max*c)*1=v ord_max*c).
  by rewrite mulr1 !mulr0 !add0r.
have hc:c!=0 by rewrite /c gt_eqF //;exact:(@cartan_axis_coordinate_positive_slope R).
have hInjective:injective L.
  move=>u v hEqual;apply/ffunP=>i.
  have hCases:i=ord0 \/i=j \/i=ord_max.
    have hi:=ltn_ord i;case hiVal:(val i) hi=>[|[|[|k]]] hi.
    - left;apply:val_inj;exact:hiVal.
    - right;left;apply:val_inj;exact:hiVal.
    - right;right;apply:val_inj;exact:hiVal.
    - by [].
  case:hCases=>[->|[->|->]].
  - by have:=congr1 (fun w:X=>w ord0) hEqual;rewrite !hLX.
  - by have:=congr1 (fun w:X=>w j) hEqual;rewrite !hLY.
  - have he:=congr1 (fun w:X=>w ord_max) hEqual;rewrite !hLZ in he.
    have:=congr1 (fun r:R=>r*c^-1) he;by rewrite -!mulrA mulfV // !mulr1.
by exists T,L;split;first exact:hT;split;first exact:hT0;split;first exact:hX;
  split;first exact:hY;split;first exact:hZ;split.
Qed.
End Normalization.
