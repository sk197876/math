(** Federer (1969), 3.4.10, p. 338:
    the actual implicit solution gives an analytic
    two-dimensional sheet inside the cited polynomial surface.
    Reuse coordinate graphs, analytic composition and the
    proved first-order product and chain rules. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanBlockLinearMaps
  EuclideanThreeBlockCoordinates EuclideanScalarCoordinateMaps EuclideanScalarCoordinateAnalytic
  NormOpenDomainLaws NormBoundedLinearTopology NormDifferentialUP NormDifferentialLinear NormDifferentialLocal NormDifferentialChain
  NormDifferentialScalarProduct ScalarPowerDifferentialComposition NormRegularity NormClassOneUP
  NormAnalyticUP NormAnalyticComposition NormAnalyticLinear NormAnalyticLocal NormAnalyticOperations
  NormAnalyticScalarProducts FunctionalAnalyticSubmanifoldUP AnalyticCoordinateGraph
  BruhatWhitneyPhysicalProjection BruhatWhitneyAuxiliaryEquation
  BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_selected_sheet_function]:
    the actual local proof witness y=x^2 t(x,z)
    in the example cited by 3.4.10, p. 338. *)
Definition bruhat_whitney_selected_sheet_function (R:realType)
    (psi:R_n R 2->R_n R 3) (v:R_n R 3):R:=
  (v ord0)^+2*psi (@bruhat_whitney_physical_projection R v) ord_max.

(** Source for [bruhat_whitney_selected_sheet]: every actual
    auxiliary analytic solution with the prescribed prefix
    defines a functional analytic surface contained in the
    original surface, 3.4.10, p. 338. *)
Theorem bruhat_whitney_selected_sheet (R:realType)
    (V:set (R_n R 2)) (psi:R_n R 2->R_n R 3):
  let X:=R_n R 3 in
  let Y:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 3) in
  let NY:=inner_norm (@euclidean_inner_productP R 2) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3) in
  let hNY:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  let Q:=@bruhat_whitney_physical_projection R in
  let U:set X:=[set v|V (Q v)] in
  let j:=Ordinal (isT:(1<3)%N) in
  let f:=@bruhat_whitney_selected_sheet_function R psi in
  @norm_analytic R Y X NY NX hNY hNX V psi ->
  (forall u,V u ->@euclidean_first_block_map R 2 1 (psi u)=u /\
    @bruhat_whitney_auxiliary_equation R (psi u)=0) ->
  @is_functional_analytic_submanifold R 3 2 U [set v|U v /\v j=f v] /\
  [set v|U v /\v j=f v] `<=` @BruhatWhitneySurface.set R.
Proof.
move=>X Y NX NY hNX hNY Q U j f hPsi hSolutions.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose theta:=fun u:Y=>psi u ord_max.
have hCoord:=@euclidean_scalar_coordinate_analytic R 3 ord_max.
have hTheta:=@norm_analytic_compose_on R Y X R^o NY NX N hNY hNX hN
  V setT psi (fun v:X=>v ord_max) (fun _ _=>Logic.I) hPsi hCoord.
have hQ:=@norm_bounded_linear_analytic R X Y NX NY hNX hNY setT
  (fun v _=>norm_full_domain_interior NX v) Q
  (@bruhat_whitney_physical_projection_bounded R).
have hComposite:=norm_analytic_composition hQ hTheta.
have hDomain:(fun v:X=>setT v /\V (Q v))=U.
  apply:funext=>v;apply:propext;split;[by case|by move=>hv;split].
rewrite hDomain in hComposite.
have hOpen:=norm_analytic_domain_open hComposite.
have hInterior v (hv:U v):norm_domain_interior NX U v.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX U v).2.
  have h:=hOpen;rewrite openE in h;exact:h v hv.
have hCoordinate:=@norm_analytic_open_restriction R X R^o NX N hNX hN setT U
  (fun v:X=>v ord0) (fun _ _=>Logic.I) hInterior
  (@euclidean_scalar_coordinate_analytic R 3 ord0).
have hF:=norm_analytic_scalar_product (norm_analytic_scalar_power 2%N hCoordinate) hComposite.
have hVertical v (hv:U v):exists L:Hom X R^o,
    has_norm_differential NX N U f v L /\L (@coordinate_basis R 3 j)=0.
  have [K hK]:=(@norm_class_firstP R Y R^o NY N hNY hN V theta).1
    (norm_analytic_class_all_orders hTheta 1%N).
  have hThetaD:=@norm_class_one_differential R Y R^o NY N V theta K hK (Q v) hv.
  have hQD:=@norm_differential_linear R X Y NX NY hNX hNY U v Q
    (hInterior v hv) (@bruhat_whitney_physical_projection_bounded R).
  have hChain:=norm_differential_chain hNX hNY hN hQD hThetaD.
  have hSame:(fun x:X=>U x /\V (Q x))=U.
    apply:funext=>x;apply:propext;split;[by case|by move=>hx;split].
  change (has_norm_differential NX N (fun x:X=>U x /\V (Q x))
    (fun x=>theta (Q x)) v (hom_comp (K (Q v)) Q)) in hChain.
  rewrite hSame in hChain.
  pose Dx:=@euclidean_scalar_coordinate_map R 3 ord0.
  have hDx:=@norm_differential_linear R X R^o NX N hNX hN U v Dx
    (hInterior v hv) (euclidean_scalar_coordinate_bounded ord0).
  have hSquare:=@norm_scalar_power_differential_composition R X NX hNX U Dx v Dx 2 hDx.
  pose Dsquare:=(2%:R*(v ord0)^+1)*:Dx.
  have hProduct:=@norm_differential_scalar_product R X R^o NX N hNX hN U
    (fun x:X=>(x ord0)^+2) (fun x=>theta (Q x)) v Dsquare
    (hom_comp (K (Q v)) Q) hSquare hChain.
  exists (scalar_vector_product_linear_term ((v ord0)^+2) (theta (Q v))
    Dsquare (hom_comp (K (Q v)) Q));split;first exact:hProduct.
  rewrite /scalar_vector_product_linear_term hom_addE hom_compE !hom_scaleE
    hom_compE /Q bruhat_whitney_physical_projection_vertical linear0.
  have hDxZero:Dx (@coordinate_basis R 3 j)=0.
    by change (@coordinate_basis R 3 j ord0=0);rewrite /coordinate_basis ffunE /=.
  by rewrite /Dsquare ?hom_scaleE hDxZero ?mulr0 ?linear0 ?scaler0 ?add0r.
split;first exact:(@analytic_coordinate_graph_functional R U f j hOpen hF hVertical).
move=>v [hv hEquation].
have [hPrefix hZero]:=hSolutions (Q v) hv.
have hFirst:=congr1 (fun u:Y=>u ord0) hPrefix.
have hLast:=congr1 (fun u:Y=>u ord_max) hPrefix.
rewrite euclidean_three_prefix_first in hFirst.
rewrite euclidean_three_prefix_second in hLast.
rewrite /Q /bruhat_whitney_physical_projection /= ffunE eqxx in hFirst.
rewrite /Q /bruhat_whitney_physical_projection /= ffunE /= in hLast.
have hActual:@bruhat_whitney_auxiliary_projection R (psi (Q v))=v.
  apply/ffunP=>i;rewrite /bruhat_whitney_auxiliary_projection ffunE.
  case h0:(i==ord0).
  - move/eqP:h0=>->;exact:hFirst.
  case h1:(i==j).
  - move/eqP:h1=>->;rewrite hFirst;exact:esym hEquation.
  have hi:i=ord_max.
    apply:val_inj;case:i h0 h1=>[i hi] /= h0 h1.
    case:i hi h0 h1=>[|[|[|i]]] //.
  by rewrite hi;exact:hLast.
rewrite -hActual;exact:bruhat_whitney_auxiliary_projects_into_surface hZero.
Qed.
