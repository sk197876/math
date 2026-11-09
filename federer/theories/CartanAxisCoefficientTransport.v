(** Federer (1969), 3.4.5, p. 321: actual
    analytic coefficient fields on the original axis in
    the real proof of the cited local/global example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness ContinuousMultilinearUP ContinuousMultilinearSealed NormAnalyticUP NormAnalyticOperations
  NormFiniteJetAgreement NormFiniteJetAnalyticPrecompose ScalarVectorLineAnalytic CartanCoordinateGeometry
  AnalyticDirectionalCoefficient AnalyticIteratedDirectionalCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AxisCoefficients.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation J:=([set z:R^o|z<1]).
Local Notation j:=(Ordinal (isT:(1<3)%N)).
Local Notation AN A f:=(@norm_analytic R X R^o NX N hNX hN A f).
Local Notation ScalarAN A f:=(@norm_analytic R R^o R^o N N hN hN A f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X R^o NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X R^o NX N hNX hN).
Local Notation es:=(fun i=>@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN).
Local Notation NS:=(fun i=>@ContinuousMultilinear.norm R i R^o R^o N N hN hN).

(** Source for [cartan_iterated_axis_coefficients_exist]: actual
    global analytic first and transverse divided coefficient
    fields exist, and each original restriction to the
    full z-axis is analytic, supporting 3.4.5, p. 321.
    No formal coefficient function is supplied as a premise. *)
Theorem cartan_iterated_axis_coefficients_exist (f:X->R):
  AN setT f ->exists C:nat->X->R,exists P:nat->nat->X->R,
    (forall i,Coefficient setT f i (@coordinate_basis R 3 ord0) (C i) /\AN setT (C i)) /\
    (forall i k,Coefficient setT (C i) k (@coordinate_basis R 3 j) (P i k) /\AN setT (P i k)) /\
    forall i k,ScalarAN setT (fun z=>P i k (cartan_axis_point z)).
Proof.
move=>hf.
have [C [P [hC hP]]]:=@analytic_iterated_directional_coefficients_exist R X R^o NX N hNX hN
  setT f (@coordinate_basis R 3 ord0) (@coordinate_basis R 3 j) hf.
have hAxis:@norm_analytic R R^o X N NX hN hNX setT (@cartan_axis_point R):=
  @scalar_vector_line_analytic R X NX hNX (@coordinate_basis R 3 ord_max).
exists C,P;split;first exact:hC;split;first exact:hP.
move=>i k;exact:(norm_analytic_compose_on (fun z (_:setT z)=>Logic.I) hAxis (hP i k).2).
Qed.

(** Source for [cartan_axis_finite_jet_agreement]: original
    agreeing finite jets at the origin retain their
    actual scalar jets on the original lower axis
    z<1, supporting the coefficient argument of 3.4.5,
    p. 321. Both original preimage domains are identified. *)
Theorem cartan_axis_finite_jet_agreement (P Q:X->R) k:
  AN U P ->AN U Q ->norm_finite_jet_agreement NX ev NZ U U P Q k 0 ->
  norm_finite_jet_agreement N es NS J J
    (fun z=>P (cartan_axis_point z)) (fun z=>Q (cartan_axis_point z)) k 0.
Proof.
move=>hP hQ hAgree.
have hAxis:@norm_analytic R R^o X N NX hN hNX setT (@cartan_axis_point R):=
  @scalar_vector_line_analytic R X NX hNX (@coordinate_basis R 3 ord_max).
have hAxis0:cartan_axis_point (0:R)=0 by rewrite /cartan_axis_point scale0r.
have hU0:U (cartan_axis_point (0:R)) by rewrite /= (cartan_axis_point_coordinates 0).2.2.
have hAtAxis:norm_finite_jet_agreement NX ev NZ U U P Q k (cartan_axis_point (0:R)).
  by rewrite hAxis0.
have hPull:=@norm_finite_jet_analytic_precompose R R^o X R^o N NX N hN hNX hN U U setT P Q
  (@cartan_axis_point R) k 0 hU0 hU0 Logic.I hP hQ hAxis hAtAxis.
have hDomains:(fun z:R^o=>setT z /\U (cartan_axis_point z))=J.
  apply:funext=>z;apply:propext;rewrite /U /J /= (cartan_axis_point_coordinates z).2.2.
  by split;[move=>[_ hz]|move=>hz;split].
by rewrite hDomains in hPull.
Qed.
End AxisCoefficients.
