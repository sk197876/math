(** Federer (1969), 4.1.26, pp. 383–384:
    the top scalar coordinate of the preceding
    vector area density is the original signed
    degree. The comparison is only at actual
    defined fibre sums. Outside A the signed
    summand is zero without requiring a differential;
    critical differentials retain sign zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading
  ExteriorDeterminant AlternatingForms AlternatingIsomorphism AlternatingPairing
  CharacteristicFunctionUP CharacteristicFunctionSealed PartialFunctionUP
  PartialFunctionPostcomposition PartialFibreNumericalSum ExtendedRealOrderTopology
  MeasureUP MeasureAlmostUP MeasureAlmostBasic CurrentAreaNormalisedImageUP
  CurrentAreaFibreSumUP CurrentAreaFibreDensityUP TopDegreeNormalisedDeterminant
  LipschitzDegreeSummandUP LipschitzDegreeSummandSealed LipschitzDegreeUP LipschitzDegreeSealed
  FiniteExteriorPowers
  EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section LipschitzDegreeAreaGraph.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable m:nat.
Local Notation X:=(R_n R m).
Local Notation V:=(exterior_power X m).
Local Notation top:=(e_lambda (@coordinate_basis R m) (ord_tuple m)).
Local Notation coordinate:=(@top_coordinate R h2 m X
  (@coordinate_basis R m) (@coordinate_basisP R m)).

(** Source for [degree_top_coordinate_form]: the original
    top scalar coordinate viewed as a covector,
    supporting the scalar specialization of 4.1.25
    in 4.1.26, p. 384. This abbreviates
    the already proved covector-Hom identification. *)
Definition degree_top_coordinate_form:A_m X R^o m:=
  hom_to_form (@HomMap R V R^o coordinate
    (introT (asboolP _) (linearP coordinate))).

(** Source for [degree_top_coordinate_pairing]: the
    actual covector pairing is the original top
    scalar coordinate, supporting 4.1.26, p. 384. *)
Lemma degree_top_coordinate_pairing (v:V):pairing v degree_top_coordinate_form=coordinate v.
Proof. by rewrite /degree_top_coordinate_form pairing_hom_identification. Qed.

Variable f:X->X.
Variable A:set X.
Local Notation chi:=(@CharacteristicFunction.value R X A).
Local Notation xi:=(fun x:X=>chi x*:top).
Variable u:partial_function X V.
Hypothesis hU:@is_current_area_normalised_image R m m f xi u.
Local Notation s:=(@LipschitzDegreeSummand.value R m f A).
Local Notation d:=(@LipschitzDegree.value R m f A).

(** Source for [area_normalised_degree_summand]: each
    actual normalized vector summand has exactly
    the determinant-sign scalar coefficient used in
    4.1.26, p. 383. No assertion is
    made at an undefined area differential. *)
Theorem area_normalised_degree_summand x (v:V):
  partial_function_graph u x v->partial_function_graph s x (coordinate v).
Proof.
move=>hv.
have[D [hD [hJ hCoefficient]]]:=(hU x v).1 hv.
have hV:v=(chi x*Num.sg (@euclidean_det R m (hom_as_linear D)))*:top.
  rewrite -hCoefficient;exact:top_degree_normalised_determinant.
have hCoordinate:coordinate v=chi x*Num.sg (@euclidean_det R m (hom_as_linear D)).
  by rewrite hV linearZ top_coordinateE;exact:mulr1.
apply:(@LipschitzDegreeSummand.laws R m f A x (coordinate v)).2.
case:(pselect (A x))=>hx.
- right;split;first exact:hx.
  exists D;split;first exact:hD.
  by rewrite hCoordinate (characteristic_on_set (@CharacteristicFunction.laws R X A) hx) mul1r.
- left;split;first exact:hx.
  by rewrite hCoordinate (characteristic_off_set (@CharacteristicFunction.laws R X A) hx) mul0r.
Qed.

(** Source for [area_fibre_degree_graph]: every defined
    original top-degree vector fibre sum has
    scalar coordinate equal to the signed degree,
    the precise specialization of 4.1.25 in
    4.1.26, pp. 383–384. The exact full
    numerical fibre and its domain are retained. *)
Theorem area_fibre_degree_graph y (eta:V):
  @is_current_area_fibre_sum R X m m f u y eta->
  partial_function_graph d y (coordinate eta).
Proof.
move=>hSum.
pose alpha:=degree_top_coordinate_form.
have hScalar:=hSum alpha.
rewrite degree_top_coordinate_pairing in hScalar.
have[w [hOn hValue]]:=(partial_fibre_numerical_sum_graph _ _ _ _).1 hScalar.
apply:(@LipschitzDegree.laws R m f A y (coordinate eta)).2.
apply:(partial_fibre_numerical_sum_graph _ _ _ _).2.
exists w;split;last exact:hValue.
move=>x hx.
have[v [hV hPair]]:=hOn x hx.
exists (coordinate v);split.
- exact:area_normalised_degree_summand hV.
- by rewrite -degree_top_coordinate_pairing.
Qed.

(** Source for [area_fibre_degree_direction]: the original
    area density is the signed degree times
    the standard top vector, supporting the
    displayed current identity in 4.1.26, p. 383.
    This is an equality at every defined fibre. *)
Theorem area_fibre_degree_direction y (eta:V):
  @is_current_area_fibre_sum R X m m f u y eta->
  partial_function_graph d y (coordinate eta) /\eta=(coordinate eta)*:top.
Proof.
move=>hSum;split;first exact:area_fibre_degree_graph hSum.
exact:(@top_expansion R h2 m X (@coordinate_basis R m) (@coordinate_basisP R m) eta).
Qed.

(** Source for [area_degree_conull_domain]: the
    original area density's conull domain gives
    a conull signed-degree domain, 4.1.26, p. 383.
    The earlier area theorem supplies the analytic
    premise; no global inverse or injectivity is used. *)
Theorem area_degree_conull_domain (mu:set X->\bar R) (hMu:is_measure mu)
    (eta:partial_function X V):
  @is_current_area_fibre_density R X m m f u eta->
  measure_almost_everywhere mu (partial_function_domain eta)->
  measure_almost_everywhere mu (partial_function_domain d).
Proof.
move=>hEta hDomain.
apply:(@measure_almost_everywhere_mono R X mu hMu _ _ _ hDomain)=>y [v hv].
exists (coordinate v);exact:area_fibre_degree_graph ((hEta y v).1 hv).
Qed.
End LipschitzDegreeAreaGraph.
