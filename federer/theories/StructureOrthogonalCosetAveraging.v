(** Federer (1969), 3.3.4, pp. 289–290:
    the actual orthogonal Haar/Fubini step.
    B_j and C_j are Borel, D is
    the original Suslin locus, and each
    actual active coset has null exception. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom HomInner HomSpaceTopology GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure OrthogonalHaarRegularity IsotropyGroupTopology LinearGroupTopology
  LinearGroupSealed TopologicalGroupUP TopologicalGroupLaws TopologicalProductMaps
  HaarIntegralUP HaarIntegralLaws CompactGroupHaarNormalisation GroupMultiplicationHomogeneous
  InvariantMeasureTranslates MeasureUP MeasureBasic MeasureSplit BorelRegularMeasureUP
  TopologicalBorel SuslinSetUP ProductMeasure ProductBorelRegularity CountablyMeasurableBasic
  StructureExceptionalSetMeasurability StructureCosetNullAveraging.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Average.
Variable R:realType.
Variables n d:nat.
Local Notation ON:=(euclidean_orthogonal_group R n).
Local Notation OD:=(euclidean_orthogonal_group R d).
Local Notation N:=[the topologicalType of set_type ON].
Local Notation H:=[the topologicalType of set_type OD].
Variables (mulN:N->N->N) (invN:N->N) (eN:N).
Variables (mulH:H->H->H) (invH:H->H) (eH:H).
Hypothesis hN:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  ON mulN invN eN.
Hypothesis hH:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R d) (@coordinate_basisP R d))
  (linear_group_inv (@euclidean_inner_productP R d) (@coordinate_basisP R d))
  (linear_group_unit (@euclidean_inner_productP R d) (@coordinate_basisP R d))
  OD mulH invH eH.
Variables (theta:set N->\bar R) (beta:set H->\bar R).
Variable iota:H->N.

(** Source for [structure_orthogonal_coset_null_average]:
    the actual normalized Haar/Fubini
    computation of Federer 3.3.4,
    pp. 289–290. Borel-regularity and
    countable bases of the actual groups,
    product measurability of the original
    exception, finite product mass and
    right-invariance are all derived. The
    geometric nullity on each actual coset
    is the remaining input to this
    supporting averaging theorem. *)
Theorem structure_orthogonal_coset_null_average (B C D:set N):
  is_normalised_haar_measure mulN theta ->is_normalised_haar_measure mulH beta ->
  continuous iota ->borel_set B ->borel_set C ->is_suslin_set R D ->
  (forall g:N,beta [set h:H|~(B `|` C `|` D) (mulN g (iota h))]=0%E) ->
  theta (~` (B `|` C `|` D))=0%E.
Proof.
move=>hTheta hBeta hIota hB hC hD hCosets.
have hMu:is_measure theta.
  have [J [hNJ hMeasure hRep hRegular]]:=hTheta.1; exact:hMeasure.
have hNu:is_measure beta.
  have [J [hNJ hMeasure hRep hRegular]]:=hBeta.1; exact:hMeasure.
have hMuRegular:=orthogonal_normalised_haar_borel_regular hN hTheta.
have hNuRegular:=orthogonal_normalised_haar_borel_regular hH hBeta.
have [U hU]:=@orthogonal_group_countable_open_base R n.
have [V hV]:=@orthogonal_group_countable_open_base R d.
have hProduct:=product_measure_is_measure hMu hNu.
have hProductRegular:=product_measure_borel_regular hMu hNu hU hV hMuRegular hNuRegular.
have hTopN:=lch_group_topological (orthogonal_group_lch hN).
have hPair:continuous (fun z:N*H=>(z.1,iota z.2):N*N).
  apply:topological_pair_continuous; first exact:first_projection_continuous.
  move=>z; exact:(continuous_comp (@second_projection_continuous N H z) (hIota z.2)).
have hTranslation:continuous (fun z:N*H=>mulN z.1 (iota z.2)).
  have hMul:continuous (fun p:N*N=>mulN p.1 p.2):=topological_group_mul_continuous hTopN.
  move=>z; exact:(@continuous_comp (N*H)%type (N*N)%type N
    (fun z:N*H=>(z.1,iota z.2)) (fun p:N*N=>mulN p.1 p.2) z
    (hPair z) (hMul (z.1,iota z.2))).
pose Bad:=~` (B `|` C `|` D).
pose S:set (N*H):=[set z|Bad (mulN z.1 (iota z.2))].
have hSMeasurable:measure_measurable (product_measure hMu hNu) S.
  exact:(structure_exceptional_preimage_measurable hProduct hProductRegular hTranslation hB hC hD).
have hSFinite:(product_measure hMu hNu S< +oo)%E.
  have hCover:S `<=` (@setT N) `*` (@setT H) by move=>z _; split.
  have hBound:=le_trans (measure_mono hProduct hCover)
    (@product_measure_rectangle_bound R N H theta beta hMu hNu setT setT
      (measure_measurable_whole hMu) (measure_measurable_whole hNu)).
  rewrite hTheta.2 hBeta.2 mul1e in hBound.
  exact:le_lt_trans hBound (ltry 1%R).
have hCount:=finite_measurable_set_countably_measurable hSMeasurable hSFinite.
have hPositive:(0<beta setT)%E by rewrite hBeta.2 lte_fin ltr01.
have hRight:=orthogonal_normalised_haar_measure_right hN hTheta.
have hInvariant:=nonzero_invariant_measure_invariant hRight.
have hOriginal (h:H):theta [set g:N|Bad (mulN g (iota h))]=theta Bad.
  have hLaw:=invariant_measure_preimage (topological_group_laws hTopN)
    (right_multiplication_homogeneous hTopN) hInvariant (invN (iota h)) Bad.
  change (theta ((fun g:N=>mulN g (invN (invN (iota h)))) @^-1` Bad)=theta Bad) in hLaw.
  by rewrite (group_invK (topological_group_laws hTopN)) in hLaw.
exact:(@structure_coset_null_average R N H theta beta hMu hNu
  (fun g h=>mulN g (iota h)) Bad hPositive hCount hCosets hOriginal).
Qed.
End Average.
