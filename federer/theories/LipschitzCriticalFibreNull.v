(** Federer (1969), 3.2.31, p. 269: the low-rank
    fibre contribution of the original Lipschitz map vanishes.
    Closed class-one agreement pieces and actual differential
    agreement transfer the proved small-rescaling estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormClassOneUP NormRegularity LinearRankAtLeast
  LipschitzUP ClassOneAgreementCoverUP LipschitzClassOneAgreementCover ClassOneAgreementDifferentials
  ClassOneCriticalFibreNull CountableNullFibreCover EuclideanLebesgueDimensions EuclideanHausdorffLebesgue
  HausdorffMeasure HausdorffFibreCutoffs NullFibresProperSource EuclideanClosedBallCompact
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section LipschitzCriticalNull.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation Leb:=(@euclidean_lebesgue_measure R m.+1).

(** Source for [lipschitz_low_rank_fibres_almost_null]: the
    vanishing critical-fibre assertion used in Federer 3.2.31,
    p. 269. Every point of A has an actual differential of
    rank below mu. Countably many class-one agreement pieces
    transfer both values and derivatives outside a proved null
    source remainder; 2.10.25 controls that remainder. No
    measurability, compactness or finite-mass premise is added. *)
Theorem lipschitz_low_rank_fibres_almost_null (F:X->Y) (A:set X) L k mu:
  (0<v)%N ->(0<mu)%N ->m.+1=(k+mu)%N ->
  is_metric_lipschitz_bound setT F L ->
  (forall a,A a ->exists D:Hom (R_n R m.+1) (R_n R v),
    has_norm_differential NX NY setT F a D /\~linear_rank_at_least D mu) ->
  measure_almost_everywhere (@hausdorff_measure R Y mu)
    [set y|hausdorff_fibre_mass F A k y=0].
Proof.
move=>hv hmu hDim hLip hA.
have [G [C hCover]]:=@lipschitz_class_one_agreement_cover R m v F L hLip.
have hField j:exists E:R_n R m.+1->Hom (R_n R m.+1) (R_n R v),
    is_norm_class_one_field NX NY setT (G j) E.
  apply:(@norm_class_firstP R (R_n R m.+1) (R_n R v) NX NY
    (inner_norm_real_norm (@euclidean_inner_productP R m.+1))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT (G j)).1.
  exact (@class_one_agreement_cover_class R m v F G C hCover j).
have [E hE]:=choice hField.
pose Good j:set X:=[set a|forall D H:Hom (R_n R m.+1) (R_n R v),
  has_norm_differential NX NY setT F a D ->
  has_norm_differential NX NY setT (G j) a H ->D=H].
have hBad j:Leb (C j `\` Good j)=0.
  exact (@class_one_agreement_cover_differentials R m v F G C hCover j).
pose B j:set X:=C j `&` [set a|~linear_rank_at_least (E j a) mu].
pose N:set X:=A `\` \bigcup_j B j.
have hLeb:=euclidean_lebesgue_is_measure R m.+1.
have hNullN:Leb N=0.
  have hUnion:Leb (\bigcup_j (C j `\` Good j))=0.
    apply:(measure_null_countable_union hLeb (countableP _))=>j _; exact:hBad.
  have hNull:Leb ((~` \bigcup_j C j) `|` \bigcup_j (C j `\` Good j))=0.
    apply:(measure_null_union hLeb _ hUnion).
    exact (@class_one_agreement_cover_conull R m v F G C hCover).
  apply:(measure_null_subset hLeb _ hNull)=>a [ha hNotB].
  case:(pselect ((\bigcup_j C j) a))=>[[j _ haj]|hNoC]; last by left.
  right; exists j=>//; split=>//; move=>hGood.
  have [D [hD hRank]]:=hA a ha.
  have hDE:=hGood D (E j a) hD (norm_class_one_differential (hE j) Logic.I).
  have hRankE:~linear_rank_at_least (E j a) mu by rewrite -hDE.
  apply:hNotB; exists j=>//; exact (conj haj hRankE).
have hFibresB j:measure_almost_everywhere (@hausdorff_measure R Y mu)
    [set y|hausdorff_fibre_mass F (B j) k y=0].
  have hNull:=@class_one_low_rank_fibres_almost_null R m.+1 v (G j) (E j) (B j) k mu
    hv hmu hDim (hE j) (fun a ha=>ha.2).
  have hPhi:hausdorff_fibre_mass F (B j) k=@hausdorff_fibre_mass R X Y (G j) (B j) k.
    apply:funext=>y; rewrite /hausdorff_fibre_mass; congr (hausdorff_measure k _).
    apply/seteqP; split=>a [ha hFa]; split=>//.
    - have he:F a=G j a:=@class_one_agreement_cover_equal R m v F G C hCover j a ha.1.
      change (G j a=y); by rewrite -he.
    - have he:F a=G j a:=@class_one_agreement_cover_equal R m v F G C hCover j a ha.1.
      change (F a=y); by rewrite he.
  by rewrite hPhi.
have hFibresN:measure_almost_everywhere (@hausdorff_measure R Y mu)
    [set y|hausdorff_fibre_mass F N k y=0].
  apply:(@null_hausdorff_fibres_proper_source R X Y F L N k mu _ hLip).
  - move=>a r hr; exact (@euclidean_closed_metric_ball_compact R m.+1 a r).
  - rewrite -hDim (euclidean_hausdorff_spherical_lebesgue N).1; exact hNullN.
pose Q j:=if j is i.+1 then B i else N.
apply:(@almost_null_fibres_countable_cover R X Y (@hausdorff_measure R X k)
  (@hausdorff_measure R Y mu) (@hausdorff_measure_is_measure R X k)
  (@hausdorff_measure_is_measure R Y mu) F A Q).
- move=>a ha; case:(pselect ((\bigcup_j B j) a))=>[[j _ haj]|hNoB].
  + by exists j.+1.
  + exists 0%N=>//; by split.
- by move=>[|j]; [exact hFibresN|exact:hFibresB].
Qed.
End LipschitzCriticalNull.
