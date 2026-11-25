(** Federer (1969), 3.2.5, p. 245: on the
    Borel pieces of 3.2.2 a Hausdorff-null target set
    has a Lebesgue-null inverse image. This uses the
    actual inverse Lipschitz estimate and source determinant. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLinearMaps
  EuclideanLebesgueDimensions MeasureUP MeasureBasic MeasureAlmostBasic HausdorffMeasure
  InjectiveDifferentialPieceUP BorelPieceImageBounds InnerOwnNormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [injective_differential_piece_null_preimage]:
    the completed-measurability step of Federer 3.2.5,
    p. 245, expanded using both Lipschitz estimates of
    3.2.2, p. 242. The null target need not be
    Borel; the arbitrary-subset image estimate suffices. *)
Lemma injective_differential_piece_null_preimage (R:realType) m n
    (f:R_n R m->R_n R n) (lambda:R) (E:set (R_n R m)) (N:set (R_n R n)):
  is_injective_differential_piece f lambda E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m N=0 ->
  euclidean_lebesgue_measure m (E `&` (f @^-1` N))=0.
Proof.
move=>hPiece hN.
pose B:=E `&` (f @^-1` N).
pose mu:=@euclidean_lebesgue_measure R m.
have hm:=euclidean_lebesgue_is_measure R m.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hImage:@hausdorff_measure R Y m (f @` B)=0.
  apply:(measure_null_subset (@hausdorff_measure_is_measure R Y m) _ hN).
  by move=>y [x [_ hx] <-].
have [s [t [g [hst [hts [hg [hForward [hInverse hModel]]]]]]]]:=hPiece.2.2.2.
have hBE:B `<=` E by move=>x [hx _].
have hBound:=(@borel_piece_image_bounds R m n f E B s t g lambda hst hg hForward hInverse hBE).2.
rewrite inner_own_norm_hausdorff hImage mule0 in hBound.
pose d:=`|euclidean_det (hom_as_linear s)|%R.
have hDet:euclidean_det (hom_as_linear s)!=0%R:=(euclidean_det_injective _).2 (can_inj hst).
have hd:(0<d)%R by rewrite /d normr_gt0.
have hdNum:d%:E \is a fin_num by rewrite fin_numE.
have hdPos:0<d%:E by rewrite lte_fin.
have hCancel:=@lee_pmul2l R d%:E hdNum hdPos (mu B) 0.
rewrite mule0 in hCancel.
change (is_true (d%:E*mu B<=0)) in hBound.
rewrite hCancel in hBound.
apply/eqP; by rewrite eq_le hBound (measure_nonnegative hm).
Qed.
