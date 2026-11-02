(** Federer (1969), 3.2.3, p. 243: image measure
    comparisons on a piece supplied by 3.2.2, followed by
    the linear source change of variables from 2.7.16(1). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric EuclideanLinearMaps EuclideanLebesgueDimensions
  EuclideanLebesgueDeterminant HausdorffMeasure HausdorffRestrictedLipschitz
  InnerOwnNormTopology LipschitzUP PartialFunctionUP PartialFunctionExtensionUP
  PartialFunctionExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_piece_image_bounds]: the displayed
    image-measure comparison for B contained in E, Federer
    3.2.3, p. 243. The inverse's total representative
    comes only from the existing opaque extension interface;
    the bound uses it exclusively on the actual image. *)
Theorem borel_piece_image_bounds (R:realType) m n
    (f:R_n R m->R_n R n) (E B:set (R_n R m))
    (s t:Hom (R_n R m) (R_n R m)) (g:partial_function (R_n R n) (R_n R m)) (lambda:R):
  cancel s t ->
  (forall y x,partial_function_graph g y x <-> E x /\ f x=y) ->
  @is_metric_lipschitz_bound R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (s @` E) (fun y=>f (t y)) lambda ->
  (forall y z x w,partial_function_graph g y x -> partial_function_graph g z w ->
    (inner_norm (@euclidean_inner_productP R m) (s x-s w)<=
      lambda*inner_norm (@euclidean_inner_productP R n) (y-z))%R) ->
  B `<=` E ->
  @hausdorff_measure R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) m (f @` B)<=
      (lambda^+m)%R%:E*(`|euclidean_det (hom_as_linear s)|%:E*euclidean_lebesgue_measure m B) /\
  `|euclidean_det (hom_as_linear s)|%:E*euclidean_lebesgue_measure m B<=
    (lambda^+m)%R%:E* @hausdorff_measure R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) m (f @` B).
Proof.
move=>hst hg hForward hInverse hBE.
pose X:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)).
pose Y:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose u:=@PartialFunctionExtension.value (R_n R n) (R_n R m) g (0%R:R_n R m).
have hu:=@PartialFunctionExtension.laws (R_n R n) (R_n R m) g (0%R:R_n R m).
have hVal x:E x -> u (f x)=x.
  move=>hx; exact (hu (f x) x ((hg (f x) x).2 (conj hx (erefl _)))).
have hForwardImage:(fun y:X=>f (t y)) @` (s @` B)=f @` B.
  apply/seteqP; split=>y.
  - move=>[v [x hx <-] <-]; rewrite hst; by exists x.
  - move=>[x hx <-]; exists (s x); last by rewrite hst.
    by exists x.
have hSourceImage:s @` B `<=` s @` E by move=>y [x hx <-]; exists x; first exact:hBE; by [].
have hF:=@hausdorff_lipschitz_on_bound R X Y (s @` E) (fun y=>f (t y)) lambda m (s @` B)
  hForward hSourceImage.
rewrite hForwardImage in hF.
have hBack:@is_metric_lipschitz_bound R Y X (f @` E) (fun y=>s (u y)) lambda.
  split; first exact hForward.1.
  move=>y z [x hx <-] [w hw <-].
  change (is_true (inner_norm (@euclidean_inner_productP R m) (s (u (f x))-s (u (f w)))<=
    lambda*inner_norm (@euclidean_inner_productP R n) (f x-f w)))%R.
  rewrite (hVal x hx) (hVal w hw).
  exact (hInverse (f x) (f w) x w ((hg (f x) x).2 (conj hx (erefl _)))
    ((hg (f w) w).2 (conj hw (erefl _)))).
have hImageSubset:f @` B `<=` f @` E by move=>y [x hx <-]; exists x; first exact:hBE; by [].
have hBackImage:(fun y:Y=>s (u y)) @` (f @` B)=s @` B.
  apply/seteqP; split=>v.
  - move=>[y [x hx <-] <-]; rewrite (hVal x (hBE x hx)); by exists x.
  - move=>[x hx <-]; exists (f x); last by rewrite (hVal x (hBE x hx)).
    by exists x.
have hI:=@hausdorff_lipschitz_on_bound R Y X (f @` E) (fun y=>s (u y)) lambda m (f @` B)
  hBack hImageSubset.
rewrite hBackImage in hI.
have hLinear:@hausdorff_measure R X m (s @` B)=
    `|euclidean_det (hom_as_linear s)|%:E*euclidean_lebesgue_measure m B.
  rewrite euclidean_norm_hausdorff_lebesgue.
  exact (euclidean_lebesgue_linear_image (hom_as_linear s) B).
by rewrite hLinear in hF hI; split.
Qed.
