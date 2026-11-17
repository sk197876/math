(** Federer 2.10.27, p. 191: supporting change of centre and
    radius in the real ball-section integral. Reuse the exact
    Lebesgue homothety and translation laws of 2.7.16 and the
    injective image-integral theorem of 2.4.18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueTranslation ProjectedVolumeDilation
  AffineDilation MeasureUP MeasurePushforward MeasureScaleIntegral InjectivePushforwardIntegral
  MeasureIntegralUP MeasureIntegralGraphEquivalence PartialFunctionPrecomposition
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [euclidean_positive_affine_integral]: the radius
    and centre transport underlying the first display of Federer
    2.10.27, p. 191. A positive scalar radius multiplies the
    actual finite integral by its natural-dimensional volume power;
    the zero-dimensional base is retained. *)
Lemma euclidean_positive_affine_integral (R:realType) m
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R)
    (f:inner_metric_space (@euclidean_inner_productP R m)->R) (a:R):
  0<r ->
  is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand f) a%:E ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (fun x=>f (r^-1*:(x-u)))) (r^+m*a)%:E.
Proof.
move=> hr hi.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose T (x:X):X:=r^-1*:(x-u).
pose V (x:X):X:=u+r*:x.
have hrNe:r!=0:=lt0r_neq0 hr.
have hVT:cancel V T.
  by move=> x;rewrite /T /V addrAC subrr add0r scalerA mulVf // scale1r.
have hTV:cancel T V.
  by move=> x;rewrite /T /V scalerA mulfV // scale1r addrC subrK.
have hPush:measure_pushforward T mu=measure_scale (r^+m) mu.
  apply:funext=> A.
  have hPre:T @^-1` A=V @` A.
    apply/seteqP;split=> x.
    + move=> hx;exists (T x)=> //;exact:hTV.
    + move=> [z hz <-];change (A (T (V z)));by rewrite hVT.
  have hImage:V @` A=[set u+z|z in (@affine_dilation R (R_n R m) 0 r) @` A].
    apply/seteqP;split=> x.
    + move=> [z hz <-];exists (r*:z).
      * exists z=> //;by rewrite /affine_dilation scaler0 add0r.
      * by [].
    + move=> [z [w hw <-] <-];exists w=> //.
      by rewrite /V /affine_dilation scaler0 add0r.
  rewrite /measure_pushforward /measure_scale /mu hPre hImage euclidean_lebesgue_translation
    euclidean_affine_dilation_volume (ger0_norm (ltW hr));by [].
have hScale:=@measure_scale_integral R X mu hm (r^+m) (exprn_gt0 m hr)
  (real_total_integrand f) a%:E hi.
rewrite -EFinM -hPush in hScale.
have hTransport:=(@injective_pushforward_integral_iff R X X mu hm T
  (real_total_integrand f) (can_inj hTV) (r^+m*a)%:E).2 hScale.
exact:(measure_integral_graph_equivalent (fun x z=>iff_refl _) hTransport).
Qed.
