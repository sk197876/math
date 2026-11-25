(** Federer (1969), 3.2.26(2), p. 261: translating
    a thin unit-disc neighbourhood to w and scaling it
    by r multiplies its cost by r^m. Derive the
    actual normalized gauge law from Euclidean volume scaling
    and positive homogeneity of the probability norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueTranslation AffineDilation ProjectedVolumeDilation
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability
  OrthogonalProjectionProbability IntegralGeometricGauge NonnegativeExtendedNormScale
  SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_shift_scale_volume]: the affine
    volume scaling used for C(w,r) in 3.2.26(2),
    p. 261, from 2.7.16(1), pp. 134–135.
    The source set can be arbitrary, including unbounded
    sets; singular zero scaling retains the established convention. *)
Lemma euclidean_shift_scale_volume (R:realType) m
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (a:R_n R m) (r:R):
  @euclidean_lebesgue_measure R m ((fun x=>(a+r*:x)%R) @` A)=
    ((`|r|^+m)%R%:E*@euclidean_lebesgue_measure R m A).
Proof.
have hImage:(fun x=>(a+r*:x)%R) @` A=
    [set (a+y)%R|y in (@affine_dilation R (R_n R m) (0%R:R_n R m) r) @` A].
  apply/seteqP; split=>y.
  - move=>[x hx <-]; exists ((r*:x)%R); last reflexivity.
    exists x; first exact hx; by rewrite /affine_dilation scaler0 add0r.
  - move=>[z [x hx <-] <-]; exists x; first exact hx.
    by rewrite /affine_dilation scaler0 add0r.
by rewrite hImage euclidean_lebesgue_translation euclidean_affine_dilation_volume.
Qed.

(** Source for [projected_volume_shift_scale]: the projected
    version of the homothety calculation in 3.2.26(2),
    p. 261. Orthogonal projections commute with translation
    and scalar multiplication, so every actual projected
    volume is multiplied by |r|^m. *)
Lemma projected_volume_shift_scale (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:R_n R n) (r:R) (p:orthogonal_projection_metric_space R n m):
  projected_volume_function ((fun x=>(a+r*:x)%R) @` A) p=
    (`|r|^+m)%R%:E*projected_volume_function A p.
Proof.
have hImage:euclidean_projection_linear p @` ((fun x=>(a+r*:x)%R) @` A)=
    (fun y=>(euclidean_projection_linear p a+r*:y)%R) @` (euclidean_projection_linear p @` A).
  apply/seteqP; split=>y.
  - move=>[z [x hx <-] <-]; exists (euclidean_projection_linear p x); first by exists x.
    by rewrite linearD linearZ.
  - move=>[z [x hx <-] <-]; exists ((a+r*:x)%R); first by exists x.
    by rewrite linearD linearZ.
by rewrite /projected_volume_function hImage euclidean_shift_scale_volume.
Qed.

(** Source for [integral_geometric_positive_similarity_gauge]: the
    cost identity zeta_t(C(w,r))=r^m g used in
    3.2.26(2), p. 261. Both finite exponents and
    infinity use the same exact positive homogeneity law
    of the actual extended-input probability norm. *)
Theorem integral_geometric_positive_similarity_gauge (R:realType) n m
    (hmn:(m<=n)%N) (t: \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (a:R_n R n) (r:R):
  1<=t ->is_suslin_set R A ->(0<r)%R ->
  @integral_geometric_gauge R n m hmn t ((fun x=>(a+r*:x)%R) @` A)=
    (r^+m)%R%:E*@integral_geometric_gauge R n m hmn t A.
Proof.
move=>ht hA hr.
pose P:=orthogonal_projection_metric_space R n m.
pose theta:=@orthogonal_projection_probability R n m hmn.
have hMeas:=@theta_star_projected_volume_measurable R n m hmn A hA.
have hFunction:projected_volume_function ((fun x=>(a+r*:x)%R) @` A)=
    (fun p:P=>(r^+m)%R%:E*projected_volume_function A p).
  apply:funext=>p; by rewrite projected_volume_shift_scale (ger0_norm (ltW hr)).
rewrite /integral_geometric_gauge hFunction
  (@nonnegative_extended_norm_scale R P theta (@theta_star_is_measure R n m hmn)
    (projected_volume_function A) t (r^+m)%R (fun p=>projected_volume_function_nonnegative A p)
    ht (exprn_ge0 m (ltW hr)) hMeas).
by rewrite muleCA.
Qed.
