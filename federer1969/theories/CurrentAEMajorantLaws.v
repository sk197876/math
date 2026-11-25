(** Federer (1969), 4.1.14, pp. 371–372: supporting laws
    for the original continuous almost-everywhere differential
    majorant. Positivity follows from full-support Lebesgue measure;
    a local representative retains the actual differential graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLocalAgreement NormClassOneUP GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HomSpaceTopology
  EuclideanHomOperator CurrentMapDifferential EuclideanLebesgueDimensions
  MeasureAlmostUP MeasureAlmostBasic EuclideanContinuousAENonnegative
  CurrentCompactMajorantApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentAEMajorantLaws.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Op:=(@euclidean_operator_norm R n nu).
Variables (U:set X) (f:X->Y) (sigma:X->R^o).

(** Source for [current_ae_differential_majorant_nonnegative]: the
    continuous sigma in Federer 4.1.14, p. 371, is nonnegative at
    every point of U, including source dimension zero. No such
    premise is added to the original theorem. *)
Theorem current_ae_differential_majorant_nonnegative:
  norm_class_zero NX (fun t:R^o=>`|t|) U sigma ->
  @is_current_ae_differential_majorant R n nu U f sigma ->
  forall x,U x->0<=sigma x.
Proof.
move=>hContinuous hAE.
apply:(@euclidean_continuous_ae_nonnegative R n U sigma hContinuous).
apply:(@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ _ _ hAE)=>x hx hUx.
have[D [hD hBound]]:=hx hUx.
have hNonnegative:0<=Op D by exact:hom_operator_norm_nonnegative.
exact:(le_trans hNonnegative hBound).
Qed.

(** Source for [current_ae_differential_majorant_total_cap]: the actual
    partial Df in Federer 4.1.14, p. 371, agrees almost everywhere
    with its existing total representative. This follows from graph
    uniqueness, not a new assumption about that representative. *)
Theorem current_ae_differential_majorant_total_cap:
  @is_current_ae_differential_majorant R n nu U f sigma ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set x|U x->Op (@current_map_differential R n nu U f x)<=sigma x].
Proof.
move=>hAE.
apply:(@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ _ _ hAE)=>x hx hUx.
have[D [hD hBound]]:=hx hUx.
by rewrite (@current_map_differential_unique R n nu U f x D hD).
Qed.

(** Source for [current_ae_differential_majorant_local_agreement]:
    the smoothing argument of Federer 4.1.14, p. 371, is local
    on the original open U. A total ambient field agreeing with
    f on an open plateau W has the same actual differential
    almost everywhere on W. It need not take ambient values in V. *)
Theorem current_ae_differential_majorant_local_agreement (W:set X) (F:X->Y):
  (forall x,W x->norm_domain_interior NX W x) ->W `<=` U ->
  (forall x,W x->f x=F x) ->
  @is_current_ae_differential_majorant R n nu U f sigma ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set x|W x->exists D:Hom X Y,
      has_norm_differential NX NY setT F x D /\ Op D<=sigma x].
Proof.
move=>hW hWU hAgreement hAE.
apply:(@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ _ _ hAE)=>x hx hWx.
have[D [hD hBound]]:=hx (hWU x hWx).
have[r [hr hBall]]:=hW x hWx.
exists D;split;last exact:hBound.
apply:(@norm_differential_local_agreement R X Y NX NY hNX U setT f F x D r hr).
- move=>h hh;split;first by [].
  move=>_;exact:hWU (x+h) (hBall h hh).
- move=>h hh _;exact:hAgreement (x+h) (hBall h hh).
- exact:hD.
Qed.
End CurrentAEMajorantLaws.
