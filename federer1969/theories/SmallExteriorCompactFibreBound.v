(** Federer (1969), 3.2.31, p. 269: supporting local
    quantitative bound with the actual small exterior majorant.
    The coefficient combines 3.2.30 and the rough fibre estimate
    of 2.10.25 with Lipschitz bound one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanHausdorffLebesgue
  EuclideanLinearJacobian LinearHausdorffMeasureImage LipschitzUP HausdorffMeasure
  HausdorffFibreCutoffs HausdorffFibreCost MeasureUP MeasureBasic
  PartialFunctionUP PartialFunctionBasic MeasureIntegralBounds
  SmallExteriorMajorantUP CompactRescaledFibreIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section SmallExteriorBound.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [small_exterior_compact_fibre_integral_bound]:
    supporting displayed bound in Federer 3.2.31, p. 269.
    The actual exterior norm is below epsilon, and the actual
    inverse-rescaled map has unit Lipschitz bound on K. With
    m=k+mu, the coefficient is v^(mu/2) 2^(mu-1) times
    alpha(k) alpha(mu)/alpha(m), exactly as in the book.
    Source mass is finite because K is compact, not by premise. *)
Theorem small_exterior_compact_fibre_integral_bound (G:X->Y) (K:set X) k mu
    (D:Hom (R_n R m) (R_n R v)) epsilon (T U:Hom (R_n R v) (R_n R v)):
  (0<v)%N ->(0<mu)%N ->m=(k+mu)%N ->(0<epsilon)%R ->
  continuous G ->compact K ->@is_small_exterior_majorant R m v mu D epsilon T U ->
  @is_metric_lipschitz_bound R X Y K (fun x=>U (G x)) 1%R ->
  measure_upper_integral (@hausdorff_measure R Y mu)
    (partial_function_total (hausdorff_fibre_mass G K k))<=
    (((Num.sqrt v%:R)^+mu*2^+mu.-1*epsilon)%R)%:E*
      ((@hausdorff_fibre_bound_constant R k mu 1%R)%:E*
        @euclidean_lebesgue_measure R m K).
Proof.
move=>hv hmu hDim heps hG hK hMajor hLip.
pose C:R:=((Num.sqrt v%:R)^+mu*2^+mu.-1)%R.
have hV:(0<(v%:R:R))%R by rewrite ltr0n.
have hRoot:(0<Num.sqrt (v%:R:R))%R by rewrite sqrtr_gt0.
have hC:(0<C)%R.
  apply:mulr_gt0; apply:exprn_gt0=>//; by rewrite ltr0n.
have hC0:(0<=C)%R:=ltW hC.
have hCE:0<=C%:E by rewrite lee_fin.
have hSmall:(euclidean_linear_jacobian mu T<epsilon)%R.
  exact (@small_exterior_majorant_small_norm R m v mu D epsilon T U hMajor).
have hImage A:@hausdorff_measure R Y mu (T @` A)<=
    (C*epsilon)%R%:E*@hausdorff_measure R Y mu A.
  have hBound:=@linear_hausdorff_measure_exterior_bound R v v mu T A hmu.
  have hCoef:(C*euclidean_linear_jacobian mu T<=C*epsilon)%R.
    exact (ler_wpM2l hC0 (ltW hSmall)).
  apply:le_trans hBound _.
  apply:lee_wpmul2r; first exact (@measure_nonnegative R Y (@hausdorff_measure R Y mu)
    (@hausdorff_measure_is_measure R Y mu) A).
  by rewrite lee_fin.
have hSource:@hausdorff_measure R X (k+mu) K=@euclidean_lebesgue_measure R m K.
  rewrite -hDim; exact:(euclidean_hausdorff_spherical_lebesgue K).1.
have hFinite:@hausdorff_measure R X (k+mu) K< +oo.
  rewrite hSource; exact:euclidean_compact_finite hK.
have hc:(0<C*epsilon)%R:=mulr_gt0 hC heps.
have hBound:=@compact_rescaled_fibre_integral_bound R m v G K k mu T U (C*epsilon)%R
  hG hK hFinite (small_exterior_majorant_left_inverse hMajor)
  (small_exterior_majorant_right_inverse hMajor) hc hImage hLip.
by rewrite hSource in hBound.
Qed.
End SmallExteriorBound.
