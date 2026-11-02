(** Federer (1969), 3.1.1, p. 211: the operator space Z is
    separable when X is finite dimensional and Y is separable.
    Approximate finitely many basis values by a dense sequence and
    use the abstract operator representation and coordinate bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis BasisInterpolation
  NormFiniteLinearBound SeparablePointSequenceUP SeparablePointSequenceSealed
  SeparableClosedCover ContinuousOperatorUP ContinuousOperatorNorm
  ContinuousOperatorFiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_operator_separable]: separability of
    Z in 3.1.1, p. 211. Countably many finite basis prescriptions
    give a dense family, also when the basis is empty. *)
Theorem continuous_operator_separable (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (evaluation : Hom Z (Hom X Y)) (ZN : Z -> R)
    (hZ : is_continuous_operator_space NX NY evaluation ZN)
    n (e : 'I_n -> X) (he : is_basis e) :
  (exists D : set (real_norm_metric_space hNY), countable D /\ dense D) ->
  exists D : set (real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)),
    countable D /\ dense D.
Proof.
move=> [D [hD hd]].
pose hZN := continuous_operator_norm_is_norm hNY hZ.
pose E := real_norm_metric_space hZN.
pose T := real_norm_metric_space hNY.
pose s := @SeparablePointSequence.value R T 0 D hD hd.
have hs := (@SeparablePointSequence.laws R T 0 D hD hd).2.
pose L (c : {ffun 'I_n -> nat}) := hom_of_linear (@basis_interpolation R (Choice.clone 'I_n _) X Y e he (fun i=>(s (c i) : Y))).
have hc c : exists z, evaluation z=L c.
  apply: (continuous_operator_surjective hZ).
  exact: (@norm_finite_linear_bounded R X Y NX NY hNX hNY n e he (L c)).
pose z c := projT1 (cid (hc c)).
have hz c := projT2 (cid (hc c)).
exists ((fun c => (z c : E)) @` setT); split.
- apply: sub_countable (card_image_le _ _) _; exact: countableP.
- move=> W [w hw] ho.
  have hn : nbhs w W by rewrite openE in ho; exact: ho w hw.
  have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP w W) hn.
  have [K [hK hbound]] := continuous_operator_finite_coordinate_bound hNX hNY hZ he.
  have hr' : 0<r := hr.
  have hp : 0<K+1 by lra.
  have hdelta : 0<r/(K+1) by rewrite divr_gt0.
  have hi i : exists k : nat, NY (evaluation w (e i)-s k)<r/(K+1).
    have [v [[k _ <-] hv]] := metric_dense_point_near hs (evaluation w (e i) : T) hdelta.
    by exists k.
  pose c := [ffun i : 'I_n => projT1 (cid (hi i))].
  have hsmall i : NY (evaluation (w-z c) (e i))<=r/(K+1).
    have heval : evaluation (z c) (e i)=s (c i).
      by rewrite hz /L hom_of_linearE basis_interpolationE.
    rewrite linearB.
    change (NY (evaluation w (e i)-evaluation (z c) (e i))<=r/(K+1)).
    rewrite heval /c ffunE.
    exact: ltW (projT2 (cid (hi i))).
  have hle := hbound (w-z c) (r/(K+1)) (ltW hdelta) hsmall.
  have hnear : ZN (w-z c)<r.
    apply: le_lt_trans hle _.
    have hprod : (K+1)*(r/(K+1))=r by rewrite mulrC divfK //; apply/eqP; lra.
    nra.
  exists (z c); split; first exact: hb _ hnear.
  by exists c.
Qed.
