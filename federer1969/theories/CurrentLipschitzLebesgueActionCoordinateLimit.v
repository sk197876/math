(** Federer (1969), 4.1.25, p. 383: convergence
    of all finitely many coordinate differentials implies
    operator-norm convergence. Reuse the coordinate reconstruction
    of 3.1.1, p. 211, and the operator-norm
    least-bound law of 1.7.6, pp. 33–34.
    The empty coordinate family includes dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanCoordinateTopology EuclideanCoordinateMetric EuclideanCoordinateHom
  EuclideanHomOperator HomSpaceTopology FinitePositiveRadiusCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LebesgueActionCoordinateLimit.
Variable R : realType.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Op := (@euclidean_operator_norm R m n).
Local Notation basis := (@coordinate_basis R m).

(** Source for [current_lipschitz_lebesgue_action_coordinate_norm_bound]:
    the sum bound from the original coordinate expansion,
    3.1.1, p. 211, controls the differential norm
    in the proof of 4.1.25, p. 383.
    No positive source dimension is assumed. *)
Lemma current_lipschitz_lebesgue_action_coordinate_norm_bound (A:Hom X Y) :
  Op A <= \sum_(i:'I_m) NY (A (basis i)).
Proof.
have hReconstruct : A = @coordinate_hom R m Y (fun i=>A (basis i)).
  apply:hom_ext=>x.
  rewrite coordinate_homE -{1}(euclidean_coordinate_expansion x).
  rewrite linear_sum; apply:eq_bigr=>i _.
  exact:linearZ.
apply:hom_operator_norm_least.
- apply:sumr_ge0=>i _; exact:real_seminorm_nonnegative hNY.1 _.
- move=>x.
  have hBound := @coordinate_hom_bound R m Y NY hNY
    (fun i=>A (basis i)) x.
  have hWeights : (\sum_i NX (basis i)*NY (A (basis i))) =
      \sum_i NY (A (basis i)).
    apply:eq_bigr=>i _.
    by rewrite euclidean_coordinate_unit_norm mul1r.
  rewrite hWeights -hReconstruct in hBound.
  by rewrite mulrC; exact:hBound.
Qed.

(** Source for [current_lipschitz_lebesgue_action_coordinate_limit]:
    finitely many directional smoothing limits give the full
    bounded differential limit invoked in 4.1.25, p. 383.
    The common positive radius comes from the preceding
    finite-radius selection law, with its empty-family endpoint. *)
Theorem current_lipschitz_lebesgue_action_coordinate_limit
    (A:R->Hom X Y) (B:Hom X Y) :
  (forall i:'I_m, forall eta:R, 0<eta -> exists delta:R,
    0<delta /\ forall e:R, 0<e -> e<delta ->
      NY (A e (basis i)-B (basis i))<eta) ->
  forall eta:R, 0<eta -> exists delta:R,
    0<delta /\ forall e:R, 0<e -> e<delta -> Op (A e-B)<eta.
Proof.
move=>hCoordinates eta hEta.
have hDimension : (0 < (m%:R:R)+1)%R.
  exact:(@ltr_wpDl R 0 (m%:R) 1 (ler0n R m) ltr01).
have hScaled : 0 < eta/(m%:R+1) by rewrite divr_gt0.
have hEach i : exists delta:R, 0<delta /\ forall e:R,
    0<e<delta -> NY (A e (basis i)-B (basis i))<eta/(m%:R+1).
  have [delta [hDelta hBound]] := hCoordinates i (eta/(m%:R+1)) hScaled.
  exists delta; split=>//e /andP[he hSmall]; exact:hBound e he hSmall.
have [delta [hDelta hBound]] := @finite_common_positive_radius_bound R
  [the finType of 'I_m]
  (fun i e=>NY (A e (basis i)-B (basis i))<eta/(m%:R+1)) hEach.
exists delta; split=>//e he hSmall.
have hRange : 0<e<delta by apply/andP; split.
apply:le_lt_trans (current_lipschitz_lebesgue_action_coordinate_norm_bound (A e-B)) _.
have hSum : (\sum_(i:'I_m) NY ((A e-B) (basis i))) <=
    \sum_(i:'I_m) eta/(m%:R+1).
  apply:ler_sum=>i _.
  change (is_true (NY (A e (basis i)-B (basis i))<=eta/(m%:R+1))).
  exact:ltW (hBound e hRange i).
apply:le_lt_trans hSum _.
rewrite sumr_const card_ord.
have hIdentity : eta/(m%:R+1) *+ m = (eta * m%:R)/(m%:R+1).
  by rewrite -[LHS]mulr_natr mulrAC.
rewrite hIdentity (ltr_pdivrMr _ _ hDimension) mulrDr mulr1 ltrDl.
exact:hEta.
Qed.
End LebesgueActionCoordinateLimit.
