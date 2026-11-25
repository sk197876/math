(** Federer (1969), 4.1.25, p. 383: the
    actual differentials and map values of the smoothings
    give pointwise limits of the paired image integrands.
    Reuse the finite multilinear difference estimate proved
    for 4.1.14, p. 372. The original differential
    may have arbitrary rank. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormClassOneUP
  RealFunctionalNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness ExteriorGrading ExteriorMaps AlternatingForms
  AlternatingDual AlternatingPairing CurrentCoefficientNorms CurrentDualNorm
  EuclideanHomOperator CurrentFormPullbackDifferenceBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LebesgueActionPullbackLimit.
Variable R : realType.
Hypothesis h2 : (1+1:R) != 0.
Variables m n k : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation PN := (@current_form_comass R h2 m k).
Local Notation QN := (@current_form_comass R h2 n k).
Local Notation hQN := (@current_form_comass_real_norm R h2 n k).
Local Notation MX := (@current_vector_mass R h2 m k).
Local Notation hMX := (@current_vector_mass_real_norm R h2 m k).
Local Notation Op := (@euclidean_operator_norm R m n).
Local Notation pull A := (@A_m_dual R X Y R^o (hom_as_linear A) k).
Variables (A:nat->Hom X Y) (B:Hom X Y) (z:nat->Y) (y:Y) (c:R).
Hypothesis hC : 1<=c.
Hypothesis hA : forall i, Op (A i)<=c.
Hypothesis hB : Op B<=c.
Hypothesis hValues : forall eta:R,0<eta -> exists N:nat,
  forall i:nat,(N<=i)%N -> NY (z i-y)<eta.
Hypothesis hDifferentials : forall eta:R,0<eta -> exists N:nat,
  forall i:nat,(N<=i)%N -> Op (A i-B)<eta.
Variable phi : Y->A_m Y R^o k.
Hypothesis hPhi : norm_class_zero NY QN setT phi.

(** Source for [current_lipschitz_lebesgue_action_pullback_limit]:
    bounded differential convergence and convergence of map
    values imply convergence of actual pullbacks, as used
    in the first proof of 4.1.25, p. 383.
    Only continuity of the fixed form at the limiting
    image point is used. *)
Theorem current_lipschitz_lebesgue_action_pullback_limit :
  forall eta:R,0<eta -> exists N:nat,forall i:nat,(N<=i)%N ->
    PN (pull (A i) (phi (z i))-pull B (phi y))<eta.
Proof.
have hc : 0<=c := le_trans ler01 hC.
pose b:=QN (phi y).
have hb : 0<=b := real_seminorm_nonnegative hQN.1 (phi y).
pose C:=c^+k+k%:R*(b*c^+k).
have hPower : 0<=c^+k := exprn_ge0 k hc.
have hCoefficient : 0<=C.
  apply:addr_ge0; first exact:hPower.
  exact:mulr_ge0 (ler0n _ _) (mulr_ge0 hb hPower).
have hDenominator : 0<C+1 := ltr_wpDl hCoefficient ltr01.
move=>eta hEta.
pose tolerance:=eta/(C+1).
have hTolerance : 0<tolerance by rewrite /tolerance divr_gt0.
have [delta [hDelta hForm]] := (@hPhi y Logic.I).2 tolerance hTolerance.
have [NValue hValue] := @hValues delta hDelta.
have [NDifferential hDifferential] := @hDifferentials tolerance hTolerance.
exists (maxn NValue NDifferential)=>i hi.
have hIV : (NValue<=i)%N := leq_trans (leq_maxl _ _) hi.
have hID : (NDifferential<=i)%N := leq_trans (leq_maxr _ _) hi.
have hFormSmall : QN (phi (z i)-phi y)<=tolerance.
  have h:=@hForm (z i-y) Logic.I (@hValue i hIV).
  have hAdd:y+(z i-y)=z i by rewrite addrC subrK.
  rewrite hAdd in h;exact:ltW h.
have hDifference : Op (A i-B)<=tolerance := ltW (@hDifferential i hID).
have hBound := @current_form_pullback_difference_bound R h2 m n k
  (A i) B c tolerance (phi (z i)) (phi y)
  hC (ltW hTolerance) (hA i) hB hDifference.
have hTotal : PN (pull (A i) (phi (z i))-pull B (phi y))<=tolerance*C.
  apply:le_trans hBound _.
  have hFirst:=ler_wpM2r hPower hFormSmall.
  have hSecond:=lexx (k%:R*(b*(tolerance*c^+k))).
  have hSum:=lerD hFirst hSecond.
  have hAlgebra:tolerance*c^+k+k%:R*(b*(tolerance*c^+k))=tolerance*C.
    rewrite /C; ring.
  by rewrite hAlgebra in hSum.
apply:le_lt_trans hTotal _.
have hStrict:tolerance*C<tolerance*(C+1) by rewrite ltr_pM2l // ltrDl.
by rewrite /tolerance divfK ?(lt0r_neq0 hDenominator) in hStrict.
Qed.

(** Source for [current_lipschitz_lebesgue_action_point_pairing_limit]:
    pair the preceding pullback limit with the original
    summable field value, supporting 4.1.25, p. 383.
    Neither simplicity nor nonzero mass of that value
    is needed for the limit. *)
Theorem current_lipschitz_lebesgue_action_point_pairing_limit
    (xi:exterior_power X k) :
  forall eta:R,0<eta -> exists N:nat,forall i:nat,(N<=i)%N ->
    `|pairing (exterior_power_map (hom_as_linear (A i)) k xi) (phi (z i))-
      pairing (exterior_power_map (hom_as_linear B) k xi) (phi y)|<eta.
Proof.
pose r:=MX xi.
have hr:0<=r:=real_seminorm_nonnegative hMX.1 xi.
have hPositive:0<r+1:=ltr_wpDl hr ltr01.
move=>eta hEta.
have hScaled:0<eta/(r+1) by rewrite divr_gt0.
have [N hN]:=@current_lipschitz_lebesgue_action_pullback_limit
  (eta/(r+1)) hScaled.
exists N=>i hi.
rewrite -!A_m_dual_pairing
  -(Bilinear.linB ((@pairing_bilinear R X R^o k).2 xi)).
have hDual:=real_functional_norm_bound
  (@current_mass_pairing_norm R h2 m k xi)
  (pull (A i) (phi (z i))-pull B (phi y)).
apply:le_lt_trans hDual _.
have hNorm:0<=PN (pull (A i) (phi (z i))-pull B (phi y)).
  exact:real_seminorm_nonnegative (@current_form_comass_real_norm R h2 m k).1 _.
have hWide:r*PN (pull (A i) (phi (z i))-pull B (phi y))<=
    (r+1)*PN (pull (A i) (phi (z i))-pull B (phi y)).
  apply:ler_wpM2r; first exact:hNorm.
  by rewrite lerDl.
apply:le_lt_trans hWide _.
have hProduct:(r+1)*PN (pull (A i) (phi (z i))-pull B (phi y))<
    (r+1)*(eta/(r+1)).
  rewrite (ltr_pM2l hPositive); exact:hN i hi.
by rewrite [X in _ < X]mulrC divfK ?(lt0r_neq0 hPositive) in hProduct.
Qed.
End LebesgueActionPullbackLimit.
