(** Supporting results for Federer (1969), 2.7.18, printed p. 141: the
    estimate "int |v_g - v_h| dgamma <= int |w_g - w_h| dgamma + chi(g)
    epsilon + chi(h) epsilon" uses int |v - w|_g dgamma = chi(g) int |v - w|
    dgamma, that is, A_g#(gamma) = chi(g) gamma together with the
    integration of a function with respect to the measure chi(g) gamma. This
    module treats the measure c phi : S |-> c phi(S) for a measure phi and a
    real number c > 0. It has the same measurable sets, null sets and
    measurable functions as phi (2.1.2, p. 54; 2.3.1, p. 72; 2.3.2, p. 73);
    its step integrals are c times those of phi, by 2.1.1(6), p. 52; hence
    its upper, lower and full integrals of 2.4.2, p. 81, are c times those
    of phi. It is L regular in the sense of 2.5.3, p. 94, whenever phi is,
    and it represents c A whenever phi represents A. Federer uses these
    facts without comment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  NumericalSumScale MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureStepFunctionUP
  MeasureIntegralUP FiniteMeasureScaling FunctionLatticeLevelFamilies FunctionLatticeRegularityUP
  RealIntegralFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_scale]: the measure c phi, S |-> c phi(S),
    used in Federer 2.7.18, p. 141, as chi(g) gamma, and in 2.7.1,
    p. 122, "A_g#(mu) = chi(g) mu". Direct definition. *)
Definition measure_scale (R : realType) (X : choiceType) (c : R) (mu : set X -> \bar R) :
    set X -> \bar R :=
  fun S => c%:E * mu S.

Section MeasureScale.
Variable R : realType.
Variable X : choiceType.

(** Source for [measure_scale_inverse]: c^{-1} (c phi) = phi for
    c > 0, supporting the transfer of integrals in Federer 2.7.18,
    p. 141. *)
Lemma measure_scale_inverse (mu : set X -> \bar R) (c : R) :
  (0 < c)%R -> measure_scale c^-1 (measure_scale c mu) = mu.
Proof.
move=> hc; apply: funext=> S.
by rewrite /measure_scale muleA -EFinM mulVf ?gt_eqF // mul1e.
Qed.

(** Source for [measure_scale_is_measure]: c phi is a measure for
    c > 0, Federer 2.1.1(6), p. 52, and 2.1.2, p. 53, as used in
    2.7.18, p. 141. *)
Lemma measure_scale_is_measure (mu : set X -> \bar R) (c : R) :
  is_measure mu -> (0 < c)%R -> is_measure (measure_scale c mu).
Proof.
by move=> hm hc; rewrite /measure_scale; exact: (@finite_scale_is_measure R X mu hm c (ltW hc)).
Qed.

Section Forward.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Variable c : R.
Hypothesis hc : (0 < c)%R.
Local Notation cmu := (measure_scale c mu).

(** Source for [measure_scale_measurable]: the phi measurable sets are
    c phi measurable, Federer 2.1.2, p. 54, supporting 2.7.18,
    p. 141. *)
Lemma measure_scale_measurable (M : set X) : measure_measurable mu M -> measure_measurable cmu M.
Proof.
move=> hM T; rewrite /measure_scale (hM T) ge0_muleDr //; exact: (measure_nonnegative hm).
Qed.

(** Source for [measure_scale_almost_everywhere]: the phi null sets
    are c phi null, Federer 2.3.1, p. 72, supporting 2.7.18,
    p. 141. *)
Lemma measure_scale_almost_everywhere (P : set X) :
  measure_almost_everywhere mu P -> measure_almost_everywhere cmu P.
Proof. by rewrite /measure_almost_everywhere /measure_scale=> ->; rewrite mule0. Qed.

(** Source for [measure_scale_measurable_function]: phi measurable
    functions are c phi measurable, Federer 2.3.2, p. 73, supporting
    2.7.18, p. 141. *)
Lemma measure_scale_measurable_function (Y : topologicalType) (f : partial_function X Y) :
  is_measure_measurable_function mu f -> is_measure_measurable_function cmu f.
Proof.
move=> [hd ho]; split; first exact: measure_scale_almost_everywhere.
by move=> U hU; apply: measure_scale_measurable; exact: ho U hU.
Qed.

(** Source for [measure_scale_step_integral]: the step integral with
    respect to c phi is c times that with respect to phi, Federer
    2.4.1, p. 80, with 2.1.1(6), p. 52. *)
Lemma measure_scale_step_integral (u : partial_function X (real_line_metric R)) z :
  is_measure_step_integral mu u z -> is_measure_step_integral cmu u (c%:E * z).
Proof.
rewrite /is_measure_step_integral /measure_scale=> hz.
have he : (fun y : R => y%:E * (c%:E * mu (partial_function_preimage u [set y]))) =
    (fun y : R => c%:E * (y%:E * mu (partial_function_preimage u [set y]))).
  by apply: funext=> y; rewrite muleCA.
by rewrite he numerical_sum_positive_scale // hz.
Qed.

(** Source for [measure_scale_step_function]: phi step functions are
    c phi step functions, Federer 2.4.1, p. 80. *)
Lemma measure_scale_step_function (u : partial_function X (real_line_metric R)) :
  is_measure_step_function mu u -> is_measure_step_function cmu u.
Proof.
move=> [hf hr [z hz]]; split=> //; first exact: measure_scale_measurable_function.
by exists (c%:E * z); exact: measure_scale_step_integral.
Qed.

(** Source for [measure_scale_upper_value]: if a is the integral of a
    phi upper function of f, then c a is the integral of a c phi upper
    function of f, Federer 2.4.2, p. 81. *)
Lemma measure_scale_upper_value (f : partial_function X (extended_real_line R)) a :
  measure_upper_step_values mu f a -> measure_upper_step_values cmu f (c%:E * a).
Proof.
move=> [u [[hu hl] hi]]; exists u; split; last exact: measure_scale_step_integral.
by split; [exact: measure_scale_step_function|exact: measure_scale_almost_everywhere].
Qed.

(** Source for [measure_scale_lower_value]: the lower-function analogue
    of measure_scale_upper_value, Federer 2.4.2, p. 81. *)
Lemma measure_scale_lower_value (f : partial_function X (extended_real_line R)) a :
  measure_lower_step_values mu f a -> measure_lower_step_values cmu f (c%:E * a).
Proof.
move=> [u [[hu hl] hi]]; exists u; split; last exact: measure_scale_step_integral.
by split; [exact: measure_scale_step_function|exact: measure_scale_almost_everywhere].
Qed.

End Forward.

Section Integral.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Variable c : R.
Hypothesis hc : (0 < c)%R.
Local Notation cmu := (measure_scale c mu).

(** Source for [hci]: c^{-1} > 0, so that phi = c^{-1} (c phi) is
    again a positive multiple; supporting lemma for 2.4.2, p. 81, as
    used in Federer 2.7.18, p. 141. *)
Let hci : (0 < c^-1)%R.
Proof. by rewrite invr_gt0. Qed.

(** Source for [hcm]: c phi is a measure, Federer 2.1.2, p. 53;
    supporting lemma for 2.7.18, p. 141. *)
Let hcm : is_measure cmu.
Proof. exact: measure_scale_is_measure. Qed.

(** Source for [measure_scale_cancel]: c (c^{-1} b) = b, supporting the
    transfer of integrals in Federer 2.7.18, p. 141. *)
Let measure_scale_cancel (b : \bar R) : c%:E * (c^-1%:E * b) = b.
Proof. by rewrite muleA -EFinM mulfV ?gt_eqF // mul1e. Qed.

(** Source for [measure_scale_cancel_left]: c^{-1} (c b) = b,
    supporting the transfer of integrals in Federer 2.7.18, p. 141. *)
Let measure_scale_cancel_left (b : \bar R) : c^-1%:E * (c%:E * b) = b.
Proof. by rewrite muleA -EFinM mulVf ?gt_eqF // mul1e. Qed.

(** Source for [measure_scale_upper_value_inverse]: every value of a
    c phi upper function of f is c times the value of a phi upper
    function of f, Federer 2.4.2, p. 81. *)
Lemma measure_scale_upper_value_inverse (f : partial_function X (extended_real_line R)) b :
  measure_upper_step_values cmu f b -> measure_upper_step_values mu f (c^-1%:E * b).
Proof.
move=> hb; have h := @measure_scale_upper_value cmu hcm c^-1 hci f b hb.
by rewrite measure_scale_inverse in h.
Qed.

(** Source for [measure_scale_lower_value_inverse]: the lower-function
    analogue, Federer 2.4.2, p. 81. *)
Lemma measure_scale_lower_value_inverse (f : partial_function X (extended_real_line R)) b :
  measure_lower_step_values cmu f b -> measure_lower_step_values mu f (c^-1%:E * b).
Proof.
move=> hb; have h := @measure_scale_lower_value cmu hcm c^-1 hci f b hb.
by rewrite measure_scale_inverse in h.
Qed.

(** Source for [measure_scale_upper_integral]: the upper integral with
    respect to c phi is c times the upper integral with respect to phi,
    Federer 2.4.2, p. 81. *)
Lemma measure_scale_upper_integral (f : partial_function X (extended_real_line R)) a :
  is_measure_upper_integral mu f a -> is_measure_upper_integral cmu f (c%:E * a).
Proof.
have hcE : (0 <= c%:E) by rewrite lee_fin ltW.
have hciE : (0 <= c^-1%:E) by rewrite lee_fin ltW.
move=> [hlow hgr]; split.
- move=> b hb; have h := hlow _ (measure_scale_upper_value_inverse hb).
  by rewrite -(measure_scale_cancel b); exact: lee_wpmul2l.
- move=> d hd; rewrite -(measure_scale_cancel d); apply: lee_wpmul2l=> //.
  apply: hgr=> b hb; have h := hd _ (measure_scale_upper_value hm hc hb).
  by rewrite -(measure_scale_cancel_left b); exact: lee_wpmul2l.
Qed.

(** Source for [measure_scale_lower_integral]: the lower integral with
    respect to c phi is c times the lower integral with respect to phi,
    Federer 2.4.2, p. 81. *)
Lemma measure_scale_lower_integral (f : partial_function X (extended_real_line R)) a :
  is_measure_lower_integral mu f a -> is_measure_lower_integral cmu f (c%:E * a).
Proof.
have hcE : (0 <= c%:E) by rewrite lee_fin ltW.
have hciE : (0 <= c^-1%:E) by rewrite lee_fin ltW.
move=> [hup hle]; split.
- move=> b hb; have h := hup _ (measure_scale_lower_value_inverse hb).
  by rewrite -(measure_scale_cancel b); exact: lee_wpmul2l.
- move=> d hd; rewrite -(measure_scale_cancel d); apply: lee_wpmul2l=> //.
  apply: hle=> b hb; have h := hd _ (measure_scale_lower_value hm hc hb).
  by rewrite -(measure_scale_cancel_left b); exact: lee_wpmul2l.
Qed.

(** Source for [measure_scale_integral]: int f d(c phi) = c int f dphi
    for c > 0, Federer 2.4.2, p. 81, as used for
    int |v - w|_g dgamma = chi(g) int |v - w| dgamma in 2.7.18,
    p. 141. *)
Theorem measure_scale_integral (f : partial_function X (extended_real_line R)) a :
  is_measure_integral mu f a -> is_measure_integral cmu f (c%:E * a).
Proof.
move=> [hf [hu hl]]; split; first exact: measure_scale_measurable_function.
by split; [exact: measure_scale_upper_integral|exact: measure_scale_lower_integral].
Qed.

(** Source for [measure_scale_represents]: if phi represents the
    functional A on L, then c phi represents c A on L, Federer 2.5.1,
    p. 92, supporting 2.7.18, p. 141. *)
Lemma measure_scale_represents (L : set (X -> R)) (A : (X -> R) -> R) :
  is_real_integral_functional mu L A ->
  is_real_integral_functional cmu L (fun f => (c * A f)%R).
Proof. by move=> hA f hf; rewrite EFinM; apply: measure_scale_integral; exact: hA. Qed.

(** Source for [measure_scale_finite]: c phi(S) < oo if and only if
    phi(S) < oo, for c > 0, supporting 2.5.3, p. 94. *)
Lemma measure_scale_finite (S : set X) : cmu S < +oo <-> mu S < +oo.
Proof.
have h0 := measure_nonnegative hm S.
split=> h.
- rewrite ltNge leye_eq; apply/negP=> /eqP he.
  by move: h; rewrite /measure_scale he gt0_muley ?lte_fin // ltxx.
- by rewrite /measure_scale; apply: lte_mul_pinfty=> //; rewrite lee_fin ltW.
Qed.

(** Source for [measure_scale_finite_hulls]: the F2 sets of phi are F2
    sets of c phi, Federer 2.5.3, p. 94. *)
Lemma measure_scale_finite_hulls (L : set (X -> R)) (W : set X) :
  function_lattice_finite_hulls L mu W -> function_lattice_finite_hulls L cmu W.
Proof.
move=> [V [hV [hdec [hfin he]]]]; exists V; split=> //; split=> //; split=> //.
exact/measure_scale_finite.
Qed.

(** Source for [measure_scale_regular]: c phi is L regular whenever phi
    is, for c > 0, Federer 2.5.3, p. 94, supporting 2.7.18, p. 141. *)
Theorem measure_scale_regular (L : set (X -> R)) :
  is_function_lattice_regular L mu -> is_function_lattice_regular L cmu.
Proof.
move=> hr S; split.
- move=> /measure_scale_finite hS.
  have [W [hSW [hW [he hWf]]]] := (hr S).1 hS.
  exists W; split=> //; split; first exact: measure_scale_finite_hulls.
  by split; [rewrite /measure_scale he|exact/measure_scale_finite].
- by move=> [W [_ [_ [-> hWf]]]].
Qed.

End Integral.
End MeasureScale.
