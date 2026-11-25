(** Federer (1969), 3.2.36, p. 273: equal actual
    tube polynomials have equal original intrinsic-volume coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PositivePolynomialCoefficientUniqueness ScalarComplementPolynomialComparison EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_reverse_weighted_coefficients_unique]: the
    finite coefficient comparison used for the isometry deduction in
    Federer 3.2.36, p. 273. Ordinal reversal and the internal
    positive-radius root count identify every coefficient; each specified
    nonzero weight then cancels. No negative-radius identity is needed. *)
Theorem positive_reverse_weighted_coefficients_unique (R:realType) N
    (c d w:'I_N.+1->R):
  (forall i,w i!=0) ->
  (forall r:R,0<r ->\sum_(i:'I_N.+1) c i*w i*r^+(N-i)=
    \sum_(i:'I_N.+1) d i*w i*r^+(N-i)) ->forall i,c i=d i.
Proof.
move=>hW hEqual.
pose a (u:nat):R^o:=c (rev_ord (inord u))*w (rev_ord (inord u)).
pose b (u:nat):R^o:=d (rev_ord (inord u))*w (rev_ord (inord u)).
have hPowers (r:R):0<r ->\sum_(i<N.+1) r^+i*:a i=\sum_(i<N.+1) r^+i*:b i.
  move=>hr; have h:=hEqual r hr.
  rewrite !finite_reverse_power_sum in h.
  have hLeft: \sum_(i<N.+1) r^+i*:a i=
      \sum_(i:'I_N.+1) (c (rev_ord i)*w (rev_ord i))*r^+i.
    apply:eq_bigr=>i _.
    change (r^+i*(c (rev_ord (inord i))*w (rev_ord (inord i)))=
      (c (rev_ord i)*w (rev_ord i))*r^+i).
    by rewrite inord_val [LHS]mulrC.
  have hRight: \sum_(i<N.+1) r^+i*:b i=
      \sum_(i:'I_N.+1) (d (rev_ord i)*w (rev_ord i))*r^+i.
    apply:eq_bigr=>i _.
    change (r^+i*(d (rev_ord (inord i))*w (rev_ord (inord i)))=
      (d (rev_ord i)*w (rev_ord i))*r^+i).
    by rewrite inord_val [LHS]mulrC.
  rewrite hLeft hRight; exact h.
have hCoefficients:=@positive_finite_power_coefficients_unique R R^o N.+1 a b hPowers.
move=>i; have h:=hCoefficients (rev_ord i) (ltn_ord (rev_ord i)).
rewrite /a /b inord_val rev_ordK in h.
apply:(mulIf (hW i)); exact h.
Qed.

(** Source for [steiner_scalar_coefficients_unique]: actual positive
    unit-ball constants weight the radius powers in the Steiner
    comparison of Federer 3.2.36, p. 273. Their proved strict
    positivity supplies every cancellation, including dimension zero. *)
Corollary steiner_scalar_coefficients_unique (R:realType) N (c d:'I_N.+1->R):
  (forall r:R,0<r ->
    \sum_(i:'I_N.+1) c i*(euclidean_unit_ball_volume R (N-i)*r^+(N-i))=
    \sum_(i:'I_N.+1) d i*(euclidean_unit_ball_volume R (N-i)*r^+(N-i))) ->
  forall i,c i=d i.
Proof.
move=>hEqual; apply:(@positive_reverse_weighted_coefficients_unique R N c d
  (fun i=>euclidean_unit_ball_volume R (N-i)) _ _).
- move=>i; exact:lt0r_neq0 (euclidean_unit_ball_volumeE R (N-i)).2.
- move=>r hr; under eq_bigr do rewrite -mulrA.
  under [RHS]eq_bigr do rewrite -mulrA.
  exact:hEqual r hr.
Qed.
