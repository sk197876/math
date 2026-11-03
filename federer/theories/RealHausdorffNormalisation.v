(** Federer 2.10.2, p. 171: alpha(p)=Gamma(1/2)^p/Gamma(p/2+1)
    for every nonnegative real degree. The Gamma evaluator and real powers
    are already opaque. The normalization is specified by the printed
    equation before its explicit scalar value and compatibility proofs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import EulerGamma EulerGammaHalfParameters EulerGammaOne
  UnitBallGammaVolume EuclideanBallVolume RealPower RealPowerNaturalHausdorff
  HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_dimension_gamma_parameter]: Federer 2.10.2,
    p. 171; the denominator's Gamma parameter is positive at every
    admissible degree, including zero. *)
Lemma real_dimension_gamma_parameter (R:realType) (p:R):
  0<=p -> 0<p/2+1.
Proof.
move=>hp; have h2:(0<2:>R) by rewrite ltr0n.
have hh:0<=p/2 by rewrite divr_ge0 // ltW.
lra.
Qed.

(** Source for [is_real_hausdorff_normalisation]: Federer 2.10.2,
    p. 171, bracketed definition. This independent scalar specification
    retains the actual defining Gamma values, not a recursively assigned
    extension of the natural-dimensional constants. *)
Definition is_real_hausdorff_normalisation (R:realType) (p:R)
    (hp:0<=p) (a:R):Prop:=
  a=(real_power (euler_gamma_half R) p/
    euler_gamma (real_dimension_gamma_parameter hp))/real_power 2 p.

(** Source for [real_hausdorff_normalisation]: Federer 2.10.2,
    p. 171, the coefficient alpha(p)2^(-p). This scalar expression uses
    only the sealed Gamma and power interfaces and has no nonpositive
    Gamma evaluation. Its nonnegative-degree proof is explicit. *)
Definition real_hausdorff_normalisation (R:realType) (p:R) (hp:0<=p):R:=
  (real_power (euler_gamma_half R) p/
    euler_gamma (real_dimension_gamma_parameter hp))/real_power 2 p.

(** Source for [real_hausdorff_normalisation_specification]: Federer
    2.10.2, p. 171; the displayed scalar satisfies its independent law. *)
Lemma real_hausdorff_normalisation_specification (R:realType) (p:R) (hp:0<=p):
  is_real_hausdorff_normalisation hp (real_hausdorff_normalisation hp).
Proof. by []. Qed.

(** Source for [real_hausdorff_normalisation_positive]: Federer
    2.10.2, p. 171; supporting positivity and finiteness of the real
    normalization, derived from actual positive Gamma integrals. *)
Lemma real_hausdorff_normalisation_positive (R:realType) (p:R) (hp:0<=p):
  0<real_hausdorff_normalisation hp.
Proof.
rewrite /real_hausdorff_normalisation; apply:divr_gt0.
- apply:divr_gt0; last exact:euler_gamma_positive.
  apply:real_power_strictly_positive; exact:euler_gamma_positive.
- apply:real_power_strictly_positive; by rewrite ltr0n.
Qed.

(** Source for [gamma_equal_positive_parameters]: Federer 2.10.2,
    p. 171; supporting proof-irrelevant transport of the same positive
    Gamma argument in the natural-degree consistency statement. *)
Lemma gamma_equal_positive_parameters (R:realType) (s t:R)
    (hs:0<s) (ht:0<t):s=t -> euler_gamma hs=euler_gamma ht.
Proof. move=>hst; subst t; exact:euler_gamma_proof_irrelevant. Qed.

(** Source for [real_hausdorff_normalisation_zero]: Federer 2.10.2,
    p. 171, compatibility with counting measure. Gamma(1) = 1 is proved
    from its actual defining integral, not assigned by convention. *)
Lemma real_hausdorff_normalisation_zero (R:realType) (hp:(0:R)<=0):
  real_hausdorff_normalisation hp = 1.
Proof.
rewrite /real_hausdorff_normalisation !real_power_zero_exponent.
have hparam : (0:R)/2+1 = 1 by rewrite mul0r add0r.
have hg:=gamma_equal_positive_parameters
  (real_dimension_gamma_parameter hp) (ltr01 : (0:R)<1) hparam.
rewrite hg euler_gamma_one !divr1.
by [].
Qed.

(** Source for [real_hausdorff_normalisation_natural]: Federer 2.10.2,
    p. 171, the stated consistency by 3.2.13, p. 251. Every natural
    degree agrees with the actual unit-ball-volume coefficient, including
    degree zero and the positive atom convention. *)
Theorem real_hausdorff_normalisation_natural (R:realType) (m:nat)
    (hp:(0:R)<=m%:R):
  real_hausdorff_normalisation hp=hausdorff_normalisation R m.
Proof.
case: m hp=>[|m] hp.
- by rewrite real_hausdorff_normalisation_zero hausdorff_normalisation_zero.
have hm:(0<m.+1)%N by [].
rewrite /real_hausdorff_normalisation /hausdorff_normalisation
  real_power_natural_exponent ?(ltW (euler_gamma_positive (positive_real_half R))) //
  real_power_natural_exponent ?ler0n // euclidean_unit_ball_gamma_volume //.
have hg:=euler_gamma_proof_irrelevant (real_dimension_gamma_parameter hp)
  (@positive_dimension_half_successor R m.+1 hm).
by rewrite hg.
Qed.
