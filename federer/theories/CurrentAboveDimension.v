(** Federer (1969), 4.1.10, p. 364: D_(n+1)(U)=0.
    More generally every degree above n vanishes on any open U.
    The proof reuses the exterior-power dimension theorem of 1.3.2;
    it imposes no support or representation condition on a current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct ExteriorGrading ExteriorPowers FiniteExteriorPowers
  AlternatingForms AlternatingPairing CurrentSpaces CurrentEvaluation
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentAboveDimension.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n j : nat.
Hypothesis hj : (n<j)%N.
Local Notation X := (R_n R n).

(** Source for [current_coefficient_above_dimension]: every
    covector above dimension n is zero, by Federer 1.3.2, p. 15,
    and the pairing of 1.4.1, p. 17, supporting 4.1.10, p. 364. *)
Lemma current_coefficient_above_dimension (a : A_m X R^o j) : a=0.
Proof.
apply: pairing_ext => eta.
have -> : eta=0 := @exterior_power_above_dimension R n X
  (@coordinate_basis R n) (@coordinate_basisP R n) h2 j hj eta.
by rewrite /pairing !linear0.
Qed.

Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hE := (@current_smooth_space_laws R h2 n U hU j).

(** Source for [current_smooth_above_dimension]: E^j(U)=0 for
    j>n, supporting the stated zero current space in Federer
    4.1.10, p. 364. Extensionality uses the actual smooth space. *)
Lemma current_smooth_above_dimension
    (phi : @current_smooth_space R h2 n U hU j) : phi=0.
Proof.
apply: (smooth_function_extensional hE) => x hx.
change (smooth_function_values_hom hE phi x=
  smooth_function_values_hom hE 0 x).
rewrite linear0; exact: current_coefficient_above_dimension.
Qed.

(** Source for [current_test_above_dimension]: D^j(U)=0 for
    j>n, supporting Federer 4.1.10, p. 364. This is the original
    compact test space, with its literal final topology. *)
Lemma current_test_above_dimension
    (phi : @current_test_space R h2 n U hU j) : phi=0.
Proof.
apply: (smooth_test_values_extensional hE) => x hx.
change (smooth_test_values_hom hE phi x=smooth_test_values_hom hE 0 x).
rewrite linear0; exact: current_coefficient_above_dimension.
Qed.

(** Source for [current_above_dimension]: D_j(U)=0 for j>n;
    in particular D_(n+1)(R^n)=0, Federer 4.1.10, p. 364.
    The final paragraph permits every open U, including empty U. *)
Theorem current_above_dimension (T : @current_space R h2 n U hU j) : T=0.
Proof.
apply: current_values_extensional => phi.
by rewrite (current_test_above_dimension phi) !linear0.
Qed.
End CurrentAboveDimension.
