(** Federer 3.2.13, p. 251: the actual normalized projection
    moment in three dimensions. This exact consequence supplies
    a test of the logarithmic estimate in 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  constructive_ereal topology lra ring.
From Federer Require Import ProjectionBeta ProjectionBetaOneGamma EulerGamma
  EulerGammaRecurrence EulerGammaHalfParameters GammaHalfSequences RealPower
  RealPowerNaturalHausdorff SphereCoordinateParameters SphereCoordinateMoment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Close Scope ereal_scope.

(** Source for [projection_three_one_moment]: supporting actual
    constant calculation from Federer 3.2.13, p. 251, used
    to check 3.2.45, p. 279. For n= 3 and m= 1 the
    t-th power of beta_t is 1/(t+1), for every finite t>= 1.
    This is proved from the original Gamma formula and recurrence. *)
Lemma projection_three_one_moment (R:realType) (hmn:(1<= 3)%N) (t:R) (ht:1<=t):
  real_power (@projection_beta R 3 1 hmn t%:E) t=(t+1)^-1.
Proof.
have hDim:(0<3)%N by [].
have hFormula:=@projection_beta_one_gamma_formula R 3 hDim t ht.
have hBase:0<(1/2:R):=positive_real_half R.
have hBaseSuc:0<(1/2:R)+1 by lra.
have hGammaDim:euler_gamma (@positive_dimension_half R 3 hDim)=
    (1/2)*euler_gamma_half R.
  have hRec:=euler_gamma_recurrence hBase hBaseSuc.
  have hEq:euler_gamma hBaseSuc=euler_gamma (@positive_dimension_half R 3 hDim).
    apply:euler_gamma_equal_parameters;field;lra.
  have hHalf:euler_gamma hBase=euler_gamma_half R.
    exact:euler_gamma_proof_irrelevant.
  by rewrite hEq hHalf in hRec.
pose hs:=positive_coordinate_moment_parameter (projection_moment_range ht).
have hsSuc:0<(t+1)/2+1 by have h:=hs;lra.
have hDenom:euler_gamma (@positive_coordinate_moment_denominator R 3 t hDim
    (projection_moment_range ht))=((t+1)/2)*euler_gamma hs.
  have hRec:=euler_gamma_recurrence hs hsSuc.
  have hEq:euler_gamma hsSuc=euler_gamma (@positive_coordinate_moment_denominator R 3 t hDim
      (projection_moment_range ht)).
    apply:euler_gamma_equal_parameters;field;lra.
  by rewrite hEq in hRec.
have hBeta:(@projection_beta R 3 1 hmn t%:E)=(@projection_beta R 3 1 hDim t%:E).
  by have ->:hmn=hDim:=Prop_irrelevance _ _.
rewrite hBeta hFormula hGammaDim hDenom.
have hGs:euler_gamma hs!=0:=lt0r_neq0 (euler_gamma_positive hs).
have hGh:euler_gamma_half R!=0:=lt0r_neq0 (euler_gamma_positive (positive_real_half R)).
have hTp:t+1!=0 by apply:lt0r_neq0;lra.
field;rewrite ?hGs ?hGh ?hTp //;lra.
Qed.

(** Source for [projection_three_one_first]: concrete original
    beta_1(3,1)= 1/2 from Federer 3.2.13, p. 251,
    for the source-estimate regression in 3.2.45, p. 279. *)
Corollary projection_three_one_first (R:realType) (hmn:(1<= 3)%N):
  @projection_beta R 3 1 hmn (1:R)%:E= 1/2.
Proof.
have h:=@projection_three_one_moment R hmn 1 (lexx 1).
have hPos:=@projection_beta_positive R 3 1 hmn (1:R)%:E.
have htE:(1<=(1:R)%:E)%E by rewrite lee_fin.
rewrite real_power_one_exponent ?(ltW (hPos htE)) // in h.
rewrite h;field;lra.
Qed.

(** Source for [projection_three_one_second]: concrete original
    beta_2(3,1)^2= 1/3 from Federer 3.2.13, p. 251,
    for the source-estimate regression in 3.2.45, p. 279. *)
Corollary projection_three_one_second (R:realType) (hmn:(1<= 3)%N):
  (@projection_beta R 3 1 hmn (2:R)%:E)^+2= 1/3.
Proof.
have ht:(1:R)<= 2 by lra.
have h:=@projection_three_one_moment R hmn 2 ht.
have htE:(1<=(2:R)%:E)%E by rewrite lee_fin.
rewrite real_power_natural_exponent ?(ltW (@projection_beta_positive R 3 1 hmn (2:R)%:E htE)) // in h.
rewrite h;field;lra.
Qed.
