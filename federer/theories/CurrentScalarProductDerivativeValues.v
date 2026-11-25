(** Federer (1969), 4.1.12, p. 367: apply
    the preceding graded Leibniz identity to a
    scalar smooth multiplier and an actual compact
    test. Both terms have the literal original degree. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear TensorUP RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct Alternating AlternatingSum
  AlternatingForms AlternatingProduct ScalarCoefficients CurrentSpaces SmoothTestSpaces
  CurrentTestFormProduct CurrentTestExteriorDerivative SmoothCurrentExteriorDerivative
  SmoothCurrentExteriorLeibniz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentScalarProductDerivativeValues.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation E d := (@current_smooth_space R h2 n U hU d).
Local Notation sv d := (@current_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_smooth_space_laws R h2 n U hU d).
Local Notation DT d := (@current_test_space R h2 n U hU d).
Local Notation value d := (@current_test_value R h2 n U hU d).
Local Notation inc d := (smooth_test_inclusion (hE d)).
Local Notation sd d := (@smooth_current_exterior_derivative R h2 n d U hU).
Local Notation d d := (@current_test_exterior_derivative R h2 n d U hU).

(** Source for [current_scalar_product_derivative_values]:
    d(gamma wedge phi)=d gamma wedge phi+gamma
    wedge d phi at every point of U, by
    the earlier identity of 4.1.6, p. 353,
    supporting Federer 4.1.12, p. 367. *)
Theorem current_scalar_product_derivative_values (gamma:E 0%N) (phi:DT m) x:
  U x->
  value m.+1 (d m (@current_test_form_product R h2 n 0%N m U hU gamma phi)) x=
    form_wedge h2 (scalar_bilinear R) (sv 1%N (sd 0%N gamma) x) (value m phi x)+
    form_wedge h2 (scalar_bilinear R) (sv 0%N gamma x) (value m.+1 (d m phi) x).
Proof.
move=>hx;apply:(can_inj (@form_includeK R X R^o m.+1)).
rewrite (linD (@form_include_linear R X R^o m.+1))
  (@form_wedge_include R h2 X R^o _ (scalar_bilinear R) 1 m)
  (@form_wedge_include R h2 X R^o _ (scalar_bilinear R) 0 m.+1).
change (form_include (sv m.+1 (inc m.+1
    (d m (@current_test_form_product R h2 n 0%N m U hU gamma phi))) x)=
  alternating_wedge h2 (scalar_bilinear R)
    (form_include (sv 1%N (sd 0%N gamma) x)) (form_include (sv m (inc m phi) x))+
  alternating_wedge h2 (scalar_bilinear R)
    (form_include (sv 0%N gamma x)) (form_include (sv m.+1 (inc m.+1 (d m phi)) x))).
rewrite (@current_test_exterior_derivative_inclusion R h2 n m U hU
    (@current_test_form_product R h2 n 0%N m U hU gamma phi))
  (@current_test_exterior_derivative_inclusion R h2 n m U hU phi)
  (@current_test_form_product_inclusion R h2 n 0%N m U hU gamma phi).
have h:=@smooth_current_exterior_leibniz_values R h2 n 0%N m U hU gamma (inc m phi) x hx.
by rewrite expr0 scale1r in h.
Qed.
End CurrentScalarProductDerivativeValues.
