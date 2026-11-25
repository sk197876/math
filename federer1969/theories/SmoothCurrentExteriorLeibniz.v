(** Federer (1969), 4.1.7, p. 356: the
    original exterior Leibniz identity on actual
    smooth forms, needed for current boundary and
    contraction. Reuse 4.1.6, p. 353, in
    its original induced norms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms Alternating AlternatingSum
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentFormInducedNorm CurrentSpaces
  SmoothCurrentFormProduct SmoothCurrentExteriorDerivative ExteriorDerivativeUP ExteriorDerivativeLeibniz
  ExteriorDerivativeFiniteSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothCurrentExteriorLeibniz.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (fun m=>@current_form_comass R h2 n m).
Local Notation hNY := (fun m=>@current_form_comass_real_norm R h2 n m).
Local Notation hNorm := (fun m=>@current_form_comass_is_induced R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation ev := (fun m=>@current_smooth_value R h2 n U hU m).
Local Notation d := (fun m=>@smooth_current_exterior_derivative R h2 n m U hU).
Local Notation aw := (alternating_wedge h2 (@scalar_bilinear R)).

(** Source for [smooth_current_exterior_leibniz_values]:
    the exact graded original product identity on
    U, supporting the second displayed current
    equation of Federer 4.1.7, p. 356. Inclusion
    in the full alternating algebra compares its
    naturally equal output degrees. *)
Theorem smooth_current_exterior_leibniz_values (phi:E k) (psi:E p) x:U x->
  form_include (ev (k+p).+1 (d (k+p) (@smooth_current_form_product R h2 n k p U hU phi psi)) x)=
    aw (form_include (ev k.+1 (d k phi) x)) (form_include (ev p psi x))+
      (-1:R)^+k*:aw (form_include (ev k phi x)) (form_include (ev p.+1 (d p psi) x)).
Proof.
move=>hx.
have [z [hZ hEqual]]:=@exterior_derivative_leibniz R h2 n k p (NY k) (NY p) (NY (k+p))
  (hNY k) (hNY p) (hNY (k+p)) (hNorm k) (hNorm p) (hNorm (k+p))
  U (ev k phi) (ev p psi) x (ev k.+1 (d k phi) x) (ev p.+1 (d p psi) x)
  (@smooth_current_exterior_derivative_actual R h2 n k U hU phi x hx)
  (@smooth_current_exterior_derivative_actual R h2 n p U hU psi x hx).
have hZActual:has_exterior_derivative NX (NY (k+p)) U
    (ev (k+p) (@smooth_current_form_product R h2 n k p U hU phi psi)) x z.
  exact:(@exterior_derivative_domain_agreement R X R^o NX hNX (k+p) (NY (k+p)) U
    (fun y=>form_wedge h2 (@scalar_bilinear R) (ev k phi y) (ev p psi y))
    (ev (k+p) (@smooth_current_form_product R h2 n k p U hU phi psi)) x z
    (fun y hy=>esym (@smooth_current_form_product_values R h2 n k p U hU phi psi y hy)) hZ).
have hUnique:=@exterior_derivative_unique R X R^o NX hNX (k+p) (NY (k+p)) (hNY (k+p)) U
  (ev (k+p) (@smooth_current_form_product R h2 n k p U hU phi psi)) x
  (ev (k+p).+1 (d (k+p) (@smooth_current_form_product R h2 n k p U hU phi psi)) x) z
  (@smooth_current_exterior_derivative_actual R h2 n (k+p) U hU
    (@smooth_current_form_product R h2 n k p U hU phi psi) x hx) hZActual.
by rewrite hUnique.
Qed.
End SmoothCurrentExteriorLeibniz.
