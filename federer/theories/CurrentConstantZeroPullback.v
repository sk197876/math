(** Federer (1969), 4.1.10, p. 364: constant-map pullback
    in degree zero evaluates the original scalar form at u. This
    supports the precise coefficient T(1) in the current formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingZero AlternatingDual
  CurrentSpaces CurrentConstantFields CurrentPushforwardDirac
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentConstantZeroPullback.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables U V : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hV : forall x, V x -> norm_domain_interior NX V x.
Variable u : X.
Hypothesis hImage : forall x, U x -> V u.
Hypothesis hConst : norm_class_all_orders hNX hNX U (fun _:X => u).
Local Notation P := (@SmoothFormPullback.operator R h2 n n 0%N U V hU hV
  (fun _:X => u) hImage hConst).
Local Notation one := (@current_constant_form R h2 n U hU 0%N (@zero_form R X R^o 1)).

(** Source for [current_constant_zero_pullback]: f#psi=psi(u)1
    for the constant map f=u, supporting f#T=T(1)delta_u in
    Federer 4.1.10, p. 364. The scalar one is an actual smooth
    zero-form; it is not required to have compact support. *)
Theorem current_constant_zero_pullback (psi : @current_smooth_space R h2 n V hV 0%N) :
  P psi=zero_form_value (@current_smooth_value R h2 n V hV 0%N psi u)*:one.
Proof.
apply: (smooth_function_extensional (@current_smooth_space_laws R h2 n U hU 0%N)) => x hx.
have hD := @norm_differential_constant R X X NX NX hNX hNX U x u (@hU x hx).
rewrite (@smooth_form_pullback_values R n n 0%N U V
  (@current_smooth_space R h2 n V hV 0%N) (@current_smooth_space R h2 n U hU 0%N)
  (@current_smooth_value R h2 n V hV 0%N) (@current_smooth_value R h2 n U hU 0%N)
  (fun _:X => u) P (@SmoothFormPullback.laws R h2 n n 0%N U V hU hV
    (fun _:X => u) hImage hConst) psi x (0:Hom X X) hx hD).
change (A_m_dual (hom_as_linear (0:Hom X X))
  (@current_smooth_value R h2 n V hV 0%N psi u)=
  smooth_function_values_hom (@current_smooth_space_laws R h2 n U hU 0%N)
    (zero_form_value (@current_smooth_value R h2 n V hV 0%N psi u)*:one) x).
rewrite linearZ.
change (A_m_dual (hom_as_linear (0:Hom X X))
  (@current_smooth_value R h2 n V hV 0%N psi u)=
  zero_form_value (@current_smooth_value R h2 n V hV 0%N psi u)*:
    @current_smooth_value R h2 n U hU 0%N one x).
rewrite (@current_constant_form_values R h2 n U hU 0%N
  (@zero_form R X R^o 1) x hx).
apply: form_ext => t.
rewrite A_m_dualE form_scaleE !zero_formE /zero_form_value !tuple0.
change (@current_smooth_value R h2 n V hV 0%N psi u [tuple]=
  @current_smooth_value R h2 n V hV 0%N psi u [tuple]*1).
by rewrite mulr1.
Qed.
End CurrentConstantZeroPullback.
