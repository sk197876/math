(** Federer (1969), 4.1.7, p. 356: actual
    smooth divergence in the original current
    identities. The opaque first-order operator
    applies the original divergence map of
    4.1.6 to the actual first differential. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherDifferentialFirst
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  ContinuousMultilinearSealed ContinuousMultilinearOne OpenFamilyTopologyUP
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  CurrentCoefficientNorms CurrentVectorSpaces CurrentDivergenceMap DivergenceDerivative
  SmoothFirstOrderUP SmoothFirstOrderSealed SmoothFirstOrderContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothCurrentDivergence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (exterior_power X p.+1).
Local Notation Z := (exterior_power X p).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_vector_mass R h2 n p.+1).
Local Notation hNY := (@current_vector_mass_real_norm R h2 n p.+1).
Local Notation NZ := (@current_vector_mass R h2 n p).
Local Notation hNZ := (@current_vector_mass_real_norm R h2 n p).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_vector_smooth_space R h2 n U hU p.+1).
Local Notation F := (@current_vector_smooth_space R h2 n U hU p).
Local Notation ev := (@current_vector_smooth_value R h2 n U hU p.+1).
Local Notation fv := (@current_vector_smooth_value R h2 n U hU p).
Local Notation hE := (@current_vector_smooth_space_laws R h2 n U hU p.+1).
Local Notation hF := (@current_vector_smooth_space_laws R h2 n U hU p).
Local Notation D := (@current_vector_smooth_derivatives R h2 n U hU p.+1).
Local Notation G := (@current_vector_smooth_derivatives R h2 n U hU p).
Local Notation hD := (@current_vector_smooth_derivative_laws R h2 n U hU p.+1).
Local Notation hG := (@current_vector_smooth_derivative_laws R h2 n U hU p).
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation eJ := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation L := (@current_divergence_map R h2 n p).
Local Notation hL := (@current_divergence_map_bounded R h2 n p).

(** Source for [smooth_current_divergence]: the
    original actual smooth div xi in
    Federer 4.1.7, p. 356. *)
Definition smooth_current_divergence:Hom E F:=
  @SmoothFirstOrder.operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF D hD L hL.
Local Notation P := smooth_current_divergence.
Local Notation hP := (@SmoothFirstOrder.laws R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF D hD L hL).

(** Source for [smooth_current_divergence_values]: the
    original divergence applies to the actual
    first differential, supporting Federer 4.1.7,
    p. 356. *)
Lemma smooth_current_divergence_values xi x:
  U x->fv (P xi) x=L (@D 1%N x xi).
Proof. exact:SmoothFirstOrder.laws. Qed.

(** Source for [smooth_current_divergence_actual]: the
    output has the original field-divergence graph,
    supporting Federer 4.1.7, p. 356,
    through the exact definition of 4.1.6. *)
Theorem smooth_current_divergence_actual xi x:
  U x->has_field_divergence h2 NX NY U (ev xi) x (fv (P xi) x).
Proof.
move=>hx.
exists (@continuous_multilinear_one_operator R X Y (J 1%N) NX NY
  (@eJ 1%N) (@JN 1%N) (@hJ 1%N) (@D 1%N x xi));split.
- exact:(@norm_higher_differential_first R X Y NX NY hNX hNY J eJ JN hJ U (ev xi)
    x (@D 1%N x xi)).1 (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD 1%N xi x hx).
- rewrite (smooth_current_divergence_values xi hx);exact:current_divergence_map_values.
Qed.

(** Source for [smooth_current_divergence_continuous]:
    divergence is continuous between the original
    smooth multivector spaces, supporting the
    current operations of Federer 4.1.7,
    p. 356. *)
Theorem smooth_current_divergence_continuous:
  open_family_continuous (smooth_function_opens hD) (smooth_function_opens hG) P.
Proof.
exact:(@smooth_first_order_operator_continuous R X Y Z NX NY NZ hNX hNY hNZ
  U E F ev fv hF D G hD hG L hL P hP).
Qed.
End SmoothCurrentDivergence.
