(** Federer (1969), 4.1.7, p. 356:
    the actual linear map xi to Lebesgue
    wedge xi on original smooth multivector
    fields. Its existence is the earlier
    locally integrable density-current theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces CurrentDensityUP CurrentDensityAction
  CurrentLebesgueDensity CurrentDensityArithmetic CurrentDensityUniqueness SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothLebesgue.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation V := (@current_vector_smooth_space R h2 n (fun _=>True) hFull m).
Local Notation vv := (@current_vector_smooth_value R h2 n (fun _=>True) hFull m).
Local Notation hV := (@current_vector_smooth_space_laws R h2 n (fun _=>True) hFull m).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation C := (@full_current_space R h2 n m).

(** Source for [current_smooth_lebesgue_value]:
    every original smooth multivector field has
    its actual Lebesgue-density current, Federer
    4.1.7, p. 356. Smoothness discharges
    local integrability; no extra premise remains. *)
Definition current_smooth_lebesgue_value (xi:V):C:=
  @current_lebesgue_density R h2 n m (vv xi)
    (@continuous_current_density_integrable R h2 n m (vv xi)
      (norm_class_continuous (smooth_function_evaluation_smooth hV xi 0%N))).

(** Source for [current_smooth_lebesgue_action]:
    the map has exactly Federer's original
    test integral, 4.1.7, p. 356. *)
Lemma current_smooth_lebesgue_action (xi:V):
  is_current_density_action mu (vv xi) (current_smooth_lebesgue_value xi).
Proof. exact:current_lebesgue_density_action. Qed.

(** Source for [current_smooth_lebesgue_linear]:
    xi to Lebesgue wedge xi is linear,
    as in the original diagram in Federer
    4.1.7, p. 356. The proof uses
    the already proved original integral arithmetic. *)
Lemma current_smooth_lebesgue_linear:linear current_smooth_lebesgue_value.
Proof.
move=>c xi eta.
have hScaled:=@current_density_scaled_action R h2 n m mu hm (vv xi)
  (current_smooth_lebesgue_value xi) c (current_smooth_lebesgue_action xi).
have hSum:=@current_density_sum_action R h2 n m mu hm
  (fun x=>c*:vv xi x) (vv eta)
  (c*:current_smooth_lebesgue_value xi) (current_smooth_lebesgue_value eta)
  hScaled (current_smooth_lebesgue_action eta).
have hField:vv (c*:xi+eta)=(fun x=>c*:vv xi x+vv eta x).
  apply:funext=>x.
  exact:(@smooth_function_evaluation_linear R X _ NX _ _ _
    (fun _=>True) V vv hV c xi eta x).
apply:(@current_density_action_unique R h2 n m mu (vv (c*:xi+eta))).
- exact:current_smooth_lebesgue_action.
- by rewrite hField.
Qed.

(** Source for [current_smooth_lebesgue_map]:
    the original linear arrow from E(R^n,
    exterior^m R^n) to currents, Federer
    4.1.7, p. 356. *)
Definition current_smooth_lebesgue_map:Hom V C:=
  @HomMap R V C current_smooth_lebesgue_value
    (introT (asboolP _) current_smooth_lebesgue_linear).
End CurrentSmoothLebesgue.
