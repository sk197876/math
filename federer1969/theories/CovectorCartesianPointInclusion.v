(** Federer (1969), 4.1.8, p. 362: separated
    forms pulled back by epsilon_z have the original
    diagonal scalar value and vanish in every other
    first degree. Reuse the original all-degree block
    pairing and degree-zero exterior unit. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear BoundedHom HomogeneousHom GradedComponents
  GrassmannAbbreviations EuclideanBlockLinearMaps ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts
  AlternatingForms AlternatingZero AlternatingDual AlternatingProduct AlternatingPairing AlternatingExtension AlternatingSum
  ScalarCoefficients ComassWedgeSymmetry CurrentDiracDensity CurrentZeroDegreeExteriorLaws CurrentCartesianVectorProduct
  CurrentCartesianVectorPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CovectorCartesianPointInclusion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation p := (hom_as_linear (@euclidean_first_block_map R m n)).
Local Notation q := (hom_as_linear (@euclidean_last_block_map R m n)).
Local Notation Q := (hom_as_linear (@euclidean_last_injection_map R m n)).
Local Notation unit := (@current_scalar_multivector_unit R m).
Local Notation Pure := (fun k l (a:A_m X R^o k) (b:A_m Y R^o l)=>
  form_wedge h2 (scalar_bilinear R) (A_m_dual p a) (A_m_dual q b)).

(** Source for [current_point_covector_pairing_all_degrees]:
    the original inclusion pullback has exactly the
    all-degree separated pairings, supporting Federer
    4.1.8, p. 362, by the preceding product
    coefficient computation on p. 361. *)
Theorem current_point_covector_pairing_all_degrees j k l (e:(k+l)%N=j)
    (a:A_m X R^o k) (b:A_m Y R^o l) (eta:exterior_power Y j):
  pairing eta (A_m_dual Q (form_reindex e (Pure k l a b)))=
    form_include a (component_val unit)*form_include b (component_val eta).
Proof.
have hF:@current_cartesian_vector_product R m n 0%N j unit eta=exterior_power_map Q j eta.
  by rewrite /current_cartesian_vector_product /current_scalar_multivector_unit
    exterior_power_map_zeroth_scalar exterior_product_zeroth_scalar_left scale1r.
rewrite A_m_dual_pairing -hF.
change (form_include (form_reindex e (Pure k l a b))
  (component_val (@current_cartesian_vector_product R m n 0%N j unit eta))=
  form_include a (component_val unit)*form_include b (component_val eta)).
rewrite form_reindex_include.
exact:(@current_cartesian_vector_pairing_all_degrees R h2 m n 0%N j k l unit eta a b).
Qed.

(** Source for [current_point_covector_diagonal]: the
    original point-inclusion pullback of p#alpha wedge
    q#beta is alpha(z) beta when alpha has degree
    zero, supporting Federer 4.1.8, p. 362. *)
Theorem current_point_covector_diagonal j (a:A_m X R^o 0%N) (b:A_m Y R^o j):
  A_m_dual Q (form_reindex (add0n j) (Pure 0%N j a b))=zero_form_value a*:b.
Proof.
apply:pairing_ext=>eta.
rewrite current_point_covector_pairing_all_degrees (bilZr (@pairing_bilinear R Y R^o j)).
change (pairing unit a*pairing eta b=zero_form_value a*pairing eta b).
by rewrite current_scalar_multivector_unit_pairing.
Qed.

(** Source for [current_point_covector_off_diagonal]: every
    original separated form of positive first degree
    pulls back to zero under epsilon_z, supporting
    Federer 4.1.8, p. 362. *)
Theorem current_point_covector_off_diagonal j k l (e:(k+l)%N=j)
    (a:A_m X R^o k) (b:A_m Y R^o l):k<>0%N->
  A_m_dual Q (form_reindex e (Pure k l a b))=0.
Proof.
move=>hk;apply:pairing_ext=>eta.
rewrite current_point_covector_pairing_all_degrees (bil0r (@pairing_bilinear R Y R^o j)).
have hDegree:(0%N!=k)%N by apply/eqP=>h;apply:hk;exact:esym h.
have hZero:form_include a (component_val unit)=0.
  change (form_extension a (component_val unit)=0).
  exact:(@form_extension_degree R X R^o k a 0%N (component_val unit)
    hDegree (component_homogeneous unit)).
by rewrite hZero mul0r.
Qed.
End CovectorCartesianPointInclusion.
