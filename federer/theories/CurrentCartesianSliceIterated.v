(** Federer (1969), 4.1.8, p. 360: every ordered
    vertical test derivative commutes with the original slice.
    This supporting induction uses the actual iterated test
    operators already proved for 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms CurrentCoefficientNorms CurrentSpaces DistributionDirectionalDerivative
  DistributionIteratedDerivative CurrentCartesianDomain CurrentCartesianSliceSealed
  CurrentCartesianSliceDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceIterated.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation H := (fun S=>@CartesianSlice.value R h2 m n i j A B hA hB S).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation IterC := (@distribution_test_iterated_derivative R Z (A_m Z R^o (i+j))
  NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ (@current_form_comass_real_norm R h2 (m+n) (i+j))
  AB hAB EC vc hEC (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j))).
Local Notation IterB := (@distribution_test_iterated_derivative R Y (A_m Y R^o j)
  NY (@current_form_comass R h2 n j) hNY (@current_form_comass_real_norm R h2 n j)
  B hB EB vb hEB (@current_smooth_derivatives R h2 n B hB j)
  (@current_smooth_derivative_laws R h2 n B hB j)).

(** Source for [current_cartesian_slice_iterated_commutation]: all
    original repeated vertical derivatives of phi_S are slices
    of the corresponding original input derivatives, supporting
    Federer 4.1.8, p. 360. The empty direction list
    and every nonnegative derivative order are retained. *)
Theorem current_cartesian_slice_iterated_commutation
    (S:@current_space R h2 m A hA i) (phi:DC) (s:seq Y):
  IterB s (H S phi)=H S (IterC [seq Q v | v<-s] phi).
Proof.
elim:s=>[|v s IH];first reflexivity.
change ((@distribution_test_directional_derivative R Y (A_m Y R^o j)
  NY (@current_form_comass R h2 n j) hNY (@current_form_comass_real_norm R h2 n j)
  B hB EB vb hEB (@current_smooth_derivatives R h2 n B hB j)
  (@current_smooth_derivative_laws R h2 n B hB j) v) (IterB s (H S phi))=
  H S ((@distribution_test_directional_derivative R Z (A_m Z R^o (i+j))
    NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ (@current_form_comass_real_norm R h2 (m+n) (i+j))
    AB hAB EC vc hEC (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
    (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) (Q v))
    (IterC [seq Q u | u<-s] phi))).
rewrite IH;exact:(@current_cartesian_slice_directional_commutation R h2 m n i j A B hA hB
  S (IterC [seq Q u | u<-s] phi) v).
Qed.
End CurrentCartesianSliceIterated.
