(** Federer (1969), 4.1.8, p. 360: the separated smooth
    forms are actual compact tests on A times B. Their supports
    lie in the product of two original compact support bounds.
    The witness compact set is used only in this existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap AlternatingForms AlternatingDual
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  CurrentCartesianDomain CurrentCartesianCompact CurrentCartesianCutoff CurrentCartesianTestProductSealed
  CurrentSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianTestProductSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation EA := (fun k=>@current_smooth_space R h2 m A hA k).
Local Notation EB := (fun k=>@current_smooth_space R h2 n B hB k).
Local Notation EC := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation va := (fun k=>@current_smooth_value R h2 m A hA k).
Local Notation vb := (fun k=>@current_smooth_value R h2 n B hB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation ta := (fun k=>@current_test_value R h2 m A hA k).
Local Notation tb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation hEA := (fun k=>@current_smooth_space_laws R h2 m A hA k).
Local Notation hEB := (fun k=>@current_smooth_space_laws R h2 n B hB k).
Local Notation hEC := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation NC := (fun k=>@current_form_comass R h2 (m+n) k).
Local Notation hNC := (fun k=>@current_form_comass_real_norm R h2 (m+n) k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [current_cartesian_test_product_support]: the
    support of an original separated test lies in the
    Cartesian product of its two exact test supports,
    supporting the current support identity of Federer 4.1.8,
    p. 360. The actual factor supports are compact;
    no larger auxiliary support bound is substituted. *)
Theorem current_cartesian_test_product_support k l (alpha:DA k) (beta:DB l):
  @current_test_support R h2 (m+n) (k+l) AB hAB (Pure k l alpha beta) `<=`
    @euclidean_cartesian_set R m n
      (@current_test_support R h2 m k A hA alpha) (@current_test_support R h2 n l B hB beta).
Proof.
pose KA:=@Build_smooth_compact_set R X NX hNX A
  (@current_test_support R h2 m k A hA alpha)
  (fun x hx=>hx.1) (smooth_test_support_compact (hEA k) alpha).
pose KB:=@Build_smooth_compact_set R Y NY hNY B
  (@current_test_support R h2 n l B hB beta)
  (fun x hx=>hx.1) (smooth_test_support_compact (hEB l) beta).
have[K hK]:=@current_cartesian_compact_rectangle R m n A B KA KB.
have hOffA:=((smooth_function_compact_support_iff (hEA k) KA
  (smooth_test_inclusion (hEA k) alpha)).1 (fun x hx=>hx)).
have hOffB:=((smooth_function_compact_support_iff (hEB l) KB
  (smooth_test_inclusion (hEB l) beta)).1 (fun x hx=>hx)).
change (forall x,~smooth_compact_carrier KA x->ta k alpha x=0) in hOffA.
change (forall x,~smooth_compact_carrier KB x->tb l beta x=0) in hOffB.
change (@smooth_function_support R Z (A_m Z R^o (k+l)) NZ hNZ AB (EC (k+l)) (vc (k+l))
  (smooth_test_inclusion (hEC (k+l)) (Pure k l alpha beta)) `<=`
  @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB)).
rewrite -hK.
apply:(smooth_function_compact_support_iff (hEC (k+l)) K
  (smooth_test_inclusion (hEC (k+l)) (Pure k l alpha beta))).2=>z hOutside.
change (@current_test_value R h2 (m+n) AB hAB (k+l) (Pure k l alpha beta) z=0).
case:(pselect (AB z))=>hz.
- rewrite ((@CartesianTestProduct.laws R h2 m n A B hA hB k l).2 alpha beta z hz).
  have hWedge:=@form_wedge_bilinear R h2 Z R^o (fun a b:R^o=>a*b) (scalar_bilinear R) k l.
  case:(pselect (smooth_compact_carrier KA (p z)))=>hFirst.
  + have hLast:~smooth_compact_carrier KB (q z).
      move=>hLast;apply:hOutside;rewrite hK;by split.
    rewrite (@hOffB (q z) hLast) linear0 (bil0r hWedge);reflexivity.
  + rewrite (@hOffA (p z) hFirst) linear0 (bil0l hWedge);reflexivity.
- exact:(smooth_test_value_outside (hEC (k+l)) (Pure k l alpha beta) hz).
Qed.
End CurrentCartesianTestProductSupport.
