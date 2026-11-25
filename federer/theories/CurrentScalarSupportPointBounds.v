(** Federer (1969), 4.1.12, p. 367: the
    scalar multiplier bound uses test values only
    on K intersect spt gamma. Off the scalar
    support both gamma and d gamma vanish. The
    original pointwise comass estimates keep constant one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear TensorUP RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces CurrentTestFormProduct
  CurrentTestExteriorDerivative SmoothCurrentExteriorDerivative
  CurrentFormSupportValues CurrentScalarProductDerivativeValues CurrentScalarProductNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentScalarSupportPointBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E k := (@current_smooth_space R h2 n U hU k).
Local Notation sv k := (@current_smooth_value R h2 n U hU k).
Local Notation DT k := (@current_test_space R h2 n U hU k).
Local Notation value k := (@current_test_value R h2 n U hU k).
Local Notation N k := (@current_form_comass R h2 n k).
Local Notation sd k := (@smooth_current_exterior_derivative R h2 n k U hU).
Local Notation td k := (@current_test_exterior_derivative R h2 n k U hU).
Local Notation product gamma := (@current_test_form_product R h2 n 0%N m U hU gamma).
Local Notation support := (@smooth_function_support R X (A_m X R^o 0%N) NX hNX U (E 0%N) (sv 0%N)).

(** Source for [current_scalar_supported_product_point_bounds]:
    pointwise bounds on gamma and d gamma on K,
    and on phi and d phi on K intersect spt gamma,
    give the two original product bounds on K,
    supporting Federer 4.1.12, p. 367. The
    scalar support is relative to U, and empty
    compact sets require no separate nonemptiness premise. *)
Theorem current_scalar_supported_product_point_bounds
    (K L:smooth_compact_set hNX U) (gamma:E 0%N) (phi:DT m) a b f:
  smooth_compact_carrier L=smooth_compact_carrier K `&` support gamma->
  0<=a->0<=b->0<=f->
  (forall x,smooth_compact_carrier K x->N 0%N (sv 0%N gamma x)<=a)->
  (forall x,smooth_compact_carrier K x->N 1%N (sv 1%N (sd 0%N gamma) x)<=b)->
  (forall x,smooth_compact_carrier L x->N m (value m phi x)<=f)->
  (forall x,smooth_compact_carrier L x->N m.+1 (value m.+1 (td m phi) x)<=f)->
  forall x,smooth_compact_carrier K x->
    N m (value m (product gamma phi) x)<=a * f /\
    N m.+1 (value m.+1 (td m (product gamma phi)) x)<=(a+b) * f.
Proof.
move=>hL ha hb hf hGamma hDgamma hPhi hDphi x hx.
have hUx:=smooth_compact_in_domain K x hx.
case:(pselect (support gamma x))=>hSupport.
- have hLx:smooth_compact_carrier L x by rewrite hL;split.
  have hPhiNorm:=hPhi x hLx.
  have hDphiNorm:=hDphi x hLx.
  have hGammaNorm:=hGamma x hx.
  have hDgammaNorm:=hDgamma x hx.
  have hProduct:N 0%N (sv 0%N gamma x) * N m (value m phi x)<=a * f.
    apply:(le_trans (ler_wpM2r (real_seminorm_nonnegative
      (@current_form_comass_real_norm R h2 n m).1 (value m phi x)) hGammaNorm)).
    exact:(ler_wpM2l ha hPhiNorm).
  have hDgammaProduct:N 1%N (sv 1%N (sd 0%N gamma) x) * N m (value m phi x)<=b * f.
    apply:(le_trans (ler_wpM2r (real_seminorm_nonnegative
      (@current_form_comass_real_norm R h2 n m).1 (value m phi x)) hDgammaNorm)).
    exact:(ler_wpM2l hb hPhiNorm).
  have hDphiProduct:N 0%N (sv 0%N gamma x) * N m.+1 (value m.+1 (td m phi) x)<=a * f.
    apply:(le_trans (ler_wpM2r (real_seminorm_nonnegative
      (@current_form_comass_real_norm R h2 n m.+1).1 (value m.+1 (td m phi) x)) hGammaNorm)).
    exact:(ler_wpM2l ha hDphiNorm).
  split.
  + exact:le_trans (@current_scalar_test_product_comass_bound R h2 n m U hU gamma phi x hUx) hProduct.
  + apply:(le_trans (@current_scalar_test_derivative_comass_bound R h2 n m U hU gamma phi x hUx)).
    rewrite mulrDl [a*f+b*f]addrC;exact:lerD hDgammaProduct hDphiProduct.
- have hGammaZero:=@current_form_value_outside_support R h2 n 0%N U hU gamma x hUx hSupport.
  have hDgammaZero:=@current_form_exterior_outside_support R h2 n 0%N U hU gamma x hUx hSupport.
  have hProductZero:value m (product gamma phi) x=0.
    rewrite (@current_test_form_product_values R h2 n 0%N m U hU gamma phi x hUx) hGammaZero.
    exact:(bil0l (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) 0%N m) _).
  have hDerivativeZero:value m.+1 (td m (product gamma phi)) x=0.
    rewrite (@current_scalar_product_derivative_values R h2 n m U hU gamma phi x hUx)
      hGammaZero hDgammaZero
      (bil0l (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) 1%N m))
      (bil0l (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) 0%N m.+1)).
    exact:add0r.
  split.
  + rewrite hProductZero (real_seminorm_zero (@current_form_comass_real_norm R h2 n m).1).
    exact:mulr_ge0 ha hf.
  + rewrite hDerivativeZero (real_seminorm_zero (@current_form_comass_real_norm R h2 n m.+1).1).
    exact:mulr_ge0 (addr_ge0 ha hb) hf.
Qed.
End CurrentScalarSupportPointBounds.
