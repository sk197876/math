(** Federer (1969), 4.1.12, p. 367: the
    exact scalar multiplier coefficient is nu_K^0(gamma)
    plus nu_K^0(d gamma). The original test-product
    flat seminorm on K is controlled by this
    coefficient and the test seminorm on K intersect
    spt gamma. No support-step restriction is added. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionSupport SmoothFunctionTopology SmoothDerivativeSeminormUP
  SmoothDerivativeSeminormLaws SmoothTestSpaces CurrentTestFormProduct CurrentTestExteriorDerivative
  SmoothCurrentExteriorDerivative CurrentFlatFormSeminormLaws CurrentCompactZerothBounds
  CurrentScalarSupportPointBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatScalarTestProductBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E d := (@current_smooth_space R h2 n U hU d).
Local Notation sv d := (@current_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_smooth_space_laws R h2 n U hU d).
Local Notation hD d := (@current_smooth_derivative_laws R h2 n U hU d).
Local Notation nu d := (smooth_function_derivative_seminorm (hD d)).
Local Notation DT d := (@current_test_space R h2 n U hU d).
Local Notation inc d := (smooth_test_inclusion (hE d)).
Local Notation sd d := (@smooth_current_exterior_derivative R h2 n d U hU).
Local Notation td d := (@current_test_exterior_derivative R h2 n d U hU).
Local Notation Flat := (@current_flat_test_seminorm R h2 n m U hU).
Local Notation product gamma := (@current_test_form_product R h2 n 0%N m U hU gamma).
Local Notation support := (@smooth_function_support R X (A_m X R^o 0%N) NX hNX U (E 0%N) (sv 0%N)).

(** Source for [current_flat_scalar_coefficient]: the
    literal coefficient nu_K^0(gamma)+nu_K^0(d gamma)
    in the original multiplier estimate of Federer
    4.1.12, p. 367. It uses the actual
    scalar smooth form and exterior differential. *)
Definition current_flat_scalar_coefficient (K:smooth_compact_set hNX U) (gamma:E 0%N):R:=
  nu 0%N K 0%N gamma+nu 1%N K 0%N (sd 0%N gamma).

(** Source for [current_flat_scalar_coefficient_nonnegative]:
    the original multiplier coefficient is nonnegative,
    supporting Federer 4.1.12, p. 367, including
    empty K and the zero scalar multiplier. *)
Lemma current_flat_scalar_coefficient_nonnegative (K:smooth_compact_set hNX U) (gamma:E 0%N):
  0<=current_flat_scalar_coefficient K gamma.
Proof.
exact:addr_ge0 (smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws (hD 0%N) K 0%N) gamma)
  (smooth_derivative_seminorm_nonnegative
    (smooth_function_derivative_seminorm_laws (hD 1%N) K 0%N) (sd 0%N gamma)).
Qed.

(** Source for [current_flat_scalar_test_product_bound]:
    F_K(gamma wedge phi) is at most the exact
    printed scalar coefficient times F_(K intersect
    spt gamma)(phi), supporting Federer 4.1.12,
    p. 367. The statement accepts any compact
    descriptor of that literal intersection and every
    actual original compact test phi. *)
Theorem current_flat_scalar_test_product_bound
    (K L:smooth_compact_set hNX U) (gamma:E 0%N):
  smooth_compact_carrier L=smooth_compact_carrier K `&` support gamma->
  forall phi:DT m,Flat K (product gamma phi)<=current_flat_scalar_coefficient K gamma * Flat L phi.
Proof.
move=>hL phi.
pose a:=nu 0%N K 0%N gamma.
pose b:=nu 1%N K 0%N (sd 0%N gamma).
pose f:=Flat L phi.
have ha:0<=a:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws (hD 0%N) K 0%N) gamma.
have hb:0<=b:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws (hD 1%N) K 0%N) (sd 0%N gamma).
have hf:0<=f:=real_seminorm_nonnegative (@current_flat_test_is_seminorm R h2 n m U hU L) phi.
have hPhi:nu m L 0%N (inc m phi)<=f.
  rewrite /f /current_flat_test_seminorm current_flat_form_seminorm_formula;by rewrite le_max lexx.
have hDphi:nu m.+1 L 0%N (inc m.+1 (td m phi))<=f.
  rewrite current_test_exterior_derivative_inclusion /f /current_flat_test_seminorm
    current_flat_form_seminorm_formula;by rewrite le_max lexx orbT.
have hPoint:forall x,smooth_compact_carrier K x->
    @current_form_comass R h2 n m (@current_test_value R h2 n U hU m (product gamma phi) x)<=a * f /\
    @current_form_comass R h2 n m.+1 (@current_test_value R h2 n U hU m.+1
      (td m (product gamma phi)) x)<=(a+b) * f.
  apply:(@current_scalar_supported_product_point_bounds R h2 n m U hU K L gamma phi a b f
    hL ha hb hf).
  - exact:current_compact_zeroth_point_bound.
  - exact:current_compact_zeroth_point_bound.
  - move=>x hx;exact:le_trans
      (@current_compact_zeroth_point_bound R h2 n m U hU L (inc m phi) x hx) hPhi.
  - move=>x hx;exact:le_trans
      (@current_compact_zeroth_point_bound R h2 n m.+1 U hU L (inc m.+1 (td m phi)) x hx) hDphi.
have hProduct:nu m K 0%N (inc m (product gamma phi))<=a * f.
  apply:(@current_compact_zeroth_least_bound R h2 n m U hU K
    (inc m (product gamma phi)) (a*f) (mulr_ge0 ha hf))=>x hx.
  exact:(hPoint x hx).1.
have hDerivative:nu m.+1 K 0%N (inc m.+1 (td m (product gamma phi)))<=(a+b) * f.
  apply:(@current_compact_zeroth_least_bound R h2 n m.+1 U hU K
    (inc m.+1 (td m (product gamma phi))) ((a+b)*f) (mulr_ge0 (addr_ge0 ha hb) hf))=>x hx.
  exact:(hPoint x hx).2.
have hAB:a<=a+b.
  have h:=lerD (lexx a) hb;by rewrite addr0 in h.
change (Flat K (product gamma phi)<=(a+b) * f).
rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula
  -(@current_test_exterior_derivative_inclusion R h2 n m U hU (product gamma phi)) ge_max.
apply/andP;split.
- exact:le_trans hProduct (ler_wpM2r hf hAB).
- exact:hDerivative.
Qed.
End CurrentFlatScalarTestProductBound.
