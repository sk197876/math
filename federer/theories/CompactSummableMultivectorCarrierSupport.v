(** Federer (1969), 4.1.18, pp. 375–376:
    vanishing off a given original compact carrier gives
    literal ambient support containment of an Omega field.
    Reuse the earlier closed-support criterion, including
    null nonzero values of the original raw representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentCoefficientNorms SmoothCompactSet
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_summable_multivector_carrier_support]:
    the exact closed carrier used in both propositions
    bounds the literal original field support,
    Federer 4.1.18, pp. 375–376. *)
Theorem compact_summable_multivector_carrier_support (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (xi:@compact_summable_multivector_space R h2 n m U hU)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hOff:forall x:current_domain R n U,~smooth_compact_carrier K (set_val x)->
      @compact_summable_multivector_value R h2 n m U hU xi x=0):
  @compact_summable_multivector_ambient_support R h2 n m U hU xi `<=`
    smooth_compact_carrier K.
Proof.
pose XT:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose raw:=@compact_summable_multivector_ambient_value R h2 n m U hU xi.
have hClosed:closed (smooth_compact_carrier K:set XT).
  exact:compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact K).
apply:(@real_function_support_in_closed_set R XT
  (fun x:XT=>@current_vector_mass R h2 n m (raw x))
  (smooth_compact_carrier K) hClosed)=>x hx.
have hRaw:raw x=0.
  case:(pselect (U x))=>hUPoint.
  - pose p:current_domain R n U:=exist _ x (mem_set hUPoint).
    change (raw (set_val p)=0).
    exact:(eq_trans
      (@compact_summable_multivector_ambient_inside R h2 n m U hU xi p)
      (hOff p hx)).
  - exact:(@compact_summable_multivector_ambient_outside R h2 n m U hU xi x hUPoint).
rewrite hRaw;exact:real_seminorm_zero (@current_vector_mass_real_norm R h2 n m).1.
Qed.
