(** Federer (1969), 4.1.25, p. 383: an original
    compact target test has one finite global comass bound.
    Compact support and the preceding continuity theorem
    supply it, including all exterior degrees and the
    one-point Euclidean space of dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentSpaces CurrentCoefficientNorms SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  NormCompactFunctionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_lipschitz_lebesgue_action_test_bound]:
    the finite test-form bound in the dominated-convergence
    proof of 4.1.25, p. 383, from the original
    compact-support test space of 4.1.1, pp. 344–345.
    No finite-volume assumption on the ambient space occurs. *)
Theorem current_lipschitz_lebesgue_action_test_bound
    (R:realType) (h2:(1+1:R)!=0) n k
    (phi:@current_test_space R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) k) :
  exists B:R,0<B /\ forall x,
    @current_form_comass R h2 n k
      (@current_test_value R h2 n (fun _=>True)
        (fun (x:R_n R n) (_:True)=>norm_full_domain_interior
          (inner_norm (@euclidean_inner_productP R n)) x) k phi x)<=B.
Proof.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose PN:=@current_form_comass R h2 n k.
pose hPN:=@current_form_comass_real_norm R h2 n k.
pose Full:=fun _:X=>True.
pose hFull:=fun (x:X) (_:True)=>norm_full_domain_interior NX x.
pose E:=@current_smooth_space R h2 n Full hFull k.
pose ev:=@current_smooth_value R h2 n Full hFull k.
pose hE:=@current_smooth_space_laws R h2 n Full hFull k.
pose value:=@current_test_value R h2 n Full hFull k.
have hSmooth:=@smooth_test_value_smooth R X (A_m X R^o k)
  NX PN hNX hPN Full E ev hE phi.
have [K hK]:=smooth_test_support_bound hE phi.
have hZero:=(@smooth_function_compact_support_iff R X (A_m X R^o k)
  NX PN hNX hPN Full E ev hE K (smooth_test_inclusion hE phi)).1 hK.
have [B [hB hBound]]:=@norm_class_zero_compact_bounded R X (A_m X R^o k)
  NX PN hNX hPN Full (smooth_compact_carrier K) (value phi)
  (smooth_compact_is_compact K) (smooth_compact_in_domain K)
  (norm_class_continuous (hSmooth 0%N)).
exists B;split;first exact:hB.
move=>x;case:(pselect (smooth_compact_carrier K x))=>hx.
- exact:hBound x hx.
- have hValue:value phi x=0:=hZero x hx.
  change (PN (value phi x)<=B).
  by rewrite hValue (real_seminorm_zero hPN.1 : PN 0 = 0);exact:ltW hB.
Qed.
