(** Federer (1969), 4.1.7, p. 357:
    a boundary-free top current on the
    whole connected Euclidean space is a
    constant multiple of its oriented Lebesgue
    current. This is the whole-domain case
    of the original preceding constancy theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CurrentDensityUP CurrentEvaluation Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct NormSpaceConnected
  CurrentSpaces CurrentBoundary CurrentOpenRestriction CurrentOpenConstantDensity EuclideanFundamentalCurrent
  CurrentSupportExtensionality TopCurrentConstancy SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_fundamental_current_whole_restriction]:
    the original open restriction to the
    whole domain is the current itself,
    supporting Federer 4.1.7, p. 357. *)
Lemma euclidean_fundamental_current_whole_restriction (R:realType) (h2:(1+1:R)!=0) n:
  @euclidean_fundamental_current_open R h2 n (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x)=
  @euclidean_fundamental_current R h2 n.
Proof.
apply:(@current_values_extensional R h2 n n (fun _=>True)
  (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x))=>psi.
rewrite euclidean_fundamental_current_open_restriction current_open_restriction_evaluation.
congr (@current_value R h2 n (fun _=>True)
  (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) n _ _).
apply:(smooth_test_values_extensional (@current_smooth_space_laws R h2 n (fun _=>True)
  (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x) n))=>x _.
exact:current_open_test_extension_values.
Qed.

(** Source for [top_current_global_constancy]: the
    original positive-dimensional constancy theorem
    on the whole Euclidean space, Federer
    4.1.7, p. 357, used for
    the primitive uniqueness qualification on p. 359. *)
Theorem top_current_global_constancy (R:realType) (h2:(1+1:R)!=0) p
    (T:@full_current_space R h2 p.+1 p.+1):
  @current_boundary R h2 p.+1 p (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R p.+1)) x) T=0 ->
  exists c:R,T=c*:@euclidean_fundamental_current R h2 p.+1.
Proof.
move=>hBoundary.
pose U:set (R_n R p.+1):=fun _=>True.
pose hU:=fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R p.+1)) x.
have hEmpty:=(@current_empty_support_iff_zero R h2 p.+1 p U hU
  (@current_boundary R h2 p.+1 p U hU T)).2 hBoundary.
have [c hSupport]:=@top_current_constancy R h2 p U hU T U openT
  (@real_norm_space_connected R (R_n R p.+1) (inner_norm (@euclidean_inner_productP R p.+1))
    (inner_norm_real_norm (@euclidean_inner_productP R p.+1))) (fun _ hx=>hx)
  (fun x hx=>False_ind _ (hEmpty x hx)).
rewrite euclidean_fundamental_current_whole_restriction in hSupport.
have hZero:=(@current_empty_support_iff_zero R h2 p.+1 p.+1 U hU
  (T-c*:@euclidean_fundamental_current R h2 p.+1)).1
  (fun x hx=>(hSupport x hx).2 Logic.I).
exists c;apply/eqP;rewrite -subr_eq0;exact/eqP.
Qed.
