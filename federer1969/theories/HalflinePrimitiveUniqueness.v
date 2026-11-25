(** Federer (1969), 4.1.7, p. 359:
    the primitive is unique after requiring
    its intended agreement with the original
    current T on U=(0,infinity).
    The bare boundary equation is treated
    separately by the two actual primitives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import CurrentDensityUP Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces CurrentBoundary
  CurrentDiracDensity CurrentOpenRestriction CurrentOpenConstantDensity EuclideanFundamentalCurrent
  EuclideanFundamentalCurrentNonzero TopCurrentGlobalConstancy HalflineCurrents HalflinePrimitiveBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflinePrimitiveUniqueness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation U := (@current_halfline_domain R).
Local Notation hU := (@current_halfline_domain_open R).
Local Notation C := (@full_current_space R h2 1 1%N).
Local Notation Q := (@current_open_restriction R h2 1 1%N U (fun _=>True) hU hFull
  (fun _ _=>Logic.I)).

(** Source for [halfline_primitive_unique_with_agreement]:
    the corrected uniqueness assertion intended
    in Federer 4.1.7, p. 359:
    boundary delta_b together with restriction
    to the original T determines the
    displayed left primitive. The proof uses
    the immediately preceding constancy theorem. *)
Theorem halfline_primitive_unique_with_agreement b (S:C):
  @current_boundary R h2 1 0%N (fun _=>True) hFull S=
    @full_dirac_current R h2 1 (euclidean_one_embed b)->
  Q S=@halfline_current R h2 b->S=@halfline_left_primitive_candidate R h2 b.
Proof.
move=>hBoundary hAgreement.
have hZeroBoundary:@current_boundary R h2 1 0%N (fun _=>True) hFull
    (S-@halfline_left_primitive_candidate R h2 b)=0.
  have hLinear:@current_boundary R h2 1 0%N (fun _=>True) hFull
      (S-@halfline_left_primitive_candidate R h2 b)=
      @current_boundary R h2 1 0%N (fun _=>True) hFull S-
      @current_boundary R h2 1 0%N (fun _=>True) hFull
        (@halfline_left_primitive_candidate R h2 b).
    exact:linearB.
  exact:(eq_trans hLinear (eq_trans
    (congr2 (fun V W:@full_current_space R h2 1 0%N=>V-W)
      hBoundary (@halfline_left_primitive_boundary R h2 b)) (subrr _))).
have [c hc]:=@top_current_global_constancy R h2 0%N
  (S-@halfline_left_primitive_candidate R h2 b) hZeroBoundary.
have hLinear:Q (S-@halfline_left_primitive_candidate R h2 b)=
    Q S-Q (@halfline_left_primitive_candidate R h2 b).
  exact:linearB.
have hScaled:Q (c*:@euclidean_fundamental_current R h2 1)=
    c*:Q (@euclidean_fundamental_current R h2 1).
  exact:linearZ.
have hTransport:=eq_trans (esym hLinear) (eq_trans (congr1 Q hc) hScaled).
have hRestricted:Q S-@halfline_current R h2 b=
    c*:@euclidean_fundamental_current_open R h2 1 U hU.
  exact:(eq_trans hTransport (congr1 (fun V:@current_space R h2 1 U hU 1%N=>c*:V)
    (esym (@euclidean_fundamental_current_open_restriction R h2 1 U hU)))).
rewrite hAgreement subrr in hRestricted.
have hNonempty:exists x,U x.
  exists (euclidean_one_embed (1:R)).
  change (is_true (0<euclidean_one_project (euclidean_one_embed (1:R)))).
  by rewrite euclidean_one_embedK ltr01.
have hNonzero:=@euclidean_fundamental_current_open_nonzero R h2 1 U hU hNonempty.
have hcZero:c=0.
  have hDisjunction:(c==0)||(@euclidean_fundamental_current_open R h2 1 U hU==0).
    rewrite -scaler_eq0;apply/eqP;exact:esym hRestricted.
  have /orP [/eqP hc0|/eqP hE0]:=hDisjunction;first exact:hc0.
  exact:False_ind _ (hNonzero hE0).
rewrite hcZero scale0r in hc.
apply/eqP;rewrite -subr_eq0;exact/eqP.
Qed.
End HalflinePrimitiveUniqueness.
