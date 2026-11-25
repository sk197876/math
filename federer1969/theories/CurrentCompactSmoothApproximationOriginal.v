(** Federer (1969), 4.1.14, p. 370: the chosen
    compact-closure family is one of the original allowed
    smooth approximations. Its additional neighbourhood
    bounds prove existence only; the defining image law
    continues to quantify every K-only bounded family. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentLipschitzCompactImage CurrentSmoothApproximationUP
  CurrentCompactSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CurrentCompactSmoothApproximationOriginal.
Variable R:realType.
Variables n nu:nat.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Variable f:R_n R n->R_n R nu.
Variable L:R.
Variable Z:set (R_n R n).
Variable g:nat->R_n R n->R_n R nu.
Hypothesis hApprox:@is_current_compact_smooth_approximation R n nu U V K f L Z g.

(** Source for [current_compact_smooth_domain_in_domain]: the
    chosen Z is a source neighbourhood inside U, Federer
    4.1.14, p. 370; its compact closure already lies in U. *)
Lemma current_compact_smooth_domain_in_domain:Z `<=` U.
Proof.
move=>x hx;apply:(current_compact_smooth_closure_in_domain hApprox).
exact:subset_closure hx.
Qed.

(** Source for [current_compact_smooth_original_approximation]:
    the chosen family satisfies the literal approximation
    assumptions in Federer 4.1.14, p. 370. Only the
    restriction of its proved derivative cap to K is used. *)
Theorem current_compact_smooth_original_approximation:
  @is_current_smooth_approximation R n nu Z V
    (@current_compact_index_in_open R n U Z K
      (current_compact_smooth_domain_contains hApprox)) f g.
Proof.
constructor.
- exact:current_compact_smooth_image hApprox.
- exact:current_compact_smooth_class hApprox.
- exists L;split;first exact:current_compact_smooth_bound_nonnegative hApprox.
  move=>i x hx.
  have hxZ:Z x:=current_compact_smooth_domain_contains hApprox hx.
  exact (@current_compact_smooth_differential_bound R n nu U V K f L Z g
    hApprox i x hxZ).
- exact:current_compact_smooth_uniform hApprox.
Qed.
End CurrentCompactSmoothApproximationOriginal.
