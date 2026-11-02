(** Federer (1969), 3.2.22, pp. 258–260: each
    source/target chart pair has compact parameter and image
    sets. Compact fibres therefore have actual measurable
    Hausdorff masses in the local coarea comparison. *)
From mathcomp Require Import all_boot reals classical_sets topology.
From Federer Require Import RectifiableChartPairPieces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_rectifiable_chart_pair_parameters]:
    the auxiliary A_ij in Federer 3.2.22, p. 259,
    is compact when K_i and C_j are compact and
    all three maps are continuous. Intersect compact K_i
    with the closed preimage of gamma_j(C_j); no
    properness of F or its composite is required. *)
Lemma compact_rectifiable_chart_pair_parameters (R:realType)
    (X Y U V:metricType R) (K:set X) (C:set U)
    (psi:X->Y) (F:Y->V) (gamma:U->V):
  compact K ->compact C ->continuous psi ->continuous F ->continuous gamma ->
  compact (rectifiable_chart_pair_parameters K C psi F gamma).
Proof.
move=>hK hC hPsi hF hGamma.
have hComp:continuous (fun a:X=>F (psi a)).
  move=>a; exact:(continuous_comp (hPsi a) (hF (psi a))).
have hImage:compact (gamma @` C):=continuous_compact (continuous_subspaceT hGamma) hC.
apply:(compact_closedI hK).
exact:((continuous_closedP _).1 hComp _ (compact_closed (@metric_hausdorff R V) hImage)).
Qed.

(** Source for [compact_rectifiable_chart_pair_piece]:
    P_ij in Federer 3.2.22, p. 258, is
    the continuous psi_i image of compact A_ij.
    This supports the compact local fibre measurability
    used in the integral comparison on p. 260. *)
Lemma compact_rectifiable_chart_pair_piece (R:realType)
    (X Y U V:metricType R) (K:set X) (C:set U)
    (psi:X->Y) (F:Y->V) (gamma:U->V):
  compact K ->compact C ->continuous psi ->continuous F ->continuous gamma ->
  compact (rectifiable_chart_pair_piece K C psi F gamma).
Proof.
move=>hK hC hPsi hF hGamma; rewrite rectifiable_chart_pair_image.
exact:(continuous_compact (continuous_subspaceT hPsi) (compact_rectifiable_chart_pair_parameters hK hC hPsi hF hGamma)).
Qed.
