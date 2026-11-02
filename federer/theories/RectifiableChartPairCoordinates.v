(** Federer (1969), 3.2.22, p. 259: the
    coordinate map phi_ij=G_j composed F composed psi_i
    maps A_ij into C_j and recovers F composed psi_i
    through gamma_j on that exact parameter set. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import RectifiableChartPairPieces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_pair_coordinate_agreement]:
    F composed psi_i=gamma_j composed phi_ij on A_ij,
    Federer 3.2.22, p. 259. The actual inverse
    law of G_j on gamma_j(C_j) proves both target
    membership and equality, with no global inverse premise. *)
Lemma rectifiable_chart_pair_coordinate_agreement (X Y U V:Type)
    (K:set X) (C:set U) (psi:X->Y) (F:Y->V) (gamma:U->V) (G:V->U):
  (forall y,C y ->G (gamma y)=y) ->
  forall a,rectifiable_chart_pair_parameters K C psi F gamma a ->
    C (G (F (psi a))) /\ F (psi a)=gamma (G (F (psi a))).
Proof.
move=>hG a [_ [u hu hValue]].
have hPhi:G (F (psi a))=u by rewrite -hValue (hG u hu).
rewrite hPhi; split; first exact hu; exact:esym hValue.
Qed.
