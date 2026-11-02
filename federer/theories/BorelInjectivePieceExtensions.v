(** Federer (1969), 3.2.9, p. 247: extend
    both Lipschitz restrictions on each Borel piece
    using the already sealed Kirszbraun theorem
    2.10.43, p. 201. The forward map
    is prescribed only on E, as printed. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  InjectiveDifferentialPieceUP InjectivePieceLipschitzRestrictions InnerOwnNormTopology TopologicalBorel
  KirszbraunTheorem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [borel_injective_piece_global_extensions]:
    the global Lipschitz maps in Federer 3.2.9,
    p. 247. On a 3.2.2 piece E,
    extend f restricted to E and its
    inverse restricted to f(E). The resulting
    maps are inverse on E; no identity
    outside E or its prescribed image is claimed. *)
Theorem borel_injective_piece_global_extensions (R:realType) m n
    (f:R_n R m->R_n R n) (lambda:R) (E:set (R_n R m)):
  is_injective_differential_piece f lambda E ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] E /\
  exists (u:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (v:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R m)),
    is_metric_lipschitz setT u /\ is_metric_lipschitz setT v /\
    forall x,E x -> u x=f x /\ v (u x)=x.
Proof.
move=>hPiece; split.
- exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) E).2 hPiece.1).
- have [hF [g [hG hInverse]]]:=injective_piece_forward_inverse_lipschitz hPiece.
  have [u [hu [hU _]]]:=federer_2_10_43 hF.
  have [v [hv [hV _]]]:=federer_2_10_43 hG.
  exists u,v; split; first exact hu; split; first exact hv.
  move=>x hx; split; first exact:hU x hx.
  rewrite (hU x hx) (hV (f x) ltac:(by exists x)); exact:hInverse x hx.
Qed.
