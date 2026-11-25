(** Federer (1969), 1.7.8, p. 34: the mixed-degree pairing identity,
    corrected by the May 1987 erratum, p. 1, book p. 34 lines 29-30. The
    working source is docs/references/federer-erratum.tex. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP LinearBasis ExteriorGrading
  ExteriorNorm ExteriorHomogeneousProducts AlternatingCoordinates
  AlternatingPairing HodgeMaps HodgeSquare HodgePairing
  HodgeAlgebraCompatibility TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [hodge_mixed_pairing]: Federer 1.7.8,
    p. 34, final display, as corrected at erratum p. 1,
    book p. 34 lines 29-30: <xi,star beta> =
    (-1)^{p(n-p)} <star xi,beta>, where beta has degree n-p. *)
Theorem hodge_mixed_pairing (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (E : exterior_power V n) (hE : exterior_norm h2 hB E = 1)
    p (hp : (p <= n)%N) (x : exterior_power V p) (beta : A_m V R^o (n-p)) :
  pairing x (form_reindex (subKn hp) (hodge_covector h2 hB E (leq_subr p n) beta)) =
    (-1 : R)^+(p*(n-p)) * pairing (hodge_vector h2 hB E hp x) beta.
Proof.
have hh := @hodge_pairing R h2 V B hB n b hb E hE (n-p) (leq_subr p n)
  (hodge_vector h2 hB E hp x) beta.
have hi := @pairing_reindex R V (n-(n-p)) p (subKn hp)
  (hodge_vector h2 hB E (leq_subr p n) (hodge_vector h2 hB E hp x))
  (hodge_covector h2 hB E (leq_subr p n) beta).
rewrite -hi (@hodge_vector_square R h2 V B hB n b hb E hE p hp x)
  (bilZl (@pairing_bilinear R V R^o p)) in hh.
have hs := congr1 (fun r : R => (-1 : R)^+(p*(n-p)) * r) hh.
change ((-1 : R)^+(p*(n-p)) * ((-1 : R)^+(p*(n-p)) *
  pairing x (form_reindex (subKn hp) (hodge_covector h2 hB E (leq_subr p n) beta))) =
  (-1 : R)^+(p*(n-p)) * pairing (hodge_vector h2 hB E hp x) beta) in hs.
by rewrite mulrA -exprMn mulrNN mul1r expr1n mul1r in hs.
Qed.
