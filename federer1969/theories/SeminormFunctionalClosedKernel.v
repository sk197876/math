(** Federer (1969), 4.1.19, p. 377:
    the weak equation annihilates the J-closure
    of smooth graph pairs by the original
    bound on beta. The preceding item
    identifies that closure with ker q. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [seminorm_functional_annihilates_closure]:
    bounded beta vanishes on the closure
    of its zero set, the continuity step
    in the converse of Federer 4.1.19,
    p. 377. Raw seminorm-null vectors
    and the zero functional bound remain allowed. *)
Theorem seminorm_functional_annihilates_closure (R : realType)
    (P : lmodType R) (J : P -> R) (beta : Hom P R^o)
    (c : R) (G : set P) (v : P) :
  0 <= c -> (forall w, `|beta w| <= c*J w) ->
  (forall w, G w -> beta w=0) ->
  (forall delta : R, 0 < delta -> exists w : P,
    G w /\ J (v-w)%R < delta) -> beta v=0.
Proof.
move=> hC hBound hZero hApprox.
have hLimit : ((`|beta v|)%:E <= (0:R)%:E)%E.
  apply: (@extended_upper_bound_from_scaled_errors R (`|beta v|)%:E 0 c hC).
  move=> delta hDelta.
  have [w [hW hDistance]] := hApprox delta hDelta.
  have h := hBound (v-w)%R.
  rewrite (linB (hom_linear beta)) (hZero w hW) subr0 in h.
  rewrite add0r lee_fin.
  exact: (le_trans h (ler_wpM2l hC (ltW hDistance))).
have hAbsolute : `|beta v|=0.
  apply/eqP; rewrite eq_le normr_ge0 andbT.
  by rewrite lee_fin in hLimit.
by apply/eqP; move/eqP: hAbsolute; rewrite normr_eq0.
Qed.
