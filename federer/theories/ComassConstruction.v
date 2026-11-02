(** Federer (1969), 1.8.1, p. 38: existence of the comass supremum in finite
    dimension. The Cauchy pairing bound of 1.7.5 supplies a finite upper
    bound. This witness is private to the sealing module; downstream
    statements use the supremum laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP InnerNorm ExteriorGrading
  AlternatingCoordinates AlternatingPairing ExteriorNorm ExteriorCovectorInner
  ExteriorPairingBound SimpleUnitBall ComassUP LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [comass_exists]: Federer 1.8.1, p. 38,
    existence of the defining supremum for each covector. This uses
    only real order completeness and the previously proved pairing bound;
    finite-dimensional compactness will prove attainment separately. *)
Theorem comass_exists (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N)
    (phi : A_m V R^o m) : exists c, is_comass h2 hB phi c.
Proof.
pose D := (fun x => pairing x phi) @` (@simple_unit_ball R h2 V B hB m).
have hn : D !=set0.
  exists (pairing 0 phi); exists 0 => //; exact: simple_unit_ball_zero.
have hb : ubound D (exterior_covector_norm h2 hB he phi).
  move=> r [x [hs hx] <-].
  have hh := le_trans (ler_norm (pairing x phi))
    (@exterior_pairing_bound R h2 V B hB n e he m x phi).
  apply: (le_trans hh).
  have hnon : 0 <= exterior_covector_norm h2 hB he phi := inner_norm_nonnegative _ _.
  have ht := ler_wpM2r hnon hx.
  by rewrite mul1r in ht.
have hu : has_ubound D by exists (exterior_covector_norm h2 hB he phi).
have hd : has_sup D by split.
exists (sup D); constructor.
- move=> x hx; apply: (sup_upper_bound hd); by exists x.
- move=> eps heps; have [r [x hx hxr] hr] := sup_adherent heps hd.
  exists x; split=> //; by rewrite hxr.
Qed.
