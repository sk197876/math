(** Federer (1969), 4.1.7, p. 356: the
    original density current, with an opaque carrier
    value specified by its actual pairing integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom GrassmannAbbreviations ExteriorGrading MeasureUP
  CurrentDensityAction CurrentDensityUP CurrentDensityExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentDensitySignature.
(** Source for [value]: the original gamma wedge xi,
    supporting Federer 4.1.7, p. 356. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (gamma:set (R_n R n)->\bar R) (hGamma:is_measure gamma)
    (hBorel:@is_current_density_borel_measure R n gamma)
    (xi:R_n R n->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_current_density R h2 n m gamma xi),@full_current_space R h2 n m.
(** Source for [laws]: the exact original pairing
    integral on every actual test form, supporting
    Federer 4.1.7, p. 356. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (gamma:set (R_n R n)->\bar R) (hGamma:is_measure gamma)
    (hBorel:@is_current_density_borel_measure R n gamma)
    (xi:R_n R n->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_current_density R h2 n m gamma xi),
  is_current_density_action gamma xi (@value R h2 n m gamma hGamma hBorel xi hField).
End CurrentDensitySignature.
Module CurrentDensity:CurrentDensitySignature.
(** Source for [value]: seal the proved existence
    witness for the original density current,
    supporting Federer 4.1.7, p. 356. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (gamma:set (R_n R n)->\bar R) (hGamma:is_measure gamma)
    (hBorel:@is_current_density_borel_measure R n gamma)
    (xi:R_n R n->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_current_density R h2 n m gamma xi):@full_current_space R h2 n m:=
  projT1 (cid (@current_from_density_exists R h2 n m gamma hGamma hBorel xi hField)).
(** Source for [laws]: the opaque current has the
    independently specified original integral action,
    supporting Federer 4.1.7, p. 356. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (gamma:set (R_n R n)->\bar R) (hGamma:is_measure gamma)
    (hBorel:@is_current_density_borel_measure R n gamma)
    (xi:R_n R n->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_current_density R h2 n m gamma xi):
  is_current_density_action gamma xi (@value R h2 n m gamma hGamma hBorel xi hField).
Proof. exact:(projT2 (cid (@current_from_density_exists R h2 n m gamma hGamma hBorel xi hField))). Qed.
End CurrentDensity.
