(** Federer (1969), 4.1.6, pp. 352–353: opaque
    linear alternation of the actual first differential.
    Existence was proved from the original coordinate
    expansion; uniqueness comes from the independent
    signed tuple specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom GrassmannAbbreviations AlternatingForms ExteriorDifferentialUP
  ExteriorDifferentialExistence ExteriorDifferentialLinearLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Module Type ExteriorDifferentialSignature.
(** Source for [value]: the alternating value of
    D phi(x), Federer 4.1.6, p. 352. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R) m,
  Hom (GrassmannAbbreviations.R_n R n) (A_m (GrassmannAbbreviations.R_n R n) W m)->
    A_m (GrassmannAbbreviations.R_n R n) W m.+1.
(** Source for [laws]: the original signed defining
    formula, Federer 4.1.6, p. 352. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R) m
  (L:Hom (GrassmannAbbreviations.R_n R n) (A_m (GrassmannAbbreviations.R_n R n) W m)),
  is_exterior_differential_value L (@value R h2 n W m L).
End ExteriorDifferentialSignature.
Module ExteriorDifferential:ExteriorDifferentialSignature.
(** Source for [value]: select the already proved
    alternating value, Federer 4.1.6, p. 352. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R) m
    (L:Hom (GrassmannAbbreviations.R_n R n) (A_m (GrassmannAbbreviations.R_n R n) W m)):
    A_m (GrassmannAbbreviations.R_n R n) W m.+1:=
  proj1_sig (cid (@euclidean_exterior_differential_exists R h2 n W m L)).
(** Source for [laws]: the selected value satisfies
    every original signed evaluation,
    Federer 4.1.6, p. 352. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R) m
    (L:Hom (GrassmannAbbreviations.R_n R n) (A_m (GrassmannAbbreviations.R_n R n) W m)):
  is_exterior_differential_value L (@value R h2 n W m L).
Proof. exact:(proj2_sig (cid (@euclidean_exterior_differential_exists R h2 n W m L))). Qed.
End ExteriorDifferential.

(** Source for [exterior_differential_linear]: exterior
    differentiation respects linear combinations,
    Federer 4.1.6, p. 353, at the level
    of actual first differentials. *)
Theorem exterior_differential_linear (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R) m:
  linear (@ExteriorDifferential.value R h2 n W m).
Proof.
move=>c L M; apply:exterior_differential_value_unique.
- exact:ExteriorDifferential.laws.
- exact:(exterior_differential_linear_values c (ExteriorDifferential.laws h2 L) (ExteriorDifferential.laws h2 M)).
Qed.

(** Source for [exterior_differential_map]: the linear
    Hom-to-form map in Federer 4.1.6,
    p. 353, exposed only through its proved laws. *)
Definition exterior_differential_map (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R) m:
    Hom (Hom (GrassmannAbbreviations.R_n R n) (A_m (GrassmannAbbreviations.R_n R n) W m))
      (A_m (GrassmannAbbreviations.R_n R n) W m.+1):=
  @HomMap R _ _ (@ExteriorDifferential.value R h2 n W m)
    (introT (asboolP _) (@exterior_differential_linear R h2 n W m)).
