(** Opaque interfaces for ap Df and ap D_i f, Federer (1969), 3.1.2,
    p. 212. Only the exact partial graph laws are exported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations RealNormUP PartialFunctionUP
  ApproximateDifferentialUP ApproximatePartialDerivativeUP ApproximateDifferentialConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ApproximateDifferentialSignature.
(** Source for [value]: ap Df from Federer 3.1.2, p. 212. *)
Parameter value : forall (R : realType) n (Y : lmodType R)
  (NY : Y -> R), is_real_norm NY ->
  (R_n R n -> Prop) -> (R_n R n -> Y) ->
  partial_function (R_n R n) (Hom (R_n R n) Y).
(** Source for [laws]: the defining graph of ap Df, Federer 3.1.2, p. 212. *)
Parameter laws : forall (R : realType) n (Y : lmodType R)
  (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop) (f : R_n R n -> Y),
  is_approximate_differential_graph NY A f (@value R n Y NY hNY A f).
(** Source for [partial_value]: ap D_i f from Federer 3.1.2, p. 212. *)
Parameter partial_value : forall (R : realType) n (Y : lmodType R)
  (NY : Y -> R), is_real_norm NY ->
  (R_n R n -> Prop) -> (R_n R n -> Y) -> 'I_n -> partial_function (R_n R n) Y.
(** Source for [partial_laws]: exact approximate partial-derivative graph,
    Federer 3.1.2, p. 212. *)
Parameter partial_laws : forall (R : realType) n (Y : lmodType R)
  (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
  (f : R_n R n -> Y) (i : 'I_n),
  is_approximate_partial_derivative_graph hNY A f i (@partial_value R n Y NY hNY A f i).
End ApproximateDifferentialSignature.

Module ApproximateDifferential : ApproximateDifferentialSignature.
(** Source for [value]: select the proved exact graph of ap Df,
    Federer 3.1.2, p. 212, privately behind its specification. *)
Definition value (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop) (f : R_n R n -> Y) :=
  projT1 (cid (approximate_differential_graph_exists hNY A f)).
(** Source for [laws]: the selected graph satisfies the definition
    of ap Df in Federer 3.1.2, p. 212. *)
Lemma laws (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop) (f : R_n R n -> Y) :
  is_approximate_differential_graph NY A f (@value R n Y NY hNY A f).
Proof. exact: projT2 (cid (approximate_differential_graph_exists hNY A f)). Qed.
(** Source for [partial_value]: select the proved exact graph of ap D_i f,
    Federer 3.1.2, p. 212, privately behind its specification. *)
Definition partial_value (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (i : 'I_n) :=
  projT1 (cid (approximate_partial_derivative_graph_exists hNY A f i)).
(** Source for [partial_laws]: the selected graph satisfies the definition
    of ap D_i f in Federer 3.1.2, p. 212. *)
Lemma partial_laws (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (i : 'I_n) :
  is_approximate_partial_derivative_graph hNY A f i (@partial_value R n Y NY hNY A f i).
Proof. exact: projT2 (cid (approximate_partial_derivative_graph_exists hNY A f i)). Qed.
End ApproximateDifferential.
