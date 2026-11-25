(** Opaque continuous-endomorphism algebra for Federer (1969),
    3.1.11, p. 220. Only the algebra, evaluation,
    norm and proved laws are exposed to the inversion argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom AlgebraUP RealNormUP ContinuousOperatorSealed
  ContinuousOperatorAlgebraUP ContinuousOperatorAlgebraConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ContinuousOperatorAlgebraSignature.
(** Source for [space]: the algebra E of continuous
    endomorphisms in Federer 3.1.11, p. 220. *)
Parameter space : forall (R : realType) (X : lmodType R)
  (NX : X->R), is_real_norm NX -> algebra R.
(** Source for [evaluation]: faithful operator evaluation
    in Federer 3.1.11, p. 220. *)
Parameter evaluation : forall (R : realType) (X : lmodType R)
  (NX : X->R) (hNX : is_real_norm NX),
  Hom (@space R X NX hNX) (Hom X X).
(** Source for [norm]: the operator norm on E,
    Federer 3.1.11, p. 220. *)
Parameter norm : forall (R : realType) (X : lmodType R)
  (NX : X->R) (hNX : is_real_norm NX), @space R X NX hNX -> R.
(** Source for [laws]: the complete abstract specification
    of E is proved, Federer 3.1.11, p. 220. *)
Parameter laws : forall (R : realType) (X : lmodType R)
  (NX : X->R) (hNX : is_real_norm NX),
  is_continuous_operator_algebra NX (@evaluation R X NX hNX) (@norm R X NX hNX).
End ContinuousOperatorAlgebraSignature.

Module ContinuousOperatorAlgebra : ContinuousOperatorAlgebraSignature.
(** Source for [space]: private proved algebra for E,
    Federer 3.1.11, p. 220. *)
Definition space (R : realType) (X : lmodType R)
    (NX : X->R) (hNX : is_real_norm NX) : algebra R :=
  @continuous_operator_algebra_witness R X NX hNX.
(** Source for [evaluation]: private evaluation witness
    for E, Federer 3.1.11, p. 220. *)
Definition evaluation (R : realType) (X : lmodType R)
    (NX : X->R) (hNX : is_real_norm NX) : Hom (@space R X NX hNX) (Hom X X) :=
  @ContinuousOperator.evaluation R X X NX NX hNX hNX.
(** Source for [norm]: private least-bound norm witness
    for E, Federer 3.1.11, p. 220. *)
Definition norm (R : realType) (X : lmodType R)
    (NX : X->R) (hNX : is_real_norm NX) : @space R X NX hNX -> R :=
  @ContinuousOperator.norm R X X NX NX hNX hNX.
(** Source for [laws]: proof of all algebra and norm
    promises, Federer 3.1.11, p. 220. *)
Lemma laws (R : realType) (X : lmodType R)
    (NX : X->R) (hNX : is_real_norm NX) :
  is_continuous_operator_algebra NX (@evaluation R X NX hNX) (@norm R X NX hNX).
Proof. exact: continuous_operator_algebra_witness_laws. Qed.
End ContinuousOperatorAlgebra.
