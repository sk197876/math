(** Federer (1969), 4.1.5, p. 349: identify
    the continuous real dual used in 2.5.12 with
    the actual abstract continuous dual Y*. Evaluation
    and the original dual norm determine this map. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP VectorDaniellHypotheses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_weak_dual_realisation]: exact
    evaluation and norm laws identifying the two
    presentations of the original Y* in Federer
    4.1.5, p. 349. Existence is separate. *)
Record is_weak_dual_realisation (R:realType) (Y:lmodType R) (NY:Y->R)
    (hNY:is_real_norm NY) (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (J:weak_dual_space hNY->D):Prop:={
  (** Source for [weak_dual_realisation_evaluation]: every
      original dual evaluation is unchanged, Federer
      4.1.5, p. 349. *)
  weak_dual_realisation_evaluation:forall alpha y,ed (J alpha) y=val alpha y;
  (** Source for [weak_dual_realisation_norm]: the original
      dual norm is unchanged, Federer 4.1.5, p. 349. *)
  weak_dual_realisation_norm:forall alpha,DN (J alpha)=dual_norm NY (val alpha)
}.
