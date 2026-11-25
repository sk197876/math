(** Federer (1969), 4.1.5, p. 349: the
    actual abstract dual contains every original
    continuous functional. Its public surjectivity and
    least-bound norm laws prove the identification,
    without exposing a dual carrier construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousRealFunctional RealFunctionalNormUP
  ContinuousDualUP VectorDaniellHypotheses WeakDualFunctionalNorm WeakDualRealisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [weak_dual_realisation_exists]: the original
    weak Y* can be represented in the actual abstract
    dual with every evaluation and norm unchanged,
    supporting Federer 4.1.5, p. 349. *)
Theorem weak_dual_realisation_exists (R:realType) (Y:lmodType R) (NY:Y->R)
    (hNY:is_real_norm NY) (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN):
  exists J:weak_dual_space hNY->D,is_weak_dual_realisation ed DN J.
Proof.
have hAt (alpha:weak_dual_space hNY):exists d:D,
    ed d=weak_dual_functional_hom alpha /\
    DN d=dual_norm NY (val alpha).
  have hContinuous:is_continuous_real_functional hNY (hom_as_linear (weak_dual_functional_hom alpha)).
    exact:(set_valP alpha).2.
  have[d hd]:=continuous_dual_surjective hD hContinuous.
  exists d; split; first exact hd.
  have hNorm:=continuous_dual_norm_laws hD d.
  rewrite hd in hNorm.
  exact:(real_functional_norm_unique hNorm (weak_dual_functional_norm_laws alpha)).
have[J hJ]:=choice hAt.
exists J; constructor.
- move=>alpha y; have h:ed (J alpha)=weak_dual_functional_hom alpha:=(hJ alpha).1.
  by rewrite h /weak_dual_functional_hom.
- move=>alpha; exact:(hJ alpha).2.
Qed.
