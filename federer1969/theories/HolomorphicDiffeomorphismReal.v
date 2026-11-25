(** Federer (1969), 3.4.12, p. 339:
    the original holomorphic coordinate change is a real
    analytic class-one diffeomorphism. The existing real
    norm and exact original inverse maps are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ScalarRestriction ComplexScalarSealed RealNormUP
  NormDifferentialUP NormDifferentialLinear NormDiffeomorphismUP NormAnalyticLocal
  HolomorphicDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_diffeomorphism_real]: the real
    coordinate change underlying the original holomorphic straightening,
    3.4.12, p. 339. Every finite real
    class follows from actual analyticity, without completeness. *)
Theorem holomorphic_diffeomorphism_real (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x))
    (A B:X->Prop) (f g:X->X) k:
  is_holomorphic_diffeomorphism hNX A B f g ->
  is_norm_diffeomorphism hNX hNX A B f g k.
Proof.
move=>hD;constructor.
- exists (hom_of_linear (linear_id (restricted_space (ComplexScalars.embed R) X))),
    (hom_of_linear (linear_id (restricted_space (ComplexScalars.embed R) X))).
  have hId:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) X) NX NX (hom_of_linear (linear_id (restricted_space (ComplexScalars.embed R) X))).
    exists 1;split;first exact:ler01.
    by move=>x;rewrite hom_of_linearE mul1r.
  by split=>//;split=>//;split=>x;rewrite !hom_of_linearE.
- exact:(norm_analytic_class_all_orders (holomorphic_diffeomorphism_forward hD).1 k).
- exact:(norm_analytic_class_all_orders (holomorphic_diffeomorphism_inverse hD).1 k).
- exact:holomorphic_diffeomorphism_maps hD.
- exact:holomorphic_diffeomorphism_inverse_maps hD.
- exact:holomorphic_diffeomorphism_left_inverse hD.
- exact:holomorphic_diffeomorphism_right_inverse hD.
Qed.
