(** Federer (1969), 3.4.11, p. 338:
    independent laws for the first nonzero homogeneous
    Taylor polynomial of an original analytic germ.
    No tangent vanishing or dimension conclusion is
    included in the specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_initial_analytic_germ_polynomial]: the
    least positive nonzero derivative order and its exact
    factorial-normalized homogeneous Taylor polynomial in 3.4.11,
    p. 338, stated using the original opaque jets. *)
Definition is_initial_analytic_germ_polynomial (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (alpha:analytic_germ_space hNX (0:X)) k (P:X->R):Prop:=
  (0<k)%N /\@AnalyticGermJets.value R X NX hNX 0 k alpha<>0 /\
  (forall i,(i<k)%N ->@AnalyticGermJets.value R X NX hNX 0 i alpha=0) /\
  forall v,P v=(k`!)%:R^-1*:@ContinuousMultilinear.evaluation R k X R^o NX
    (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) [ffun _=>v]
    (@AnalyticGermJets.value R X NX hNX 0 k alpha).
