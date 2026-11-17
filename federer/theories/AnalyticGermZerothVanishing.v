(** Federer (1969), 3.4.7, pp. 324–325:
    the value-zero condition is the zeroth derivative
    condition in the positive-order argument. This proof
    identifies the actual derivative, without choosing another
    formal power-series interpretation of the germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_zeroth_vanishing]: the
    original equation Phi(0)=0 in 3.4.7, p. 325,
    says exactly that the actual zeroth jet is zero. *)
Lemma analytic_germ_zeroth_vanishing (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (f:@analytic_representative_type R X NX hNX a):
  analytic_representative_value f a = 0 <->
  @AnalyticGermJets.value R X NX hNX a 0%N (analytic_germ f) = 0.
Proof.
pose ev:=@ContinuousMultilinear.evaluation R 0%N X R^o NX (fun t=>`|t|)
  hNX (@scalar_absolute_value_norm R).
pose jet:=@AnalyticGermJets.value R X NX hNX a 0%N (analytic_germ f).
have hActual:=@AnalyticGermJets.laws R X NX hNX a 0%N (analytic_germ f) f (erefl _).
split.
- move=>hValue;apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R 0%N
    X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)))=>u.
  have hu:u = [ffun _:'I_0=>(0:X)].
    by apply/ffunP=>i;have:=ltn_ord i;rewrite ltn0.
  rewrite hu linear0.
  exact:etrans hActual.2 hValue.
- move=>hJet.
  have hh:=hActual.2.
  by rewrite hJet linear0 in hh;exact:esym hh.
Qed.
