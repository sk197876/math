(** Federer (1969), 3.4.12, p. 338:
    complex scalar multiplication is a bounded real
    linear map on the original complex normed space.
    Its exact scalar equation and norm bound are
    proved from the independent complex norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ScalarRestriction
  ComplexScalarSealed ComplexNormUP ComplexModulus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_scalar_real_bounded_exists]: the
    bounded target scalar operation used to differentiate
    complex-linear jet identities in 3.4.12, p. 338.
    The selected map is only an existence witness;
    every scalar and original complex norm remain. *)
Theorem complex_scalar_real_bounded_exists (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (c:ComplexScalars.C R):
  exists M:Hom (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) X),
    (forall x,M x=c*:(x:X)) /\@norm_bounded_linear R
      (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) X) NX NX M.
Proof.
pose XR:=restricted_space (ComplexScalars.embed R) X.
have hLinear:linear (fun x:XR=>(c*:(x:X):XR)).
  move=>a x y.
  change (c*:((ComplexScalars.embed R a)*:(x:X)+y)=
    (ComplexScalars.embed R a)*:(c*:(x:X))+c*:(y:X)).
  by rewrite scalerDr !scalerA [c*ComplexScalars.embed R a]mulrC.
pose M:=@HomMap R XR XR (fun x=>c*:(x:X)) (introT (asboolP _) hLinear).
exists M;split;first by move=>x.
exists (complex_modulus c);split;first exact:complex_modulus_ge0.
move=>x;change (is_true (NX (c*:(x:X))<=complex_modulus c*NX x)).
by rewrite (complex_norm_scale hNX).
Qed.
