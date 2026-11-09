(** Federer (1969), 3.4.5, p. 319: the
    independent symmetry and factorial bounds on coefficient
    sequences used to prove compactness of the growth classes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed FiniteArgumentPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_formal_analytic_jet]: independently stated
    coefficient laws in the compactness argument of 3.4.5,
    p. 319. Each coefficient has actual multilinear symmetry
    and the printed norm bound. Analytic realisation is a
    theorem to prove, and is not a field of this predicate. *)
Record is_formal_analytic_jet (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (s t:nat)
    (w:forall m,@ContinuousMultilinear.space R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)):Prop:={
  (** Source for [formal_analytic_jet_symmetric]: symmetry of
      every actual coefficient, 3.1.11, p. 220,
      as used in 3.4.5, p. 319. *)
  formal_analytic_jet_symmetric:forall m (sigma:'S_m) (u:{ffun 'I_m->X}),
    @ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
      (finite_argument_permutation sigma u) (w m)=
    @ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R) u (w m);
  (** Source for [formal_analytic_jet_growth]: the original
      all-order factorial bound of 3.4.5, p. 319,
      including its actual zeroth coefficient. *)
  formal_analytic_jet_growth:forall m,
    @ContinuousMultilinear.norm R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R) (w m)<=
      s%:R*t%:R^+m*(m`!)%:R
}.
