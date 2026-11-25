(** Federer (1969), 4.1.1, p. 346: the
    derivative of D^k phi in a fixed direction
    is D^k of that directional derivative. This
    supporting argument moves one argument through
    the symmetric differential of 3.1.11, p. 220. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP NormHigherDifferentialUP
  NormHigherDifferentialSymmetricForm SymmetricForms MultilinearArguments
  MultilinearSuccessorArguments MultilinearArgumentSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_first_last_exchange]: symmetry
    moves a single first argument to the last
    position without changing a higher differential,
    supporting the Taylor argument of Federer
    4.1.1, p. 346. Arity casts change
    only the representation of the natural-number sum. *)
Theorem norm_higher_first_last_exchange (R:realType) k (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R) (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (U:X->Prop) (f:X->Y) a (z:Z k.+1):
  has_norm_higher_differential NX ev ZN U f k.+1 a z ->forall (u:{ffun 'I_k->X}) v,
    @ev k.+1 (multilinear_arguments_cast (add1n k)
      (multilinear_arguments_join [ffun _: 'I_1=>v] u)) z=
    @ev k.+1 (multilinear_successor_arguments u v) z.
Proof.
move=>hz u v.
have [phi [hPhi _]]:=norm_higher_differential_symmetric_form_exists hNX hNY hZ hz.
pose A:=multilinear_arguments_cast (add1n k)
  (multilinear_arguments_join [ffun _: 'I_1=>v] u).
pose B:=multilinear_successor_arguments u v.
pose tA:=( [tuple A i|i<k.+1] ).
pose tB:=( [tuple B i|i<k.+1] ).
have hPerm:perm_eq tA tB.
  change (perm_eq (multilinear_argument_sequence A) (multilinear_argument_sequence B)).
  rewrite /A /B multilinear_argument_sequence_cast multilinear_argument_sequence_join
    multilinear_argument_sequence_successor.
  have hOne:multilinear_argument_sequence [ffun _: 'I_1=>v]=[::v].
    by rewrite /multilinear_argument_sequence enum_ordSl enum_ord0 /= ffunE.
  by rewrite hOne perm_catC perm_refl.
have hEq:=@sform_tuple_symmetric R X Y k.+1 phi tA tB hPerm.
have hA:[ffun i=>tnth tA i]=A by apply/ffunP=>i; by rewrite ffunE tnth_mktuple.
have hB:[ffun i=>tnth tB i]=B by apply/ffunP=>i; by rewrite ffunE tnth_mktuple.
by rewrite !hPhi hA hB in hEq.
Qed.
