(** Federer (1969), 3.4.6, p. 322: the two
    original mixed-derivative argument blocks agree in the
    tuple and grouped finite-family interfaces of 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ConcatenatedFamilies MultilinearArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [weierstrass_joined_arguments_tuple]: grouping
    the original i and j blocks is precisely tuple
    concatenation, supporting the mixed divided coefficient
    formula of 3.4.6, p. 322. Empty blocks are retained. *)
Lemma weierstrass_joined_arguments_tuple (T:Type) i j
    (u:{ffun 'I_i->T}) (v:{ffun 'I_j->T}):
  multilinear_arguments_join u v=
    [ffun s=>tnth [tuple of [tuple u r | r<i]++[tuple v r | r<j]] s].
Proof.
have hTuple:[tuple multilinear_arguments_join u v s | s<(i+j)%N]=
    [tuple of [tuple u r | r<i]++[tuple v r | r<j]].
  apply:val_inj.
  change ([seq multilinear_arguments_join u v s |s<-enum 'I_(i+j)]=
    [seq u r|r<-enum 'I_i]++[seq v r|r<-enum 'I_j]).
  rewrite -(concatenate_family_sequence u v).
  apply:eq_map=>s;by rewrite /multilinear_arguments_join ffunE.
apply/ffunP=>s;by rewrite [RHS]ffunE -hTuple tnth_mktuple.
Qed.
