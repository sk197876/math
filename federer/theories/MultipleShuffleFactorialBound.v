(** Federer (1969), 3.1.24, p. 239: the
    factorial factor in the operator bound for a composition
    term, by the shuffle argument of 1.10.2 and 1.10.5. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import Shuffles MultipleShuffles MultipleShuffleBijection ShuffleCardinalityBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [multiple_shuffle_card_successor]: supporting
    the composition coefficient norm in Federer 3.1.24,
    p. 239. Splitting off the first block gives the
    product of the binary-shuffle count and the tail count,
    by the proved block-shuffle bijection of 1.4.2. *)
Lemma multiple_shuffle_card_successor p ds :
  #|{:Sh_multi (p::ds)}|= #|{:Sh p (sumn ds)}| * #|{:Sh_multi ds}|.
Proof.
have hh:=bij_eq_card (@compose_multiple_bijective p ds).
rewrite card_prod in hh; exact: esym hh.
Qed.

(** Source for [multiple_shuffle_factorial_bound]: supporting
    the factorial denominators in the composition norm estimate
    of Federer 3.1.24, p. 239. The number of
    block shuffles multiplied by the product of the block
    factorials is at most the total factorial. The bound
    follows from binary shuffle counts and Pascal factorials;
    empty and zero-size blocks are included. *)
Theorem multiple_shuffle_factorial_bound ds :
  #|{:Sh_multi ds}| * (\prod_(d<-ds) d`!) <= (sumn ds)`!.
Proof.
elim:ds=>[|p ds ih].
- rewrite big_nil /= muln1.
  have hi:injective (fun _ : Sh_multi [::]=>tt).
    move=>s t _; apply: val_inj; apply/permP=>i; by case:i=>i.
  have hh:=leq_card (fun _ : Sh_multi [::]=>tt) hi; by rewrite card_unit in hh.
- rewrite multiple_shuffle_card_successor big_cons /= mulnACA.
  have h1:=leq_mul (leqnn (#|{:Sh p (sumn ds)}| * p`!)) ih.
  have h2:=leq_mul (leq_mul (shuffle_cardinality_bound p (sumn ds)) (leqnn (p`!)))
    (leqnn (sumn ds)`!).
  have h3:=leq_trans h1 h2.
  have hp:(p<=p+sumn ds)%N:=leq_addr _ _.
  have hf:=bin_fact hp.
  rewrite addKn in hf.
  rewrite -hf.
  rewrite !mulnA in h3; rewrite !mulnA; exact h3.
Qed.
