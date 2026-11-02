(** Federer (1969), 3.2.28(2), printed p. 264:
    the vertical kernel of DQ. These supporting identities
    use alternating multilinearity of the actual exterior word,
    1.3.1–1.4.1, pp. 13–17, with no inner product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom TensorUP TensorFamilyUP FamilyUpdate
  Bilinear GradedComponents ExteriorAlgebra ExteriorGrading ExteriorExpansion
  FiniteExteriorPowers ExteriorWordMultilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_ordered_word_repeated_entry]: equal
    factors at distinct slots make the exterior word zero,
    1.3.1 and 1.4.1, pp. 13–17. Supporting the vertical
    differential calculation in Federer 3.2.28(2), p. 264. *)
Lemma exterior_ordered_word_repeated_entry (K:fieldType) (V:lmodType K)
    m (e:'I_m->V) (i j:'I_m):
  i!=j -> e i=e j -> e_lambda e (ord_tuple m)=0.
Proof.
move=>hij heq; apply:val_inj.
change (component_val (e_lambda e (ord_tuple m))=
  component_val (0:exterior_power V m)).
rewrite e_lambdaE linear0.
apply:exterior_word_nonuniq.
change (~~uniq [tuple e a|a<m]).
apply/negP=>hu.
have hi:injective (tnth [tuple e a|a<m]) by apply/tuple_uniqP.
have hEq:tnth [tuple e a|a<m] i=tnth [tuple e a|a<m] j.
  by rewrite !tnth_mktuple heq.
by move:hij; rewrite (hi _ _ hEq) eqxx.
Qed.

(** Source for [exterior_word_replacement_linear]: fixing all
    but one factor gives a linear map, 1.4.1, p. 17.
    Supporting actual DQ in Federer 3.2.28(2), p. 264. *)
Lemma exterior_word_replacement_linear (K:fieldType) (V:lmodType K)
    m (e:'I_m->V) (i:'I_m):
  linear (fun v=>e_lambda (family_with (i:=i) [ffun a=>e a] v) (ord_tuple m)).
Proof. exact:(@exterior_ordered_word_multilinear K V m [ffun a=>e a] i). Qed.

(** Source for [exterior_word_replacement_same]: replacing a
    factor by itself leaves the word unchanged, supporting
    Federer 3.2.28(2), p. 264, by the ordered-product
    convention of 1.3.2, pp. 14–15. *)
Lemma exterior_word_replacement_same (K:fieldType) (V:lmodType K)
    m (e:'I_m->V) (i:'I_m):
  e_lambda (family_with (i:=i) [ffun a=>e a] (e i)) (ord_tuple m)=
    e_lambda e (ord_tuple m).
Proof.
have he:(fun a=>family_with (i:=i) [ffun a=>e a] (e i) a)=e.
  apply:funext=>a; case:(eqVneq i a)=>[<-|hia].
  - exact:family_with_in.
  - by rewrite family_with_out // ffunE.
change (e_lambda (fun a=>family_with (i:=i) [ffun a=>e a] (e i) a) (ord_tuple m)=
  e_lambda e (ord_tuple m)).
by rewrite he.
Qed.

(** Source for [exterior_word_replacement_other]: substituting
    another existing factor gives zero, supporting the vertical
    kernel in Federer 3.2.28(2), p. 264, by alternating
    multilinearity, 1.4.1, pp. 16–17. *)
Lemma exterior_word_replacement_other (K:fieldType) (V:lmodType K)
    m (e:'I_m->V) (i j:'I_m):
  i!=j -> e_lambda (family_with (i:=i) [ffun a=>e a] (e j)) (ord_tuple m)=0.
Proof.
move=>hij.
apply:(@exterior_ordered_word_repeated_entry K V m
  (family_with (i:=i) [ffun a=>e a] (e j)) i j hij).
by rewrite family_with_in family_with_out // ffunE.
Qed.

(** Source for [exterior_word_replacement_combination]: replacing
    slot i by a linear combination of existing factors retains
    only coefficient i. Supporting the vertical calculation in
    Federer 3.2.28(2), p. 264, by 1.4.1, p. 17. *)
Lemma exterior_word_replacement_combination (K:fieldType) (V:lmodType K)
    m (e:'I_m->V) (i:'I_m) (c:'I_m->K):
  e_lambda (family_with (i:=i) [ffun a=>e a] (\sum_(j<m) c j*:e j)) (ord_tuple m)=
    c i*:e_lambda e (ord_tuple m).
Proof.
pose f:=fun v=>e_lambda (family_with (i:=i) [ffun a=>e a] v) (ord_tuple m).
have hf:linear f:=exterior_word_replacement_linear e i.
change (f (\sum_(j<m) c j*:e j)=c i*:e_lambda e (ord_tuple m)).
rewrite (big_morph f (linD hf) (lin0 hf)).
under eq_bigr do rewrite (linZ hf).
have hSame:f (e i)=e_lambda e (ord_tuple m):=exterior_word_replacement_same e i.
rewrite (bigD1 i) //= hSame.
have hz:(\sum_(j<m|j!=i) c j*:f (e j))=0.
  apply:big1=>j hji; rewrite /f exterior_word_replacement_other ?scaler0 //.
  by rewrite eq_sym.
by rewrite hz addr0.
Qed.
