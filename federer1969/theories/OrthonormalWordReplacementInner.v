(** Federer (1969), 3.2.28(2), printed p. 264:
    the horizontal differential preserves length. These supporting
    word calculations expand the inner-product permutation formula
    of 1.7.5, pp. 31–32, with one normal replacement. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import Bilinear InnerProductUP InnerProductLaws
  OrthonormalFamilies FamilyUpdate TensorFamilyUP ExteriorGrading
  FiniteExteriorPowers InnerExterior InnerExteriorProducts
  SimpleVectorFrames InversionCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Replacements.
Variable R:realFieldType.
Variable h2:(1+1:R)!=0.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Variable m:nat.
Variable e:'I_m->V.
Hypothesis he:orthonormal_family B e.

(** Source for [orthonormal_replacement_pairing_diagonal]:
    two words with a normal vector in the same slot have
    inner product equal to that of the normal vectors.
    Supporting the isometry in Federer 3.2.28(2), p. 264,
    by 1.7.5, pp. 31–32. *)
Lemma orthonormal_replacement_pairing_diagonal (i:'I_m) (v w:V):
  (forall j,B (e j) v=0) -> (forall j,B (e j) w=0) ->
  exterior_inner_form h2 hB
    (e_lambda (family_with (i:=i) [ffun j=>e j] v) (ord_tuple m))
    (e_lambda (family_with (i:=i) [ffun j=>e j] w) (ord_tuple m))=B v w.
Proof.
move=>hv hw.
pose u:=family_with (i:=i) [ffun j=>e j] v.
pose z:=family_with (i:=i) [ffun j=>e j] w.
have hOff (a b:'I_m):a!=b -> B (u b) (z a)=0.
  move=>hab; rewrite /u /z.
  case:(eqVneq i a)=>[hia|hia].
  - have hib:i!=b by rewrite hia.
    rewrite -hia family_with_in (@family_with_out m (fun _=>V) [ffun j=>e j] i v b hib) ffunE.
    exact:hw.
  - rewrite (@family_with_out m (fun _=>V) [ffun j=>e j] i w a hia) ffunE.
    case:(eqVneq i b)=>[<-|hib].
    + rewrite dfwith_in ffunE (inner_symmetric hB); exact:hv.
    + by rewrite dfwith_out // !ffunE he eq_sym (negbTE hab).
rewrite exterior_inner_product_permutations.
have hf (s:'S_m):
  foldr *%R 1 [seq B (u (s j)) (z j)|j<-enum 'I_m]=
    \prod_(j<m) B (u (s j)) (z j).
  by rewrite foldrE big_map enumT.
under eq_bigr do rewrite hf.
rewrite (diagonal_permutation_sum (a:=fun a b=>B (u b) (z a))) //.
rewrite (bigD1 i) //= /u /z !family_with_in.
have hRest:(\prod_(j<m|j!=i) B
    (family_with (i:=i) [ffun j=>e j] v j)
    (family_with (i:=i) [ffun j=>e j] w j))= 1.
  apply:big1=>j hji.
  by rewrite !family_with_out 1?eq_sym // !ffunE he eqxx.
by rewrite hRest mulr1.
Qed.

(** Source for [orthonormal_replacement_pairing_off_diagonal]:
    normal replacements in distinct slots are orthogonal.
    Supporting the horizontal length calculation in Federer
    3.2.28(2), p. 264, from the zero column in the
    permutation formula of 1.7.5, pp. 31–32. *)
Lemma orthonormal_replacement_pairing_off_diagonal (i j:'I_m) (v w:V):
  i!=j -> (forall a,B (e a) v=0) ->
  exterior_inner_form h2 hB
    (e_lambda (family_with (i:=i) [ffun a=>e a] v) (ord_tuple m))
    (e_lambda (family_with (i:=j) [ffun a=>e a] w) (ord_tuple m))=0.
Proof.
move=>hij hv.
pose u:=family_with (i:=i) [ffun a=>e a] v.
pose z:=family_with (i:=j) [ffun a=>e a] w.
rewrite exterior_inner_product_permutations; apply:big1=>s _.
have hf:foldr *%R 1 [seq B (u (s a)) (z a)|a<-enum 'I_m]=
    \prod_(a<m) B (u (s a)) (z a).
  by rewrite foldrE big_map enumT.
rewrite hf (bigD1 i) //=.
have hz:B (u (s i)) (z i)=0.
  have hji:j!=i by rewrite eq_sym.
  rewrite /z (@family_with_out m (fun _=>V) [ffun a=>e a] j w i hji) ffunE /u.
  case:(eqVneq i (s i))=>[hi|hi].
  - rewrite -hi dfwith_in !ffunE (inner_symmetric hB); exact:hv.
  - by rewrite dfwith_out // !ffunE he eq_sym (negbTE hi).
by rewrite hz mul0r mulr0.
Qed.
End Replacements.
