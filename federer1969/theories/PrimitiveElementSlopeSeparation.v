(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: finitely many slopes separate the
    original pair from distinct conjugate pairs.
    Reuse characteristic-zero natural-scalar injectivity
    and finite-list cardinality. Source: Bourbaki,
    Algebra II (1990), Chapter V, section 7,
    no. 4, Theorem 1, pp. V.40–41. *)
From mathcomp Require Import all_boot all_order all_algebra boolp ring.
From Federer Require Import PolynomialCoefficientUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [characteristic_zero_scalar_avoids_list]:
    an original characteristic-zero scalar avoids
    any finite excluded list, the infinite-base-field
    step of the cited primitive-element argument.
    Apply existing scalar injectivity and list bounds. *)
Lemma characteristic_zero_scalar_avoids_list (K E:fieldType) (phi:{rmorphism K->E}) (F:seq E):
  [pchar K] =i pred0 ->exists t:K,phi t \notin F.
Proof.
move=>hCharacteristic;apply:contrapT=>hNoChoice.
have hAll i:phi (i%:R) \in F.
  case hMem:(phi (i%:R) \in F);first by [].
  exfalso;apply:hNoChoice;exists (i%:R);by rewrite hMem.
have hInjective:injective (fun i:nat=>phi (i%:R)).
  move=>i j hEqual;apply:(characteristic_zero_nat_injective hCharacteristic).
  exact:(fmorph_inj phi hEqual).
pose G:=[seq phi (i%:R)|i<-iota 0 (size F).+1].
have hUnique:uniq G by rewrite /G (map_inj_uniq hInjective) iota_uniq.
have hSubset:{subset G<=F}.
  move=>y /mapP [i hi ->];exact:hAll i.
have hBound:=uniq_leq_size hUnique hSubset.
by rewrite /G size_map size_iota ltnn in hBound.
Qed.

(** Source for [primitive_pair_finite_slope_exclusions]:
    outside finitely many original slopes, equality
    of alpha+t beta with a conjugate pair
    forces both coordinates to agree, the classical
    reasoning invoked in 3.4.8(8), p. 330.
    The finite list is only an existence witness. *)
Theorem primitive_pair_finite_slope_exclusions (K E:fieldType) (phi:{rmorphism K->E})
  (a b:E) (A B:seq E):
  exists F:seq E,forall t:K,phi t \notin F ->forall u:E,u \in A ->
    forall v:E,v \in B ->a+phi t * b = u+phi t * v ->u = a /\v = b.
Proof.
pose F:=[seq (u-a)/(b-v)|u<-A,v<-B].
exists F=>t hGood u hU v hV hEquality.
have hSame:v = b.
  apply:contrapT=>hDifferent.
  have hDen:b-v!=0.
    apply/eqP=>hZero;apply:hDifferent;exact:esym (subr0_eq hZero).
  have hCross:phi t * (b-v) = u-a.
    have hRestore:phi t * (b-v) = (a+phi t * b)-a-phi t * v by ring.
    rewrite hRestore hEquality;ring.
  have hSlope:phi t = (u-a)/(b-v).
    apply:(mulIf hDen);by rewrite divfK.
  apply:(negP hGood);rewrite /F;apply/allpairsP;exists (u,v);by split.
rewrite hSame in hEquality.
have hFirst:=congr1 (fun z:E=>z-phi t * b) hEquality.
rewrite !addrK in hFirst;split;[exact:esym hFirst|exact:hSame].
Qed.
